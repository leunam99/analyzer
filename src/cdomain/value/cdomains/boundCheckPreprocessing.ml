open GoblintCil

module  M = Messages

let top_function = ref None 

let find_top_fun ast = 
  iterGlobals ast (function GFun (fd,_) when fd.svar.vname = "__top" -> top_function := Some fd.svar | _ -> ());
  (if !top_function = None then
     let varinfo = (makeGlobalVar "__top" (TFun (TInt (ILongLong,[]), Some [], false, [Attr ("goblint_stub", [])]))) in
     let loc = { line = -1;
                 file = "unknown";
                 byte = -1;
                 column = -1;
                 endLine = -1;
                 endByte = -1;
                 endColumn = -1;
                 synthetic = true;}
     in
     let fundec = { 
       svar  = varinfo;
       smaxid = 0;
       slocals = [];
       sformals = [];
       sbody = mkBlock [];
       smaxstmtid = None;
       sallstmts = [];
     } in 
     let local = makeLocalVar fundec "x" (TInt (ILongLong,[])) in
     fundec.sbody <- mkBlock [mkStmt (Return (Some (Lval( Var local, NoOffset)),loc, loc)) ];
     ast.globals <- GFun (fundec, loc) :: ast.globals;
     top_function := Some varinfo;

  )

let applicable_functions = ref BatSet.empty

class applicable_functions_visitor included excluded = object(self)
  inherit nopCilVisitor

  method! vvdec var = 
    (match var.vtype with 
     | TFun _ -> 
       if not (List.mem var.vname (GobConfig.get_string_list "mainfun")
               || List.mem var.vname (GobConfig.get_string_list "exitfun")
               || LibraryFunctions.is_special var
              ) then
         included := BatSet.add var !included;
     | _ -> ()
    );
    DoChildren

  method! vexpr = function
    | AddrOf (Var v,_) -> begin 
        match v.vtype with 
        | TFun _ ->
          (*If we allow for address to be taken, we would need to handle dynamic calls*)
          excluded := BatSet.add v !excluded; DoChildren
        | _ -> DoChildren (*for arrays we do not care as they can not change size*)
      end
    | _ -> DoChildren
end

let find_applicable_functions ast =
  let inc = ref BatSet.empty in
  let exc = ref BatSet.empty in
  visitCilFileSameGlobals (new applicable_functions_visitor inc exc) ast;
  applicable_functions := BatSet.diff !inc !exc

let is_applicable var = 
  not (hasAttribute "goblint_cil_nested" var.vattr) && (*might get deallocated in the middle of the function*)
  match unrollType var.vtype with
  | TPtr _
  | TArray _ -> true
  | _ -> false

let is_applicable var = 
  let res = is_applicable var in
  if M.tracing then M.trace "length_vars" "accepting var: %a %b" d_global (GVar (var, {init=None}, locUnknown)) res ;
  res

let length_var_name var = "__length_" ^ var.vname ^ "_" ^ Int.to_string var.vid 

let ikind = ILongLong
let size_type = TInt (ikind,[]) (*should be larger than size_t, and signed so that overflow is not a problem *)

let rec offs_to_expr offs = 
  match offs with 
  | NoOffset 
  | Field (_, NoOffset) -> Some (mkCast ~e:zero ~newt:size_type)
  | Field _ -> None (*TODO this might contain another array access, but with a different type, so we can not handle it easily*)
  | Index (exp,offs') -> 
    let rest = offs_to_expr offs' in
    BatOption.map (fun rest -> BinOp (PlusA,mkCast ~e:exp ~newt:size_type, rest, size_type)) rest

let rec ptr_to_var_and_offset ?additional_offset exp  = 
  match exp with 
  | StartOf (Var v, off) 
  | Lval (Var v, off) -> BatOption.map (fun off -> M.trace "oob" "basecase Some"; (v, off)) @@ offs_to_expr @@ BatOption.map_default (addOffset off) off additional_offset
  | CastE _ -> M.trace "oob" "expr %a cast" d_exp exp; None (*TODO?*)
  | BinOp (IndexPI, ptr_expr, offs_expr, _)
  | BinOp (PlusPI , ptr_expr, offs_expr, _) -> begin
      match ptr_to_var_and_offset ?additional_offset ptr_expr with 
      | None -> None
      | Some (v,o) -> Some (v, BinOp (PlusA, o, mkCast ~e:offs_expr ~newt:size_type, size_type))
    end
  | BinOp (MinusPI , ptr_expr, offs_expr, _) -> begin
      match ptr_to_var_and_offset ?additional_offset ptr_expr with 
      | None -> None
      | Some (v,o) -> Some (v, BinOp (MinusA, o, mkCast ~e:offs_expr ~newt:size_type, size_type))
    end
  | _ -> M.trace "oob" "expr %a not matched" d_exp exp; None  (*do not result in a pointer, (or only multidimensional)*)

let ptr_to_var_and_offset ?additional_offset exp = 
  let res = ptr_to_var_and_offset ?additional_offset exp in
  (if M.tracing then 
     match res with
     | None -> M.trace "oob" "expr %a not valid" d_exp exp
     | Some (v, e) -> M.trace "oob" "expr %a + offs ? converted to var %a and offset %a" d_exp exp d_lval (Var v, NoOffset) d_exp e);
  res

let mapping = BatHashtbl.create (100)

class definitionVisitor pointer_vars excluded = object(self)
  inherit nopCilVisitor

  method! vvdec var = 
    (*TODO: instead, we could also match on actual uses of indexing *)
    if is_applicable var then 
      pointer_vars := BatSet.add var !pointer_vars;
    DoChildren

  method! vexpr = function
    | AddrOf (Var v,_) -> begin 
        match v.vtype with 
        | TFun _ 
        | TArray _ ->
          (*If we allow for address to be taken, we would need to track if the pointer is changed through another pointer*)
          excluded := BatSet.add v !excluded; DoChildren
        | _ -> DoChildren 
      end
    | _ -> DoChildren
end

class instructionTransformer (vars) = object(self)
  inherit nopCilVisitor

  method! vinst = function
    | VarDecl (v,loc) -> 
      if BatSet.mem v vars then begin
        match v.vtype, BatHashtbl.find_option mapping v.vid with 
        | TArray (t,Some length_expr,l), Some length_var ->
          let lval = Var length_var, NoOffset in
          let expr = CastE (size_type, length_expr) in
          v.vtype <- TArray (t, Some (Lval lval), l);
          ChangeTo [ 
            Set (lval,expr,loc,loc);
            VarDecl (v,loc)
          ] 
        | _ -> SkipChildren
      end else SkipChildren
    | _ -> DoChildren

  method! vstmt stmt = 
    let set_length_to_expr array arg_exp typ loc = 
      let var = BatHashtbl.find mapping array.vid in
      let exp = match typ with 
        | None -> arg_exp
        | Some t -> BinOp (Div,mkCast ~e:arg_exp ~newt:size_type,mkCast ~e:(SizeOf t) ~newt:size_type,size_type)
      in Set ((Var var, NoOffset), exp, loc, loc)
    in
    let set_var_top var loc = Call (Some (Var var, NoOffset), (Lval(Var (BatOption.get !top_function), NoOffset)), [], loc, loc) in
    match stmt.skind with
    | Instr instr -> 
      let rec transform_instructions ins = begin 
        match ins with
        | (Call (Some (Var tmp, NoOffset), Lval(Var f, NoOffset),[arg_exp],_,_) as call)  (* tmp = malloc (size)*)
          :: (Set ((Var array, NoOffset), CastE (TPtr (typ,_),Lval(Var tmp2, NoOffset)), loc_set,_) as set)(* array = (type* ) tmp*)
          :: xs
          when tmp.vid = tmp2.vid 
            && (f.vname = "malloc" || f.vname = "alloca" || List.mem f.vname (GobConfig.get_string_list "ana.malloc.wrappers") ) (*TODO more robust identification needed?*)
            && BatSet.mem array vars ->
          call
          :: set
          :: set_length_to_expr array arg_exp (Some typ) loc_set (* length_array = size / sizeof type*)
          :: transform_instructions xs
        | (Call (Some (Var tmp, NoOffset), Lval(Var f, NoOffset),[_;arg_exp],_,_) as call)  (* tmp = realloc (old_ptr, size)*)
          :: (Set ((Var array, NoOffset), CastE (TPtr (typ,_),Lval(Var tmp2, NoOffset)), loc_set,_) as set)(* array = (type* ) tmp*)
          :: xs
          when tmp.vid = tmp2.vid 
            && f.vname = "realloc" (*TODO more robust identification needed?*)
            && BatSet.mem array vars ->
          call
          :: set
          :: set_length_to_expr array arg_exp (Some typ) loc_set (* length_array = size / sizeof type*)
          :: transform_instructions xs
        | (Call (Some (Var tmp, NoOffset), Lval(Var f, NoOffset),[arg_exp;single],_,_) as call)  (* tmp = calloc (nbr, single_size)*)
          :: (Set ((Var array, NoOffset), CastE (TPtr (typ,_),Lval(Var tmp2, NoOffset)), loc_set,_) as set)(* array = (type* ) tmp*)
          :: xs
          when tmp.vid = tmp2.vid 
            && f.vname = "calloc" (*TODO more robust identification needed?*)
            && BatSet.mem array vars 
            && constFold true single = constFold true (SizeOf typ) -> (*TODO multiple could be made to work*)
          call
          :: set
          :: set_length_to_expr array arg_exp None loc_set (* length_array = nbr*)
          :: transform_instructions xs
        | (Set ((Var lhs_ptr, NoOffset), expr, loc_set,_) as set) (*pointer to pointer assignment Needs to be here instead of vinstr, so that we do not catch the sets from above*)
          :: xs 
          when BatSet.mem lhs_ptr vars -> (*TODO could be more general: allow same size / rhs size multiple of lhs size*) 
          let length_var_lhs = BatHashtbl.find mapping lhs_ptr.vid in
          let new_length_instr = match ptr_to_var_and_offset expr with 
            | Some (v,o) -> begin
                match BatHashtbl.find_option mapping v.vid, constFold true o with 
                | Some length_var_rhs, Const (CInt (c,_,_)) -> 
                  let length_expr = BinOp (MinusA, Lval (Var length_var_rhs, NoOffset), o, size_type) in
                  Set ((Var length_var_lhs, NoOffset), length_expr, loc_set, loc_set)
                | _ -> set_var_top length_var_lhs loc_set
              end
            | None -> set_var_top length_var_lhs loc_set
          in
          set 
          :: new_length_instr
          :: xs
        | (Set ((Var pointer, _), _, loc_set,_) as set) (*pointer = unknown   Needs to be here instead of vinstr, so that we do not catch the sets from above*)
          :: xs
          when isPointerType pointer.vtype
            && BatSet.mem pointer vars ->
          let var = BatHashtbl.find mapping pointer.vid in
          set
          :: set_var_top var loc_set
          :: transform_instructions xs
        | x::xs -> x :: transform_instructions xs
        | [] -> []
      end in
      stmt.skind <- Instr (transform_instructions instr);
      DoChildren
    | _ -> DoChildren

end

let function_argument_changes = BatHashtbl.create 100

class arrayVisitor (fd : fundec) = object(self)
  inherit nopCilVisitor

  method! vfunc fd = 
    (*if we change the function definition (e.g. adding local variables) inside this visitor, they are overwritten again -> call other visitor and do not execute this ine*)
    (*TODO probably it would be better to change the interface of preprocess to directly call this with fd*)
    let pointers = ref BatSet.empty in
    let excluded = ref BatSet.empty in 
    let def_visitor = new definitionVisitor pointers excluded in
    ignore @@ visitCilFunction def_visitor fd;
    pointers := BatSet.diff !pointers !excluded;
    BatSet.iter ( fun var ->
        let length_var = 
          if List.mem var fd.sformals && BatSet.mem fd.svar !applicable_functions then 
            let (set,orig_formals) = BatHashtbl.find_default function_argument_changes fd.svar.vid (BatSet.empty, fd.sformals) in
            let formal = Cil.makeFormalVar fd ~where:var.vname (length_var_name var) size_type in
            let index = fst @@ BatList.findi (fun _ v -> v.vid = var.vid) orig_formals in
            if M.tracing then M.trace "call_tfm" "adding length var at argument %d in function %s" index fd.svar.vname;  
            (*save the positions of the arguments for which we add length variables*)
            BatHashtbl.replace function_argument_changes fd.svar.vid (BatSet.add index set, orig_formals);
            formal
          else
            Cil.makeLocalVar fd (length_var_name var) size_type 
        in
        BatHashtbl.add mapping var.vid length_var;
        (*the only purpose of this variable is to be tracked by the relational domains, so make sure they do*)
        length_var.vattr <- [Attr ("goblint_relation_track", [])]; 
        if not var.vhasdeclinstruction then (
          match var.vtype with
          | TArray (t,Some l,a) -> 
            let new_instruction = Set ((Var length_var, NoOffset), mkCast ~e:l ~newt:size_type, var.vdecl, var.vdecl ) in
            self#queueInstr [new_instruction]
          | _ -> ()
        );
      ) !pointers;
    ignore @@ visitCilFunction (new instructionTransformer !pointers) fd;

    SkipChildren

end

let unknown_length fd loc = 
  let var = makeTempVar fd size_type in
  Lval (Var var, NoOffset), Call (Some (Var var, NoOffset), Lval (Var (BatOption.get !top_function), NoOffset), [], loc, loc) 

class call_transfromation_visitor (fd : fundec) = object(self)
  inherit nopCilVisitor

  method! vinst = function
    | Call (lval,Lval (Var f, NoOffset), args, loc, loc2) as call -> begin
        let rec find_var expr = 
          let points_to typ =
            match unrollType typ with 
            | TPtr (t,_)
            | TArray (t,_,_) -> t 
            | _ -> raise (Invalid_argument "Not a pointer")
          in
          match expr with 
          | StartOf (Var v, NoOffset)
          | Lval (Var v, NoOffset) -> Some v, expr
          (*handle casts to same size, importantly, for example, adding a const attribute*)
          | CastE (t,e) -> 
            (try 
               if bitsSizeOf (points_to (typeOf e)) = bitsSizeOf (points_to t) 
               then fst (find_var e), expr
               else None, expr
             with _ -> None, expr )
          | _ -> None, expr
        in
        let args = List.map find_var args in 
        match BatHashtbl.find_option function_argument_changes f.vid with
        | Some (set,_) -> 
          let rec adjust_arguments index args =
            if BatSet.mem index set then 
              match args with 
              | [] -> ([],[])
              | (Some v, x)::xs -> begin
                  let xs', instr = adjust_arguments (index + 1) xs in
                  match BatHashtbl.find_option mapping v.vid with 
                  | None -> 
                    if M.tracing then M.trace "call_tfm" "unknown length at %d" index; 
                    let l, i = unknown_length fd loc in
                    x::l::xs', i::instr
                  | Some l -> 
                    if M.tracing then M.trace "call_tfm" "known length var at %d: %s" index l.vname; 
                    x::(Lval (Var l, NoOffset))::xs', instr
                end 
              | (_,x)::xs -> 
                let xs', instr = adjust_arguments (index + 1) xs in
                if M.tracing then M.trace "call_tfm" "unknown length at %d" index; 
                let l, i = unknown_length fd loc in
                x::l::xs', i::instr
            else (
              if M.tracing then M.trace "call_tfm" "call: %a index %d does no have length" d_instr call index; 
              match args with 
              | [] -> ([],[])
              | x::xs -> 
                let xs', instr = adjust_arguments (index + 1) xs in
                (snd x)::xs', instr
            )
          in
          let args', instr = adjust_arguments 0 args in
          let call' = Call (lval,Lval (Var f, NoOffset), args', loc, loc2) in  
          ChangeTo (instr @ [call'])
        | _ -> SkipChildren
      end
    | _ -> SkipChildren

end

let () =
  Cilfacade.register_pre_preprocess ("boundTransformation") find_top_fun;
  Cilfacade.register_pre_preprocess ("boundTransformation") find_applicable_functions;
  Cilfacade.register_preprocess ("boundTransformation") (new arrayVisitor);
  Cilfacade.register_post_process ("boundTransformation") (new call_transfromation_visitor);