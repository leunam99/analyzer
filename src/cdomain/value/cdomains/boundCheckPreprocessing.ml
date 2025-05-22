open GoblintCil

module  M = Messages

let has_right_type var = 
  match var.vtype with
  | TPtr _
  | TArray _ -> true
  | _ -> false

let has_right_type var = 
  let res = has_right_type var in
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
    if has_right_type var then 
      pointer_vars := BatSet.add var !pointer_vars;
    DoChildren

  (*If we allow for pointer to be taken, we would need to track if the pointer is changed through another pointer*)
  method! vexpr = function
    | AddrOf (Var v,_) -> excluded := BatSet.add v !excluded; DoChildren
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
    let set_var_top var loc = Call (Some (Var var, NoOffset), (Lval(Var (BatOption.get !Cilfacade.top_function), NoOffset)), [], loc, loc) in
    match stmt.skind with
    | Instr instr -> 
      let rec transform_instructions ins = begin 
        match ins with
        | (Call (Some (Var tmp, NoOffset), Lval(Var f, NoOffset),[arg_exp],_,_) as call)  (* tmp = malloc (size)*)
          :: (Set ((Var array, NoOffset), CastE (TPtr (typ,_),Lval(Var tmp2, NoOffset)), loc_set,_) as set)(* array = (type* ) tmp*)
          :: xs
          when tmp.vid = tmp2.vid 
            && (f.vname = "malloc" || f.vname = "alloca") (*TODO more robust identification needed?*)
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
        let length_var = Cil.makeLocalVar fd (length_var_name var) size_type in
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


let () =
  Cilfacade.register_preprocess ("lin2vareq_p") (new arrayVisitor);