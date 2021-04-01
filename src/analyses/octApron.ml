(** Analysis using Apron for integer variables. *)

open Prelude.Ana
open Analyses
open Apron
open OctApronDomain
open Utilities

module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name () = "octApron"

  module D = OctApronDomain.D
  module G = Lattice.Unit
  module C = D

  let val_of x = x
  let context x = if GobConfig.get_bool "exp.full-context" then x else D.bot ()

  let threadenter ctx lval f args = D.top ()
  let threadspawn ctx lval f args fctx = D.bot ()
  let exitstate  _ = D.top ()
  let startstate _ = D.top ()

  let enter ctx r f args =
    if D.is_bot ctx.local then [ctx.local, D.bot ()] else
      let f = Cilfacade.getdec f in
      let is, fs = D.typesort f.sformals in
      let is = is @ List.map (fun x -> x^"'") is in
      let fs = fs @ List.map (fun x -> x^"'") fs in
      let newd = D.add_vars ctx.local (is,fs) in
      let formargs = Utilities.zip f.sformals args in
      let arith_formals = List.filter (fun (x,_) -> isArithmeticType x.vtype) formargs in
      List.iter (fun (v, e) -> D.assign_var_with newd (v.vname^"'") e) arith_formals;
      D.forget_all_with newd (List.map (fun (x,_) -> x.vname) arith_formals);
      List.iter  (fun (v,_)   -> D.assign_var_eq_with newd v.vname (v.vname^"'")) arith_formals;
      D.remove_all_but_with newd (is@fs);
      [ctx.local, newd]


  let combine ctx r fe f args fc d =
    if D.is_bot ctx.local || D.is_bot d then D.bot () else
      let f = Cilfacade.getdec f in
      match r with
      | Some (Var v, NoOffset) when isArithmeticType v.vtype && (not v.vglob) ->
        let nd = D.forget_all ctx.local [v.vname] in
        let fis,ffs = D.get_vars ctx.local in
        let fis = List.map Var.to_string fis in
        let ffs = List.map Var.to_string ffs in
        let nd' = D.add_vars d (fis,ffs) in
        let formargs = Utilities.zip f.sformals args in
        let arith_formals = List.filter (fun (x,_) -> isArithmeticType x.vtype) formargs in
        List.iter (fun (v, e) -> D.substitute_var_with nd' (v.vname^"'") e) arith_formals;
        let vars = List.map (fun (x,_) -> x.vname^"'") arith_formals in
        D.remove_all_with nd' vars;
        D.forget_all_with nd' [v.vname];
        D.substitute_var_eq_with nd' "#ret" v.vname;
        D.remove_all_with nd' ["#ret"];
        A.unify Man.mgr nd nd'
      | _ -> D.topE (A.env ctx.local)
  let rec print_list_exp myList = match myList with
    | [] -> print_endline "End!"
    | head::body -> 
    begin
      D.print_expression head;
      print_list_exp body
    end

  let rec get_vnames_list exp = match exp with
    | Lval lval -> 
      let lhost, offset = lval in 
      (match lhost with
        | Var vinfo -> [vinfo.vname]
        | _ -> [])
    | UnOp (unop, e, typ) -> get_vnames_list e
    | BinOp (binop, e1, e2, typ) -> (get_vnames_list e1) @ (get_vnames_list e2)
    | _ -> []

  let invalidate oct (exps: exp list) =
    if Messages.tracing && exps <> [] then Messages.tracel "invalidate" "Will invalidate expressions [%a]\n" (d_list ", " d_plainexp) exps;
    let () = print_list_exp exps in 
    let l = List.flatten (List.map get_vnames_list exps) in
    D.forget_all_with oct l

  let special ctx r f args =
    if D.is_bot ctx.local then D.bot () else
      begin
        match LibraryFunctions.classify f.vname args with
        | `Assert expression -> ctx.local
        | `Unknown "printf" -> ctx.local
        | `Unknown "__goblint_check" -> ctx.local
        | `Unknown "__goblint_commit" -> ctx.local
        | `Unknown "__goblint_assert" -> ctx.local
        | `Malloc size -> 
          (match r with
            | Some lv ->
              D.remove_all ctx.local [f.vname]
            | _ -> ctx.local)
        | `Calloc (n, size) -> 
          (match r with
            | Some lv ->
              D.remove_all ctx.local [f.vname]
            | _ -> ctx.local)
        | `ThreadJoin (id,ret_var) -> D.topE (A.env ctx.local)
        | `ThreadCreate _ -> D.topE (A.env ctx.local)
        | `Lock (_, _, _) -> D.topE (A.env ctx.local)
        | `Unlock ->  D.topE (A.env ctx.local)
        | _ ->
          begin
            let st =
              match LibraryFunctions.get_invalidate_action f.vname with
              | Some fnc -> let () = invalidate ctx.local (fnc `Write  args) in ctx.local
              | None -> D.topE (A.env ctx.local)
            in
              st      
          end
      end

  let branch ctx e b =
    if D.is_bot ctx.local then 
      D.bot () 
    else
      let res = D.assert_inv ctx.local e (not b) in 
      if D.is_bot res then raise Deadcode;
      res

  let return ctx e f =
    if D.is_bot ctx.local then D.bot () else
      
      let nd = match e with
        | Some e when isArithmeticType (typeOf e) -> 
          let nd = D.add_vars ctx.local (["#ret"],[]) in 
          let () = D.assign_var_with nd "#ret" e in
          nd
        | None -> D.topE (A.env ctx.local)
        | _ -> D.add_vars ctx.local (["#ret"],[])
      in
      let vars = List.filter (fun x -> isArithmeticType x.vtype) (f.slocals @ f.sformals) in
      let vars = List.map (fun x -> x.vname) vars in
      D.remove_all_with nd vars;
      nd

  let body ctx f =
    if D.is_bot ctx.local then D.bot () else
      let vars = D.typesort f.slocals in
      D.add_vars ctx.local vars

  let check_boundaries oct v e ikind (n:int) signed = 
    let lower_limit, upper_limit = D.get_boundaries n signed in 
    let oct_with_max = D.assert_inv oct (BinOp (Ge, e, (Const (CInt64 (upper_limit, ikind, None))), intType)) true in
    let oct_with_min = D.assert_inv oct (BinOp (Le, e, (Const (CInt64 (lower_limit, ikind, None))), intType)) true in
    let outside = D.is_bot oct_with_max && D.is_bot oct_with_min in 
    let new_oct = if outside && signed then 
      (* Signed overflows are undefined behavior, so octagon goes to top. *)
      D.topE (A.env oct)
    else if outside && not signed then
      (* Unsigned overflows are defined, but for now the variable in question goes to top. *)
      let () = D.forget_all_with oct [v.vname] in
      oct
    else
      D.assign_var oct v.vname e
    in
    (outside, new_oct)
    
  
  let handle_underflow_and_overflow oct v e =
    let out_of_bounds, new_oct = match v.vtype with
      | TInt (ikind, _)-> (
        match ikind with
        (* Signed *)
        | IInt -> check_boundaries oct v e ikind 32 true
        | IShort -> check_boundaries oct v e ikind 16 true
        | ILong -> check_boundaries oct v e ikind 64 true
        | ILongLong -> check_boundaries oct v e ikind 64 true
        (* Unsigned *)
        | IUInt -> check_boundaries oct v e ikind 32 false
        | IUShort -> check_boundaries oct v e ikind 16 false
        | IULong -> check_boundaries oct v e ikind 64 false
        | IULongLong -> check_boundaries oct v e ikind 64 false
        | _ -> (false, oct) 
      )
      | _ -> (false, oct) 
    in
    (* let () = if out_of_bounds then
      print_endline (v.vname^" is under/overflowing")
    else 
      print_endline (v.vname^" is not under/overflowing "^(Pretty.sprint 20 (Cil.d_type () v.vtype)))
    in *)
    new_oct

  let assign ctx (lv:lval) e =
    if D.is_bot ctx.local then D.bot () else
      match lv with
      | Var v, NoOffset when isArithmeticType v.vtype && (not v.vglob) -> 
        handle_underflow_and_overflow ctx.local v e
      | _ -> D.topE (A.env ctx.local)

  let query ctx (q:Queries.t) : Queries.Result.t =
    let open Queries in
    let d = ctx.local in
    match q with
    | Assert e ->
      let x = match D.check_assert e ctx.local with
        | `Top -> `Top
        | `True -> `Lifted true 
        | `False -> `Lifted false 
        | _ -> `Bot
      in
      `AssertionResult x
    | EvalInt e ->
      begin
        match D.get_int_val_for_cil_exp d e with
        | Some i -> `Int i
        | _ -> `Top
      end
    | _ -> Result.top ()
end

let _ =
  MCP.register_analysis (module Spec : Spec)