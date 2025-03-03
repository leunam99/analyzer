(**TODO short description*)

open Batteries
open GoblintCil
open Pretty
open GobApron
open VectorMatrix
open PentagonSubDomains

module EqualitiesConjunctionWithIntervals (Ineq : TwoVarInequalities) =
struct
  type t = EConj.t *  (Value.t IntMap.t ) * Ineq.t [@@deriving eq, ord]

  let hash (econj, v, ineq) = 5 * EConj.hash econj + 13* IntMap.fold (fun k value acc -> 13 * 13 * acc + 31 * k + Value.hash value) v 0 + 7 * Ineq.hash ineq

  let show_values formatter is =     
    if IntMap.is_empty is then "{}"
    else
      let str = IntMap.fold (fun k v acc -> Printf.sprintf "%s=%s , %s" (formatter k) (Value.show v) acc) is "" in
      "{" ^ String.sub str 0 (String.length str - 3) ^ "}" 

  let show_formatted formatter ((dim, econj), is, ineq) = Printf.sprintf "(%s, %s, %s)" (EConj.show_formatted formatter econj) (show_values formatter is) (Ineq.show_formatted formatter ineq)

  let show = show_formatted (Printf.sprintf "var_%d") 

  let copy = identity

  let empty () = (EConj.empty (), IntMap.empty, Ineq.empty)
  let is_empty (e,is, ineq) = EConj.is_empty e && IntMap.is_empty is && Ineq.is_empty ineq
  let make_empty_with_size size = (EConj.make_empty_conj size, IntMap.empty, Ineq.empty)

  let is_top_con (e, is, ineq) = EConj.is_top_con e && IntMap.is_empty is && Ineq.is_empty ineq

  let modify_variables_in_domain_values map indexes op =
    let map_value _ = identity in EConj.modify_variables_in_domain_general map map_value indexes op

  let modify_variables_in_domain_values map indexes op =
    let res = modify_variables_in_domain_values map indexes op in if M.tracing then
      M.tracel "modify_dims" "dimarray bumping with (fun x -> x + %d) at positions [%s] in { %s } -> { %s }"
        (op 0 1)
        (Array.fold_right (fun i str -> (string_of_int i) ^ ", " ^ str) indexes "")
        (show_values (Printf.sprintf "var_%d") map)
        (show_values (Printf.sprintf "var_%d") res);
    res

  (*TODO we now potentially create the memo_bumpvar function three times (using it twice)-> inefficient?*)
  let dim_add (ch: Apron.Dim.change) (econj, i, ineq) =
    (EConj.dim_add ch econj, modify_variables_in_domain_values i ch.dim (+), Ineq.modify_variables_in_domain ineq ch.dim (+))


  let forget_variable (econj, is, ineq) var = (EConj.forget_variable econj var, IntMap.remove var is, Ineq.forget_variable ineq var)

  let dim_remove (ch: Apron.Dim.change) (econj, v, ineq) ~del =
    if Array.length ch.dim = 0 || is_empty (econj, v, ineq) then
      (econj, v, ineq)
    else (
      let cpy = Array.copy ch.dim in
      Array.modifyi (+) cpy; (* this is a hack to restore the original https://antoinemine.github.io/Apron/doc/api/ocaml/Dim.html remove_dimensions semantics for dim_remove *)
      let (econj', v', ineq') = Array.fold_lefti (fun y i x -> forget_variable y (x)) (econj, v, ineq) cpy in  (* clear m' from relations concerning ch.dim *)
      let econj'' = EConj.modify_variables_in_domain econj' cpy (-) in
      let v'' = modify_variables_in_domain_values v' cpy (-) in
      let ineq'' = Ineq.modify_variables_in_domain ineq' cpy (-) in
      (econj'', v'', ineq''))


  let get_rhs (econ, _, _) = EConj.get_rhs econ

  let get_value ((econ, vs, _) as t) lhs = 
    match IntMap.find_opt lhs vs with
      Some i -> i
    | None -> (*If there is no value saved, we have calculate it*)
      let (v,o,d) = get_rhs t lhs in
      if (v,o,d) = Rhs.var_zero lhs then Value.top  (*no relation -> Top*) 
      else match v with 
          None -> Value.div (Value.of_bigint o) (Value.of_bigint d)(*constant*) (*TODO is divisor always 1?*) 
        | Some (coeff,v) -> match IntMap.find_opt v vs with
            None -> Value.top (*uninitialised*) 
          | Some i -> Value.div (Value.add (Value.of_bigint o) @@ Value.mul (Value.of_bigint coeff) i) (Value.of_bigint d)


  (*Does not check the values directly, only the inequality domain, so we can use this to detect contradictions *)
  let is_less_than ((_,vs,ineq) as t) x y = 
    let get_information lhs =
      let rhs = get_rhs t lhs in
      match rhs with 
      | (Some (_,var), _ ,_) -> (rhs, get_value t var)
      (*We need to know which root a constant is referring to, so we use this the trivial equation to carry that information*)
      | (_,o,_) -> (Rhs.var_zero lhs, Value.of_bigint o) 
    in
    Ineq.is_less_than (get_information x) (get_information y) ineq


  let get_value t lhs = 
    let res = get_value t lhs in
    if M.tracing then M.tracel "get_value" "reading var_%d from %s -> %s" lhs (show t) (Value.show res);
    res

  let constrain_with_congruence_from_rhs econ lhs i =(**TODO do not recalculate this every time?*)
    (*calculate the congruence constraint for x from a single equation (cx + o) / d  *)
    let congruence_of_rhs (c, o, d) =
      (*adapted euclids extended algorithm for calculating the modular multiplicative inverse*)
      let rec inverse t r t_old r_old = 
        if Z.equal r Z.zero 
        then t_old
        else 
          let q = Z.div r_old r in
          inverse (Z.sub t_old (Z.mul q t)) (Z.sub r_old (Z.mul q r)) t r
      in let inverse a n = 
           let a = Z.rem a n in
           let a = if Z.lt a Z.zero then Z.add a n else a
           in inverse Z.one a Z.zero n
           (*  x = -o c^-1 (mod d)   *)
      in Value.of_congruence @@ (Z.mul (Z.neg o) (inverse c d), d)
    in
    let meet_with_rhs _ rhs i = match rhs with
      | (Some (c, v), o, d) when v = lhs ->  begin
          let cong = (congruence_of_rhs (c, o, d)) in
          let res = Value.meet i cong in
          if M.tracing then M.tracel "refine_pentagon" "refining %s with rhs %s (constraint: %s) -> %s" (Value.show i) (Rhs.show rhs) (Value.show cong) (Value.show res);
          res
        end
      | _ -> i
    in
    IntMap.fold meet_with_rhs (snd econ) i 

  let set_value ((econ, is, ineq) as t:t) lhs i =
    if M.tracing then M.tracel "modify_pentagon" "set_value var_%d=%s, before: %s" lhs (Value.show i) (show t);
    let set_value_for_root lhs i =
      if M.tracing then M.tracel "modify_pentagon" "set_value_for_root var_%d=%s, before: %s" lhs (Value.show i) (show t);
      let i = constrain_with_congruence_from_rhs econ lhs i in
      if M.tracing then M.tracel "modify_pentagon" "set_value_for_root refined to %s" (Value.show i);
      if i = Value.top then (econ, IntMap.remove lhs is, ineq) (*stay sparse*)
      else if Value.is_bot i then raise EConj.Contradiction
      else match Value.to_int i with
        | Some (Int x) ->  (*If we have a constant, update all equations refering to this root*)
          let update_references = function
            | (Some (coeff, v), o, d) when v = lhs -> (None, Z.div (Z.add o @@ Z.mul x coeff) d, Z.one)
            | t -> t
          in
          ((fst econ, IntMap.add lhs (None, x, Z.one) @@ IntMap.map update_references (snd econ)), IntMap.remove lhs is, ineq)
        | _ -> (econ, IntMap.add lhs i is, ineq) (*Not a constant*)
    in 
    let (v,o,d) = get_rhs t lhs in
    if (v,o,d) = Rhs.var_zero lhs then
      set_value_for_root lhs i
    else
      match v with
      | None -> (econ, is, ineq) (*For a constant, we do not need to save an value*) (*TODO should we check for equality?*)
      | Some (coeff, v) ->
        let i1 = Value.mul (Value.of_bigint d) i in
        let i2 = Value.sub i1 (Value.of_bigint o) in
        let i3 = Value.div i2 (Value.of_bigint coeff) in
        let i_transformed = i3 in 
        if M.tracing then M.tracel "modify_pentagon" "transforming with %s i: %s i1: %s i2: %s i3: %s" (Rhs.show ((Some (coeff, v)),o,d)) (Value.show i) (Value.show i1) (Value.show i2) (Value.show i3);
        set_value_for_root v i_transformed

  let set_value t lhs i =
    let res = set_value t lhs i in
    if M.tracing then M.tracel "modify_pentagon" "set_value before: %s eq: var_%d=%s  ->  %s " (show t) lhs (Value.show i) (show res);
    res

  (*TODO: If we are uptdating a variable, we will overwrite the value again -> maybe skip setting it here, because of performance?*)
  let set_rhs (econ, is, ineq) lhs rhs  =
    let econ' = EConj.set_rhs econ lhs rhs in
    match rhs with 
    | (None, _, _) -> econ', IntMap.remove lhs is, ineq (*when setting as a constant, we do not need a separate value *)
    | _ -> 
      let new_constraint = get_value (econ', is, ineq) lhs in
      let old_constraint = get_value (econ, is, ineq) lhs in
      let new_value = Value.meet new_constraint old_constraint in
      if Value.is_bot new_value then raise EConj.Contradiction
      else set_value (econ', is, ineq) lhs new_value

  let set_rhs t lhs rhs = 
    let res = set_rhs t lhs rhs  in
    if M.tracing then M.tracel "modify_pentagon" "set_rhs before: %s eq: var_%d=%s  ->  %s " (show t) lhs (Rhs.show rhs) (show res);
    res

  let meet_with_one_conj ((ts, is, ineq) as t:t) i (var, offs, divi) =
    let (var,offs,divi) = Rhs.canonicalize (var,offs,divi) in (* make sure that the one new conj is properly canonicalized *)
    let res : t =
      let subst_var ((dim,econj), is, ineq) x (vary, o, d) =
        let (vary, o, d) = Rhs.canonicalize (vary, o, d) in
        (* [[x substby (cy+o)/d ]] ((c'x+o')/d')             *)
        (* =====>   (c'cy + c'o+o'd)/(dd')                   *)
        let adjust = function
          | (Some (c',varx), o',d') when varx = x ->
            let open Z in Rhs.canonicalize (BatOption.map (fun (c, y)-> (c * c', y)) vary, c'*o + o'*d, d'*d)
          | e -> e
        in
        let value = get_value (ts, is, ineq) x in
        if vary = None then begin
          if d <> Z.one then 
            (if M.tracing then M.tracel "meet_with_one_conj" "meet_with_one_conj substituting var_%d with constant %s, which is not an integer" i (Rhs.show (var,offs,divi));
             raise EConj.Contradiction);
          if not @@ Value.contains value (Z.div offs divi) then 
            (if M.tracing then M.tracel "meet_with_one_conj" "meet_with_one_conj substituting var_%d with constant %s, Contradicts %s" (i) (Rhs.show (var,offs,divi)) (Value.show value);
             raise EConj.Contradiction)
        end;        
        let is' = IntMap.remove x is in (*if x was the representative, it might not be anymore -> remove value and add it back afterwards*)
        let t' = (dim, IntMap.add x (vary, o, d) @@ IntMap.map adjust econj), is', ineq in (* in case of sparse representation, make sure that the equality is now included in the conjunction *)
        set_value t' x value 
      in
      (match var, (EConj.get_rhs ts i) with
       (*| new conj      , old conj          *)
       | None          , (None            , o1, divi1) -> if not @@ (Z.equal offs o1 && Z.equal divi divi1) then raise EConj.Contradiction else t
       (*  o/d         =  x_i  = (c1*x_h1+o1)/d1            *)
       (*  ======> x_h1 = (o*d1-o1*d)/(d*c1) /\  x_i = o/d  *)
       | None          , (Some (coeff1,h1), o1, divi1) -> 
         subst_var t h1 (None, Z.(offs*divi1 - o1*divi),Z.(divi*coeff1))
       (* (c*x_j+o)/d  =  x_i  =  o1/d1                     *)
       (*  ======> x_j = (o1*d-o*d1)/(d1*c) /\  x_i = o1/d1 *)
       | Some (coeff,j), (None            , o1, divi1) -> subst_var t j  (None, Z.(o1*divi - offs*divi1),Z.(divi1*coeff))
       (* (c*x_j+o)/d  =  x_i  = (c1*x_h1+o1)/d1            *)
       (*  ======>   x_j needs normalization wrt. ts        *)
       | Some (coeff,j), ((Some (coeff1,h1), o1, divi1) as oldi)->
         (match EConj.get_rhs ts j with
          (* ts[x_j]=o2/d2             ========>  ... *)
          | (None            , o2, divi2) ->
            let newxi  = Rhs.subst (None,o2,divi2) j (Some (coeff,j),offs,divi) in
            let newxh1 = snd @@ EConj.inverse i (coeff1,h1,o1,divi1) in
            let newxh1 = Rhs.subst newxi i newxh1 in
            subst_var t h1 newxh1
          (* ts[x_j]=(c2*x_h2+o2)/d2   ========>   ...  *)
          | (Some (coeff2,h2), o2, divi2) as normalizedj ->
            if h1 = h2 then (* this is the case where x_i and x_j already where in the same equivalence class; let's see whether the new equality contradicts the old one *)
              let normalizedi= Rhs.subst normalizedj j (Some(coeff,j),offs,divi) in
              if not @@ Rhs.equal normalizedi oldi then raise EConj.Contradiction else t
            else if h1 < h2 (* good, we now unite the two equvalence classes; let's decide upon the representative *)
            then (* express h2 in terms of h1: *)
              let (_,newh2)= EConj.inverse j (coeff2,h2,o2,divi2) in
              let newh2 = Rhs.subst oldi i (Rhs.subst (snd @@ EConj.inverse i (coeff,j,offs,divi)) j newh2) in
              subst_var t h2 newh2
            else (* express h1 in terms of h2: *)
              let (_,newh1)= EConj.inverse i (coeff1,h1,o1,divi1) in
              let newh1 = Rhs.subst normalizedj j (Rhs.subst (Some(coeff,j),offs,divi) i newh1) in
              subst_var t h1 newh1)) in
    if M.tracing then M.tracel "meet_with_one_conj" "meet_with_one_conj conj: %s eq: var_%d=%s  ->  %s " (show t) i (Rhs.show (var,offs,divi)) (show res)
  ; res

  let meet_with_one_value var value t meet_function =
    let refined_value = Value.refine value in
    let new_value = meet_function refined_value (get_value t var)
    in if Value.is_bot new_value then raise EConj.Contradiction else 
      let res =  set_value t var new_value
      in if M.tracing then M.tracel "meet_value" "meet var_%d: before: %s meeting: %s -> %s, total: %s-> %s" (var) (Value.show @@ get_value t var) (Value.show value) (Value.show new_value) (show t) (show res);
      res

  let join_with_one_value var value ((ts, _, _) as t:t) = 
    let (_,cong) = constrain_with_congruence_from_rhs ts var (Value.top) in (*TODO probably should be a flag in set_value to do a join instead of meet so we do not do this twice*)
    let value' = Value.join value (Value.I.bot (), cong) in
    set_value t var value' 
end

(** [VarManagement] defines the type t of the affine equality domain (a record that contains an optional matrix and an apron environment) and provides the functions needed for handling variables (which are defined by [RelationDomain.D2]) such as [add_vars], [remove_vars].
    Furthermore, it provides the function [simplified_monomials_from_texp] that converts an apron expression into a list of monomials of reference variables and a constant offset *)
module VarManagement (Ineq : TwoVarInequalities) =
struct
  module EConjI = EqualitiesConjunctionWithIntervals(Ineq)
  include SharedFunctions.VarManagementOps (EqualitiesConjunctionWithIntervals(Ineq))

  let dim_add = EConjI.dim_add
  let size t = BatOption.map_default (fun ((d,_),_,_) -> d) 0 t.d

  (** Parses a Texpr to obtain a (coefficient, variable) pair list to repr. a sum of a variables that have a coefficient. If variable is None, the coefficient represents a constant offset. *)
  let monomials_from_texp (t: t) texp =
    let open Apron.Texpr1 in
    let exception NotLinearExpr in
    let exception ScalarIsInfinity in
    let negate coeff_var_list =
      List.map (fun (monom, offs, divi) -> Z.(BatOption.map (fun (coeff,i) -> (neg coeff, i)) monom, neg offs, divi)) coeff_var_list in
    let multiply_with_Q dividend divisor coeff_var_list =
      List.map (fun (monom, offs, divi) -> Rhs.canonicalize Z.(BatOption.map (fun (coeff,i) -> (dividend*coeff,i)) monom, dividend*offs, divi*divisor) ) coeff_var_list in
    let multiply a b =
      (* if one of them is a constant, then multiply. Otherwise, the expression is not linear *)
      match a, b with
      | [(None,coeff, divi)], c
      | c, [(None,coeff, divi)] -> multiply_with_Q coeff divi c
      | _ -> raise NotLinearExpr
    in
    let rec convert_texpr texp =
      begin match texp with
        | Cst (Interval _) -> failwith "constant was an interval; this is not supported"
        | Cst (Scalar x) ->
          begin match SharedFunctions.int_of_scalar ?round:None x with
            | Some x -> [(None,x,Z.one)]
            | None -> raise ScalarIsInfinity end
        | Var x ->
          let var_dim = Environment.dim_of_var t.env x in
          begin match t.d with
            | None -> [(Some (Z.one,var_dim),Z.zero,Z.one)]
            | Some d ->
              (match (EConjI.get_rhs d var_dim) with
               | (Some (coeff,i), k,divi) -> [(Some (coeff,i),Z.zero,divi); (None,k,divi)]
               | (None,           k,divi) -> [                              (None,k,divi)])
          end
        | Unop  (Neg,  e, _, _) -> negate (convert_texpr e)
        | Unop  (Cast, e, _, _) -> convert_texpr e (* Ignore since casts in apron are used for floating point nums and rounding in contrast to CIL casts *)
        | Unop  (Sqrt, e, _, _) -> raise NotLinearExpr
        | Binop (Add, e1, e2, _, _) -> convert_texpr e1 @ convert_texpr e2
        | Binop (Sub, e1, e2, _, _) -> convert_texpr e1 @ negate (convert_texpr e2)
        | Binop (Mul, e1, e2, _, _) -> multiply (convert_texpr e1) (convert_texpr e2)
        | Binop _  -> raise NotLinearExpr end
    in match convert_texpr texp with
    | exception NotLinearExpr -> None
    | exception ScalarIsInfinity -> None
    | x -> Some(x)

  (** convert and simplify (wrt. reference variables) a texpr into a tuple of a list of monomials (coeff,varidx,divi) and a (constant/divi) *)
  let simplified_monomials_from_texp (t: t) texp =
    BatOption.bind (monomials_from_texp t texp)
      (fun monomiallist ->
         let d = Option.get t.d in
         let module IMap = IntMap in
         let accumulate_constants (exprcache,(aconst,adiv)) (v,offs,divi) = match v with
           | None -> let gcdee = Z.gcd adiv divi in exprcache,(Z.(aconst*divi/gcdee + offs*adiv/gcdee),Z.lcm adiv divi)
           | Some (coeff,idx) -> let (somevar,someoffs,somedivi)=Rhs.subst (EConjI.get_rhs d idx) idx (v,offs,divi) in (* normalize! *)
             let newcache = Option.map_default (fun (coef,ter) -> IMap.add ter Q.((IMap.find_default zero ter exprcache) + make coef somedivi) exprcache) exprcache somevar in
             let gcdee = Z.gcd adiv divi in
             (newcache,(Z.(aconst*divi/gcdee + offs*adiv/gcdee),Z.lcm adiv divi))
         in
         let (expr,constant) = List.fold_left accumulate_constants (IMap.empty,(Z.zero,Z.one)) monomiallist in (* abstract simplification of the guard wrt. reference variables *)
         Some (IMap.fold (fun v c acc -> if Q.equal c Q.zero then acc else (Q.num c,v,Q.den c)::acc) expr [], constant) )

  let simplified_monomials_from_texp (t: t) texp =
    let res = simplified_monomials_from_texp t texp in
    if M.tracing then M.tracel "from_texp" "%s %a -> %s" (EConjI.show @@ BatOption.get t.d) Texpr1.Expr.pretty texp
        (BatOption.map_default (fun (l,(o,d)) -> List.fold_right (fun (a,x,b) acc -> Printf.sprintf "%s*var_%d/%s + %s" (Z.to_string a) x (Z.to_string b) acc) l ((Z.to_string o)^"/"^(Z.to_string d))) "" res);
    res

  let simplify_to_ref_and_offset (t: t) texp =
    BatOption.bind (simplified_monomials_from_texp t texp )
      (fun (sum_of_terms, (constant,divisor)) ->
         (match sum_of_terms with
          | [] -> Some (None, constant,divisor)
          | [(coeff,var,divi)] -> Some (Rhs.canonicalize (Some (Z.mul divisor coeff,var), Z.mul constant divi,Z.mul divisor divi))
          |_ -> None))

  let simplify_to_ref_and_offset t texp = timing_wrap "coeff_vec" (simplify_to_ref_and_offset t) texp

  (*TODO texpr has rather few constructors. Would we be more precise if we evaluated the CIL expression instead??*)
  let eval_texpr (t:t) texp = 
    let open Apron.Texpr1 in
    let binop_function = function
      | Add -> Value.add 
      | Sub -> Value.sub
      | Mul -> Value.mul
      | Div -> Value.div
      | Mod -> Value.rem
      | Pow -> failwith "power is not supported" (*TODO should this be supported*)
    in let unop_function = function
        | Neg -> Value.neg
        | Cast -> identity
        | Sqrt -> failwith "sqrt is not supported" (*TODO should this be supported*)
    in let rec eval = function
        | Cst (Scalar x) -> 
          begin match SharedFunctions.int_of_scalar ?round:None x with
            | Some x -> Value.of_bigint x
            | None -> Value.top
          end
        | Cst (Interval _) -> failwith "constant was an interval; this is not supported" (*TODO monomials_from_texp does not support this as well, but maybe we should*)
        | Var x -> 
          let var_dim = Environment.dim_of_var t.env x in
          begin match t.d with
            | None -> Value.top
            | Some d -> EConjI.get_value d var_dim
          end
        | Binop (Sub, Var a , Var b, Int, _) ->
          (*TODO are there more locations where we can use the inequality information? What if we allow Ineq to return more precise information? (e.g. 5a < 4b + 11)*)
          let dim_a = Environment.dim_of_var t.env a in
          let dim_b = Environment.dim_of_var t.env b in
          begin match t.d with
            | None -> Value.top
            | Some d -> 
              let v = Value.sub (EConjI.get_value d dim_a) (EConjI.get_value d dim_b) in
              match EConjI.is_less_than d dim_a dim_b with
              | None -> v
              | Some true -> Value.meet v (Value.ending Z.minus_one)
              | Some false -> Value.meet v (Value.starting Z.one)
          end
        | Binop (op, a, b, Int, _) -> (binop_function op) (eval a) (eval b)
        | Unop (op, a, Int, _) -> (unop_function op) (eval a)
        | _ -> Value.top (*not integers*)
    in 
    let res = eval texp in
    if M.tracing then M.tracel "eval_texp" "%s %a -> %s" (EConjI.show @@ BatOption.get t.d) Texpr1.Expr.pretty texp (Value.show res);
    res

  (*TODO Could be more precise with query*)
  (*TODO We also only catch variables on the first level, but miss e.g. (x+7)+7 -> use more recursion similar to negate?*)
  let rec to_inequalities (t:t) texpr = 
    let open Apron.Texpr1 in
    let inequality_from_add var expr = 
      let v = eval_texpr t expr in (*TODO we evaluate some subexpressions twice when calling this in assign_texpr -> bad for performance??*)
      if Value.must_be_pos v then 
        [(Ineq.Gt, var)]
      else if Value.must_be_neg v then 
        [(Ineq.Lt, var)]
      else if Value.leq v (Value.of_bigint Z.zero) then 
        [(Ineq.Eq, var)]
      else if Value.leq v (Value.starting Z.zero) then 
        [(Ineq.Ge, var)]
      else if Value.leq v (Value.ending Z.zero) then
        [(Ineq.Le, var)]
      else
        []
    in let inequality_from_mul var expr = 
         let v_expr = eval_texpr t expr in
         let v_var = eval_texpr t (Var var) in
         if   Value.leq v_expr (Value.of_bigint Z.one)
           || Value.leq v_var (Value.of_bigint Z.zero) 
         then [(Ineq.Eq, var)]
         else
           match Value.must_be_pos v_expr, Value.must_be_neg v_expr, Value.must_be_pos v_var, Value.must_be_neg v_var with
           | true, _   , true, _    -> if Value.contains v_expr Z.one then [Ineq.Ge, var] else [Ineq.Gt, var]
           | _,    true, _   , true -> [Ineq.Gt, var]
           | true, _   , _   , true -> if Value.contains v_expr Z.one then [Ineq.Le, var] else [Ineq.Lt, var] 
           | _   , true, true, _    -> [Ineq.Lt, var]
           | _   , _   , _   , _    -> []
    in match texpr with 
    | Binop (Add, Var x, Var y, _, _) -> inequality_from_add x (Var y) @ inequality_from_add y (Var x)
    | Binop (Add, e, Var y, _, _) 
    | Binop (Add, Var y, e, _, _) -> inequality_from_add y e
    | Binop (Mul, Var x, Var y, _, _) -> inequality_from_mul x (Var y) @ inequality_from_mul y (Var x)
    | Binop (Mul, e, Var y, _, _)
    | Binop (Mul, Var y, e, _, _) -> inequality_from_add y e
    | Binop (Sub, Var y, e, _, _) ->       
      let v = eval_texpr t e in 
      if Value.must_be_pos v then 
        [(Ineq.Lt, y)]
      else if Value.must_be_neg v then 
        [(Ineq.Gt, y)]
      else if Value.leq v (Value.of_bigint Z.zero) then 
        [(Ineq.Eq, y)]
      else if Value.leq v (Value.starting Z.zero) then 
        [(Ineq.Le, y)]
      else if Value.leq v (Value.ending Z.zero) then
        [(Ineq.Ge, y)]
      else
        []
    | Binop (Div, Var y, e, _, _) -> begin
        let v_expr = eval_texpr t e in
        let v_var = eval_texpr t (Var y) in
        if   Value.leq v_expr (Value.of_bigint Z.one)
          || Value.leq v_var (Value.of_bigint Z.zero) 
        then [(Ineq.Eq, y)]
        else
          match Value.must_be_pos v_expr, Value.must_be_neg v_expr, Value.must_be_pos v_var, Value.must_be_neg v_var with
          | true, _   , true, _    -> if Value.contains v_expr Z.one then [Ineq.Le, y] else [Ineq.Lt, y]
          | _,    true, _   , true -> [Ineq.Gt, y]
          | true, _   , _   , true -> if Value.contains v_expr Z.one then [Ineq.Ge, y] else [Ineq.Gt, y] 
          | _   , true, true, _    -> [Ineq.Lt, y]
          | _   , _   , _   , _    -> []
      end
    | Binop (Mod, e, Var y, _, _) -> 
      let v_var = eval_texpr t (Var y) in
      if Value.must_be_pos v_var then
        [Ineq.Lt, y]
      else if Value.must_be_neg v_var then 
        [Ineq.Gt, y]
      else []
    | Unop (Neg, e, _, _) ->
      let v = eval_texpr t e in
      let negate (cond, var) =
        if Value.must_be_pos v then 
          match cond with 
          | Ineq.Lt | Ineq.Le | Ineq.Eq -> Some (Ineq.Lt, var)
          | _ -> None
        else if Value.must_be_neg v then 
          match cond with 
          | Ineq.Gt | Ineq.Ge | Ineq.Eq -> Some (Ineq.Gt, var)
          | _ -> None
        else if Value.leq v (Value.of_bigint Z.zero) then 
          Some (cond, var)
        else if Value.leq v (Value.starting Z.zero) then 
          match cond with 
          | Ineq.Lt -> Some (Ineq.Lt, var)
          | Ineq.Le | Ineq.Eq -> Some (Ineq.Le, var)
          | _ -> None
        else if Value.leq v (Value.ending Z.zero) then
          match cond with 
          | Ineq.Gt -> Some (Ineq.Gt, var)
          | Ineq.Ge | Ineq.Eq -> Some (Ineq.Ge, var)
          | _ -> None
        else
          None
      in List.filter_map negate (to_inequalities t e)
    | Unop (Cast, e, _, _) -> to_inequalities t e
    | Var x -> [(Ineq.Eq, x)]
    | _ -> []

  let to_inequalities (t:t) texpr = 
    let res = to_inequalities t texpr in
    let show_ineq (cond, var) = Ineq.show_cond cond ^ " " ^ Var.show var ^ ", "
    in if M.tracing then M.tracel "inequalities" "expr: %a ineq: %s" Texpr1.Expr.pretty texpr (List.fold (^) "" @@ List.map show_ineq res);
    res 


  let assign_const t var const divi = match t.d with
    | None -> t
    | Some t_d -> {d = Some (EConjI.set_rhs t_d var (None, const, divi)); env = t.env}


end


module ExpressionBounds (Ineq : TwoVarInequalities): (SharedFunctions.ConvBounds with type t = VarManagement(Ineq).t) =
struct
  include VarManagement (Ineq)

  let bound_texpr t texpr =
    let v = eval_texpr t (Texpr1.to_expr texpr) in
    let from_top = function
      | TopIntOps.Int x -> Some x
      | _ -> None 
    in let min = BatOption.bind (Value.minimal v) (from_top)
    in let max = BatOption.bind (Value.maximal v) (from_top) in
    (if M.tracing then M.tracel "bounds" "min: %s max: %s" (BatOption.map_default Z.to_string "None" min) (BatOption.map_default Z.to_string "None" max);
     min, max)

  let bound_texpr d texpr1 = timing_wrap "bounds calculation" (bound_texpr d) texpr1
end

module D (Ineq : TwoVarInequalities) =
struct
  include Printable.Std
  include ConvenienceOps (SharedFunctions.Mpqf)
  module VarManagement = VarManagement(Ineq)
  include VarManagement

  module Bounds = ExpressionBounds(Ineq)
  module V = RelationDomain.V
  module Arg = struct
    let allow_global = true
  end
  module Convert = SharedFunctions.Convert (V) (Bounds) (Arg) (SharedFunctions.Tracked)

  type var = V.t

  let name () = "lin2vareq_pentagon"

  let to_yojson _ = failwith "ToDo Implement in future"

  (** t.d is some empty array and env is empty *)
  let is_bot t = equal t (bot ())

  (** forall x_i in env, x_i:=X_i+0 *)
  let top_of env = {d = Some (EConjI.make_empty_with_size (Environment.size env)); env = env}

  (** env = \emptyset, d = Some([||]) *)
  let top () = {d = Some (EConjI.empty()); env = empty_env}

  (** is_top returns true for top_of array and empty array; precondition: t.env and t.d are of same size *)
  let is_top t = GobOption.exists EConjI.is_top_con t.d

  let to_subscript i =
    let transl = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|] in
    let rec subscr i =
      if i = 0 then ""
      else (subscr (i/10)) ^ transl.(i mod 10) in
    subscr i

  let show_var env i =
    let res = Var.to_string (Environment.var_of_dim env i) in
    match String.split_on_char '#' res with
    | varname::rest::[] -> varname ^ (try to_subscript @@ int_of_string rest with _ -> "#" ^ rest)
    | _ -> res

  (** prints the current variable equalities with resolved variable names *)
  let show varM =
    match varM.d with
    | None -> "⊥\n"
    | Some (((dim,_), _, _) as arr) ->
      if is_bot varM then
        "Bot \n"
      else
        EConjI.show_formatted (show_var varM.env) arr ^ (to_subscript dim)

  let pretty () (x:t) = text (show x)
  let printXml f x = BatPrintf.fprintf f "<value>\n<map>\n<key>\nequalities\n</key>\n<value>\n%s</value>\n<key>\nenv\n</key>\n<value>\n%a</value>\n</map>\n</value>\n" (XmlUtil.escape (show x)) Environment.printXml x.env
  let eval_interval ask t texpr = 
    let from_top = function
      | TopIntOps.Int x -> Some x
      | _ -> None 
    in let i = eval_texpr t (Texpr1.to_expr texpr)
    in if M.tracing then M.tracel "eval_interval" "evaluating %a in %s to %s" Texpr1.pretty texpr (show t) (Value.show i);
    match fst i with
    | None -> (None, None)
    | Some (l, u) -> (from_top l, from_top u)

  let refine_with_tcons t tcons = 
    match t.d with 
    | None -> t
    | Some d ->
      let initial_value = match Tcons1.get_typ tcons with
        | EQ | DISEQ -> Value.of_bigint Z.zero
        | SUP -> Some (Int Z.one, Top Pos), Value.C.top ()
        | SUPEQ -> Some (Int Z.zero, Top Pos), Value.C.top ()
        | EQMOD (n) -> 
          begin match SharedFunctions.int_of_scalar ?round:None n with
              None -> Value.top 
            | Some n -> Value.of_congruence (Z.zero, n)
          end
      in 
      let is_inequality = Tcons1.get_typ tcons = DISEQ in
      let refine_var d var value =
        let dim = Environment.dim_of_var t.env var in
        if is_inequality then begin
          match Value.to_int value, Value.to_int (EConjI.get_value d dim) with 
          | Some v, Some i when TopIntOps.equal v i ->
            if M.tracing then M.trace "refine_tcons" "inequality %s <> %s must be wrong" (Var.to_string var) (Value.show value);
            raise EConj.Contradiction
          | _ -> d (*TODO if value is a constant, we sometimes could do some refinement*)
        end else (
          if M.tracing then M.trace "refine_tcons" "refining var %s with %s" (Var.to_string var) (Value.show value) ;
          EConjI.meet_with_one_value dim value d Value.meet )
      in
      let eval d texpr = eval_texpr {d= Some d; env = t.env} texpr in
      let open Texpr1 in
      let rec refine_values d value expr = 
        if M.tracing then M.trace "refine_tcons" "refining expr %s with %s" (GobFormat.asprint print_expr expr) (Value.show value) ;
        match expr with
        | Binop (op,a,b,_,_) -> 
          let refine_both op_a op_b = 
            let b_val = eval d b in
            let d' = refine_values d (op_a value b_val) a in
            let a_val = eval d' a in
            refine_values d' (op_b value a_val) b
          in begin
            match op with 
            | Add -> refine_both (Value.sub) (Value.sub)
            | Sub -> refine_both (Value.add) (Fun.flip Value.sub) 
            (*Because the overflow handeling in SharedFunctions guarantees us no wrapping behaviour, this is always invertible *)
            | Mul -> refine_both (Value.div) (Value.div)
            (*DIV and MOD are largely inspired by BaseInvariant*)
            | Div -> 
              (* Integer division means we need to add the remainder, so instead of just `a = c*b` we have `a = c*b + a%b`.
               * However, a%b will give [-b+1, b-1] for a=top, but we only want the positive/negative side depending on the sign of c*b.
               * If c*b = 0 or it can be positive or negative, we need the full range for the remainder. *)
              let b_val = eval d b in
              if Value.to_int b_val = Some (Int Z.zero) then begin
                M.error ~category:M.Category.Integer.div_by_zero ~tags:[CWE 369] "Must Undefined Behavior: Second argument of div or mod is 0";
                d
              end else 
                let a_val = eval d a in
                let b_c = Value.mul b_val value in
                let rem =
                  let is_pos = Value.must_be_pos b_c in
                  let is_neg = Value.must_be_neg b_c in
                  let full = Value.rem a_val b_val in
                  if is_pos then Value.meet (Value.starting Z.zero) full
                  else if is_neg then Value.meet (Value.ending Z.zero) full
                  else full
                in let d' = refine_values d (Value.add b_c rem) a in
                refine_values d' (Value.div (Value.sub a_val rem) value) b
            | Mod ->         
              (* a' = a/b*b + c and derived from it b' = (a-c)/(a/b)
                * The idea is to formulate a' as quotient * divisor + remainder. *)
              let a_val = eval d a in
              let b_val = eval d b in
              if Value.to_int b_val = Some (Int Z.zero) then begin
                M.error ~category:M.Category.Integer.div_by_zero ~tags:[CWE 369] "Must Undefined Behavior: Second argument of div or mod is 0";
                d
              end else 
                let a' = Value.add (Value.mul (Value.div a_val b_val) b_val) value in
                let b' = Value.div (Value.sub a_val value) (Value.div a_val value) in
                (* However, for [2,4]%2 == 1 this only gives [3,4].
                 * If the upper bound of a is divisible by b, we can also meet with the result of a/b*b - c to get the precise [3,3].
                 * If b is negative we have to look at the lower bound. *)
                let is_divisible bound =
                  match bound a_val with
                  | Some (TopIntOps.Int ba) -> Value.rem (Value.of_bigint ba) b_val |> Value.to_int = Some (Int Z.zero)
                  | _ -> false
                in
                let max_pos = match Value.maximal b_val with None -> true | Some x -> TopIntOps.compare x TopIntOps.zero >= 0 in
                let min_neg = match Value.minimal b_val with None -> true | Some x -> TopIntOps.compare x TopIntOps.zero < 0 in
                let implies a b = not a || b in
                let a'' =
                  if implies max_pos (is_divisible Value.maximal) && implies min_neg (is_divisible Value.minimal) then
                    Value.meet a' (Value.sub (Value.mul (Value.div a_val b_val) b_val) value)
                  else a'
                in
                let a''' =
                  (* if both b and c are definite, we can get a precise value in the congruence domain *)
                  match Value.to_int b_val, Value.to_int value with
                  | Some (TopIntOps.Int b), Some (TopIntOps.Int c) ->
                    (* a%b == c  -> a: c+bℤ *)
                    let t = Value.of_congruence (c, b) in
                    (*If the calculated congruence implies this one, we have a contradiction*)
                    (*TODO we could check for definite values and contradictions at every step, not just in MOD / Variable assignment*)
                    if is_inequality && Value.leq a_val (Value.of_congruence (c,b)) then raise EConj.Contradiction;
                    Value.meet a'' t
                  | _, _ -> a''
                in
                let d' = refine_values d (b') b in
                refine_values d' (a''') a
            | Pow -> failwith "refine_with tcons: pow unsupported"
          end
        | Unop (op, e,_,_) -> begin match op with 
            | Neg -> refine_values d (Value.neg value) e
            | Cast -> refine_values d value e
            | Sqrt -> failwith "sqrt is not supported" (*TODO should this be supported*)
          end
        | Cst (Scalar x) -> 
          begin match SharedFunctions.int_of_scalar ?round:None x with
            | Some x -> (if Value.contains value x || is_inequality then d else raise EConj.Contradiction) 
            | None -> d
          end
        | Cst (Interval _) -> failwith "constant was an interval; this is not supported" 
        | Var v -> refine_var d v value
      in let refine_inequalities ((econ, vs, ineq) as d) expr = 
           let rhss = EConjI.get_rhs d in
           let vss = EConjI.get_value d in
           match expr with 
           (*TODO we could use to_inequalities for more flexible handeling?*)
           | Binop (Sub, Var a, Var b, Int, _) -> 
             begin
               let dim_a = Environment.dim_of_var t.env a in
               let dim_b = Environment.dim_of_var t.env b in
               if M.tracing then M.tracel "meet_condition" "calling from refine inside %s" (EConjI.show d)   ;
               let ineq' = match Tcons1.get_typ tcons with 
                 | EQ -> Ineq.meet_condition dim_a dim_b Ineq.Eq rhss vss ineq
                 | SUP -> Ineq.meet_condition dim_b dim_a Ineq.Lt rhss vss ineq
                 | SUPEQ -> Ineq.meet_condition dim_b dim_a Ineq.Le rhss vss ineq
                 | _ -> ineq
               in (econ, vs, ineq')
             end
           | _ -> d
      in try 
        let expr = to_expr @@ Tcons1.get_texpr1 tcons in 
        let d' = refine_values d initial_value expr in
        let d'' = refine_inequalities d' expr in
        {d=Some d'';env=t.env}
      with EConj.Contradiction -> bot_env

  let refine_with_tcons t tcons = 
    let res = refine_with_tcons t tcons in
    if M.tracing then M.tracel "refine_tcons" "before: %s \n refined with %s\n result: %s " (show t) (Tcons1.show tcons) (show res)  ;
    res

  let meet_with_one_conj t i (var, o, divi) =
    match t.d with
    | None -> t
    | Some d ->
      try
        { d = Some (EConjI.meet_with_one_conj d i (var, o, divi)); env = t.env}
      with EConj.Contradiction ->
        if M.tracing then M.trace "meet" " -> Contradiction with conj\n";
        { d = None; env = t.env}

  let meet_with_one_conj t i e =
    let res = meet_with_one_conj t i e in
    if M.tracing then M.tracel "meet" "%s with single eq %s=%s -> %s" (show t) (Z.(to_string @@ Tuple3.third e)^ show_var t.env i) (Rhs.show_rhs_formatted (show_var t.env) e) (show res);
    res

  let meet_with_one_value meet_function i value t =
    let res = match t.d with
      | None -> t
      | Some d ->
        try
          { d = Some (EConjI.meet_with_one_value i value d meet_function); env = t.env}
        with EConj.Contradiction ->
          if M.tracing then M.trace "meet" " -> Contradiction with value\n";
          { d = None; env = t.env}
    in
    if M.tracing then M.tracel "meet" "%s with single value %s=%s -> %s" (show t) (show_var t.env i) (Value.show value) (show res);
    res

  (*TODO do I need a narrow function??*)
  let meet_with_inequalities ineq t = 
    match t.d with 
    | None -> t
    | Some ((econ, vs, ineq2) as d) ->
      try
        { d = Some (econ, vs, Ineq.meet (EConjI.get_rhs d) (EConjI.get_value d) ineq ineq2); env = t.env}
      with EConj.Contradiction ->
        if M.tracing then M.trace "meet" " -> Contradiction with inequalities\n";
        { d = None; env = t.env}

  let meet_with_inequalities ineq t = 
    let res = meet_with_inequalities ineq t in
    if M.tracing then M.tracel "meet" "%s with inequalities %s -> %s" (show t) (Ineq.show_formatted (show_var t.env) ineq) (show res);
    res

  let meet' t1 t2 meet_function =     
    let sup_env = Environment.lce t1.env t2.env in
    let t1 = change_d t1 sup_env ~add:true ~del:false in
    let t2 = change_d t2 sup_env ~add:true ~del:false in
    match t1.d, t2.d with
    | Some d1', Some (econ, vs, ineq) ->
      let conj_met = IntMap.fold (fun lhs rhs map -> meet_with_one_conj map lhs rhs) (snd econ) t1 (* even on sparse d2, this will chose the relevant conjs to meet with*)
      in let vals_met = IntMap.fold (meet_with_one_value meet_function) vs conj_met
      in meet_with_inequalities ineq vals_met 
    | _ -> {d = None; env = sup_env}

  let meet t1 t2 =
    meet' t1 t2 Value.meet

  let meet t1 t2 =
    let res = meet t1 t2 in
    if M.tracing then M.tracel "meet" "meet a: %s\n U  \n b: %s \n -> %s" (show t1) (show t2) (show res) ;
    res

  let meet t1 t2 = timing_wrap "meet" (meet t1) t2

  let leq t1 t2 =
    let env_comp = Environment.cmp t1.env t2.env in (* Apron's Environment.cmp has defined return values. *)
    let implies ts i (var, offs, divi) =
      let tuple_cmp = Tuple3.eq (Option.eq ~eq:(Tuple2.eq (Z.equal) (Int.equal))) (Z.equal) (Z.equal) in
      match var with
      (* directly compare in case of constant value *)
      | None -> tuple_cmp (var, offs, divi) (EConj.get_rhs ts i)
      (* normalize in case of a full blown equality *)
      | Some (coeffj,j) -> tuple_cmp (EConj.get_rhs ts i) @@ Rhs.subst (EConj.get_rhs ts j) j (var, offs, divi)
    in
    (*TODO allow congruence implied by Rhs? or fix bug that some aren't always set!!*)
    let implies_value v i value = Value.leq (EConjI.get_value v i) value
    in
    if env_comp = -2 || env_comp > 0 then false else
    if is_bot_env t1 || is_top t2 then true
    else if is_bot_env t2 || is_top t1 then false else
      let m1, (econ2, vs2, ineq2) = Option.get t1.d, Option.get t2.d in
      let (econ1, _, ineq1) as m1' = if env_comp = 0 then m1 else VarManagement.dim_add (Environment.dimchange t1.env t2.env) m1 in
      IntMap.for_all (implies econ1) (snd econ2) (* even on sparse m2, it suffices to check the non-trivial equalities, still present in sparse m2 *)
      && IntMap.for_all (implies_value m1') (vs2)
      && Ineq.leq ineq1 (EConjI.get_value m1') ineq2

  let leq a b = timing_wrap "leq" (leq a) b

  let leq t1 t2 =
    let res = leq t1 t2 in
    if M.tracing then M.tracel "leq" "leq a: %s b: %s -> %b" (show t1) (show t2) res ;
    res

  (*The first parameter is the function used to join two values. Different uses for join / widen*)
  (*TODO do we need the same for the inequalities? not for simple inequalities, but for more complex ones*)
  let join' join_function a b  = 
    let join_econj ad bd env = (LinearTwoVarEqualityDomain.D.join {d = Some ad; env} {d = Some bd; env}).d
    in
    (*Check all variables (up to index vars) if we need to save an value for them*)
    let rec collect_values x y econj_joined vars t =
      if vars < 0 then t
      else if EConj.nontrivial econj_joined vars then collect_values x y econj_joined (vars-1) t (*we only need values for roots of the connected components*)
      else let joined_value = join_function (EConjI.get_value x vars) (EConjI.get_value y vars) in
        collect_values x y econj_joined (vars-1) (EConjI.join_with_one_value vars joined_value t)
    in
    let join_d ((econ_x, _, ineq_x) as x) ((econ_y, _, ineq_y) as y) env = 
      let econj' = join_econj (econ_x) (econ_y) env in
      match econj' with 
        None ->  None 
      | Some econj'' ->
        if M.tracing then M.tracel "join" "join_econj of %s, %s resulted in %s" (EConjI.show x) (EConjI.show y) (EConj.show @@ snd econj'');
        let ineq' = Ineq.join ineq_x (EConjI.get_value x) ineq_y (EConjI.get_value y) in
        Some (collect_values x y econj'' ((Environment.size env)-1) (econj'', IntMap.empty, ineq'))         
    in
    (*Normalize the two domains a and b such that both talk about the same variables*)
    match a.d, b.d with
    | None, _ -> b
    | _, None -> a
    | Some x, Some y when is_top a || is_top b ->
      let new_env = Environment.lce a.env b.env in
      top_of new_env
    | Some x, Some y when (Environment.cmp a.env b.env <> 0) ->
      let sup_env = Environment.lce a.env b.env in
      let mod_x = dim_add (Environment.dimchange a.env sup_env) x in
      let mod_y = dim_add (Environment.dimchange b.env sup_env) y in
      {d = join_d mod_x mod_y sup_env; env = sup_env}
    | Some x, Some y when EConjI.equal x y -> {d = Some x; env = a.env}
    | Some x, Some y  -> {d = join_d x y a.env; env = a.env} 


  let join = join' (Value.join) 
  let join a b = timing_wrap "join" (join a) b

  let join a b =
    let res = join a b in
    if M.tracing then M.tracel "join" "join a: %s b: %s -> %s" (show a) (show b) (show res) ;
    assert(leq a res);
    assert(leq b res);
    res

  let widen = join' (Value.widen) 

  let widen a b =
    let res = widen a b in
    if M.tracing then M.tracel "widen" "widen a: %s b: %s -> %s" (show a) (show b) (show res) ;
    res

  let narrow a b = meet' a b Value.narrow

  let narrow a b =
    let res = narrow a b in
    if M.tracing then M.tracel "narrow" "narrow a: %s b: %s -> %s" (show a) (show b) (show res) ;
    res

  let pretty_diff () (x, y) =
    dprintf "%s: %a not leq %a" (name ()) pretty x pretty y

  let forget_var t var =
    if is_bot_env t || is_top t then t
    else
      {d = Some (EConjI.forget_variable (Option.get t.d) (Environment.dim_of_var t.env var)); env = t.env}

  let forget_vars t vars =
    if is_bot_env t || is_top t || List.is_empty vars then
      t
    else
      let newm = List.fold (fun map i -> EConjI.forget_variable map (Environment.dim_of_var t.env i)) (Option.get t.d) vars in
      {d = Some newm; env = t.env}

  let forget_vars t vars =
    let res = forget_vars t vars in
    if M.tracing then M.tracel "ops" "forget_vars %s -> %s" (show t) (show res);
    res

  let forget_vars t vars = timing_wrap "forget_vars" (forget_vars t) vars

  (** implemented as described on page 10 in the paper about Fast Interprocedural Linear Two-Variable Equalities in the Section "Abstract Effect of Statements"
      This makes a copy of the data structure, it doesn't change it in-place. *)
  let assign_texpr (t: VarManagement.t) var texp =
    match t.d with
    | Some (econj, vs, ineq) ->
      let var_i = Environment.dim_of_var t.env var (* this is the variable we are assigning to *) in
      let t' = match simplify_to_ref_and_offset t texp with
        | None ->
          (* Statement "assigned_var = ?" (non-linear assignment) *)
          forget_var t var
        | Some (None, off, divi) ->
          (* Statement "assigned_var = off" (constant assignment) *)
          assign_const (forget_var t var) var_i off divi
        | Some (Some (coeff_var,exp_var), off, divi) when var_i = exp_var ->
          (* Statement "assigned_var = (coeff_var*assigned_var + off) / divi" *)
          {d=Some (EConj.affine_transform econj var_i (coeff_var, var_i, off, divi), vs, ineq); env=t.env }          
        | Some (Some monomial, off, divi) ->
          (* Statement "assigned_var = (monomial) + off / divi" (assigned_var is not the same as exp_var) *)
          meet_with_one_conj (forget_var t var) var_i (Some (monomial), off, divi)
      in begin match t'.d with 
          None -> if M.tracing then M.tracel "ops" "assign_texpr resulted in bot (before: %s, expr: %s) " (show t) (Texpr1.show (Texpr1.of_expr t.env texp));
          bot_env
        | Some d' -> 
          (*TODO use query for more precision instead?!*)
          let (econ, vs, ineq) as d'' = EConjI.set_value d' var_i (VarManagement.eval_texpr t texp) in
          if M.tracing then M.tracel "assign_texpr" "assigning %s = %s before inequality: %s" (Var.show var) (Texpr1.show (Texpr1.of_expr t.env texp)) (show {d = Some (econ, vs, ineq); env = t.env});
          let meet_cond ineq (cond, var) = 
            let dim = Environment.dim_of_var t.env var in
            if dim <> var_i then (*TODO If cond = Eq, we could restore the previous state before forgetting the variable*)
              Ineq.meet_condition var_i dim cond (EConjI.get_rhs d'') (EConjI.get_value d'') ineq
            else ineq
          in
          let ineq' = List.fold meet_cond ineq (VarManagement.to_inequalities t texp) in
          if M.tracing then M.tracel "assign_texpr" "after inequality: %s" (show {d = Some (econ, vs, ineq'); env = t.env});
          {d = Some (econ, vs, ineq'); env = t'.env} 
      end
    | None -> bot_env

  let assign_texpr t var texp = timing_wrap "assign_texpr" (assign_texpr t var) texp

  (* no_ov -> no overflow
     if it's true then there is no overflow
      -> Convert.texpr1_expr_of_cil_exp handles overflow *)
  let assign_exp ask (t: VarManagement.t) var exp (no_ov: bool Lazy.t) =
    let t = if not @@ Environment.mem_var t.env var then add_vars t [var] else t in
    match Convert.texpr1_expr_of_cil_exp ask t t.env exp no_ov with
    | texp -> assign_texpr t var texp
    | exception Convert.Unsupported_CilExp _ -> forget_var t var

  let assign_exp ask t var exp no_ov =
    let res = assign_exp ask t var exp no_ov in
    if M.tracing then M.tracel "ops" "assign_exp t:\n %s \n var: %a \n exp: %a\n no_ov: %b -> \n %s"
        (show t) Var.pretty var d_exp exp (Lazy.force no_ov) (show res);
    res

  let assign_var (t: VarManagement.t) v v' =
    let t = add_vars t [v; v'] in
    assign_texpr t v (Var v')

  let assign_var t v v' =
    let res = assign_var t v v' in
    if M.tracing then M.tracel "ops" "assign_var t:\n %s \n v: %a \n v': %a\n -> %s" (show t) Var.pretty v Var.pretty v' (show res);
    res

  (** Parallel assignment of variables.
      First apply the assignments to temporary variables x' and y' to keep the old dependencies of x and y
      and in a second round assign x' to x and y' to y
  *)
  let assign_var_parallel t vv's =
    let assigned_vars = List.map fst vv's in
    let t = add_vars t assigned_vars in
    let primed_vars = List.init (List.length assigned_vars) (fun i -> Var.of_string (Int.to_string i  ^"'")) in (* TODO: we use primed vars in analysis, conflict? *)
    let t_primed = add_vars t primed_vars in
    let multi_t = List.fold_left2 (fun t' v_prime (_,v') -> assign_var t' v_prime v') t_primed primed_vars vv's in
    match multi_t.d with
    | Some arr when not @@ is_top multi_t ->
      let switched_arr = List.fold_left2 (fun multi_t assigned_var primed_var-> assign_var multi_t assigned_var primed_var) multi_t assigned_vars primed_vars in
      drop_vars switched_arr primed_vars ~del:true
    | _ -> t

  let assign_var_parallel t vv's =
    let res = assign_var_parallel t vv's in
    if M.tracing then M.tracel "ops" "assign_var parallel: %s -> %s" (show t) (show res);
    res

  let assign_var_parallel t vv's = timing_wrap "var_parallel" (assign_var_parallel t) vv's

  let assign_var_parallel_with t vv's =
    (* TODO: If we are angling for more performance, this might be a good place ot try. `assign_var_parallel_with` is used whenever a function is entered (body),
       in unlock, at sync edges, and when entering multi-threaded mode. *)
    let t' = assign_var_parallel t vv's in
    t.d <- t'.d;
    t.env <- t'.env

  let assign_var_parallel_with t vv's =
    if M.tracing then M.tracel "var_parallel" "assign_var parallel'";
    assign_var_parallel_with t vv's

  let assign_var_parallel' t vs1 vs2 =
    let vv's = List.combine vs1 vs2 in
    assign_var_parallel t vv's

  let assign_var_parallel' t vv's =
    let res = assign_var_parallel' t vv's in
    if M.tracing then M.tracel "ops" "assign_var parallel'";
    res

  let substitute_exp ask t var exp no_ov =
    let t = if not @@ Environment.mem_var t.env var then add_vars t [var] else t in
    let res = assign_exp ask t var exp no_ov in
    forget_var res var

  let substitute_exp ask t var exp no_ov =
    let res = substitute_exp ask t var exp no_ov in
    if M.tracing then M.tracel "ops" "Substitute_expr t: \n %s \n var: %a \n exp: %a \n -> \n %s" (show t) Var.pretty var d_exp exp (show res);
    res

  let substitute_exp ask t var exp no_ov = timing_wrap "substitution" (substitute_exp ask t var exp) no_ov

  (** Assert a constraint expression.
      The overflow is completely handled by the flag "no_ov",
      which is set in relationAnalysis.ml via the function no_overflow.
      In case of a potential overflow, "no_ov" is set to false
      and Convert.tcons1_of_cil_exp will raise the exception Unsupported_CilExp Overflow

      meet_tcons -> meet with guard in if statement
      texpr -> tree expr (right hand side of equality)
      -> expression used to derive tcons -> used to check for overflow
      tcons -> tree constraint (expression < 0)
      -> does not have types (overflow is type dependent)
  *)
  let meet_tcons ask t tcons original_expr no_ov =
    match t.d with
    | None -> t
    | Some d ->
      let expr = (Texpr1.to_expr @@ Tcons1.get_texpr1 tcons) in
      (* meet EConj*)
      let t' = match simplified_monomials_from_texp t expr with
        | None -> t
        | Some (sum_of_terms, (constant,divisor)) ->(
            match sum_of_terms with
            | [] -> (* no reference variables in the guard, so check constant for zero *)
              begin match Tcons1.get_typ tcons with
                | EQ when Z.equal constant Z.zero -> t
                | SUPEQ when Z.geq constant Z.zero -> t
                | SUP when Z.gt constant Z.zero -> t
                | DISEQ when not @@ Z.equal constant Z.zero -> t
                | EQMOD _ -> t
                | _ -> bot_env (* all other results are violating the guard *)
              end
            | [(coeff, index, divi)] -> (* guard has a single reference variable only *)
              if Tcons1.get_typ tcons = EQ then
                meet_with_one_conj t index (Rhs.canonicalize (None, Z.neg @@ Z.(divi*constant),Z.(coeff*divisor)))
              else
                t (* only EQ is supported in equality based domains *)
            | [(c1,var1,d1); (c2,var2,d2)] -> (* two variables in relation needs a little sorting out *)
              begin match Tcons1.get_typ tcons with
                | EQ -> (* c1*var1/d1 + c2*var2/d2 +constant/divisor = 0*)
                  (* ======>  c1*divisor*d2 * var1 = -c2*divisor*d1 * var2 +constant*-d1*d2*)
                  (*   \/     c2*divisor*d1 * var2 = -c1*divisor*d2 * var1 +constant*-d1*d2*)
                  let open Z in
                  if var1 < var2 then
                    meet_with_one_conj t var2 (Rhs.canonicalize (Some (neg @@ c1*divisor,var1),neg @@ constant*d2*d1,c2*divisor*d1))
                  else
                    meet_with_one_conj t var1 (Rhs.canonicalize (Some (neg @@ c2*divisor,var2),neg @@ constant*d2*d1,c1*divisor*d2))
                | _-> t (* Not supported in equality based 2vars without coeffiients *)
              end
            | _ -> t (* For equalities of more then 2 vars we just return t *))
      in if t'.d = None then (if M.tracing then M.tracel "meet_tcons" "meet_conj resulted in None (expr: %s)" (Tcons1.show tcons); t') else begin
        if M.tracing then M.tracel "meet_tcons" "after conj: %s (expr: %s)" (show t') (Tcons1.show tcons);
        refine_with_tcons t' tcons
      end


  let meet_tcons ask t tcons original_expr no_ov  =
    let res = meet_tcons ask t tcons original_expr no_ov
    in if M.tracing then M.tracel "meet_tcons" "meet_tcons with expr: %a no_ov:%b : %s -> %s" d_exp original_expr (Lazy.force no_ov) (show t) (show res);
    res


  let meet_tcons t tcons expr = timing_wrap "meet_tcons" (meet_tcons t tcons) expr

  let unify a b =
    meet a b

  let unify a b =
    let res = unify a b in
    if M.tracing then M.tracel "ops" "unify: %s\n    U\n %s -> %s" (show a) (show b) (show res);
    res

  (** Assert a constraint expression. Defined in apronDomain.apron.ml

      If the constraint is never fulfilled, then return bottom.
      Else the domain can be modified with the new information given by the constraint.

      It basically just calls the function meet_tcons.

      It is called by eval (defined in sharedFunctions), but also when a guard in
      e.g. an if statement is encountered in the C code.

  *)
  let assert_constraint ask d e negate (no_ov: bool Lazy.t) =
    match Convert.tcons1_of_cil_exp ask d d.env e negate no_ov with
    | tcons1 -> meet_tcons ask d tcons1 e no_ov
    | exception Convert.Unsupported_CilExp _ -> d

  let assert_constraint ask d e negate no_ov = timing_wrap "assert_constraint" (assert_constraint ask d e negate) no_ov

  let relift t = t

  (*TODO add inequalities (and value information?) to invariants*)
  (** representation as C expression

      This function returns all the equalities that are saved in our datastructure t.

      Lincons -> linear constraint *)
  let invariant t =
    let of_coeff xi coeffs o =
      let typ = (Option.get @@ V.to_cil_varinfo xi).vtype in
      let ikind = Cilfacade.get_ikind typ in
      let cst = Coeff.s_of_z (IntDomain.Size.cast ikind o) in
      let lincons = Lincons1.make (Linexpr1.make t.env) Lincons1.EQ in
      Lincons1.set_list lincons coeffs (Some cst);
      lincons
    in
    let get_const acc i = function
      | (None, o, d) ->
        let xi = Environment.var_of_dim t.env i in
        of_coeff xi [(GobApron.Coeff.s_of_z @@ Z.neg d, xi)] o :: acc
      | (Some (c,r), _,_) when r = i -> acc
      | (Some (c,r), o, d) ->
        let xi = Environment.var_of_dim t.env i in
        let ri = Environment.var_of_dim t.env r in
        of_coeff xi [(GobApron.Coeff.s_of_z @@ Z.neg d, xi); (GobApron.Coeff.s_of_z c, ri)] o :: acc
    in
    BatOption.get t.d |> fun ((_,map),_,_) -> IntMap.fold (fun lhs rhs list -> get_const list lhs rhs) map []

  let cil_exp_of_lincons1 = Convert.cil_exp_of_lincons1

  let env t = t.env

  type marshal = t
  (* marshal is not compatible with apron, therefore we don't have to implement it *)
  let marshal t = t

  let unmarshal t = t

end

module D2 (Ineq : TwoVarInequalities): RelationDomain.RD with type var = Var.t =
struct
  module D = D(Ineq)
  module ConvArg = struct
    let allow_global = false
  end
  include SharedFunctions.AssertionModule (D.V) (D) (ConvArg)
  include D

  (*We can be more precise than the function from the AssertionModule by including congruence information*)
  let eval_int ask d e no_ov =
    let module ID = Queries.ID in
    match Cilfacade.get_ikind_exp e with
    | exception Cilfacade.TypeOfError _
    | exception Invalid_argument _ ->
      ID.top () (* real top, not a top of any ikind because we don't even know the ikind *)
    | ik ->
      if M.tracing then M.trace "relation" "eval_int: exp_is_constraint %a = %B" d_plainexp e (exp_is_constraint e);
      if exp_is_constraint e then
        match check_assert ask d e no_ov with
        | `True -> ID.of_bool ik true
        | `False -> ID.of_bool ik false
        | `Top -> ID.top_of ik
      else
        (*TODO we could also provide information for non-linear expressions*)
        match Convert.texpr1_of_cil_exp ask d (env d) e no_ov with
        | texpr1 ->
          let (i, c) = eval_texpr d (Texpr1.to_expr texpr1) in
          let c =  match c with 
            | None -> ID.bot_of ik
            | Some c -> ID.of_congruence ik c
          in let i = match i with
              | None -> ID.bot_of ik
              | Some (TopIntOps.Int l, TopIntOps.Int u) -> ID.of_interval ik (l,u)
              | Some (TopIntOps.Int l, _) -> ID.starting ik l
              | Some (_, TopIntOps.Int u) -> ID.ending ik u
              | _ -> ID.top_of ik
          in ID.meet c i
        | exception Convert.Unsupported_CilExp _ -> ID.top_of ik

end