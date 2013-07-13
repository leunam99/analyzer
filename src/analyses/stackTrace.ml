(** Stack-trace "analyses". *)

open Cil
open Pretty
open Analyses
module LF = LibraryFunctions

module Spec (D: StackDomain.S)=
struct
  include Analyses.DefaultSpec2

  let name = "stack trace"
  module D = D
  module C = D
  module G = Lattice.Unit
  
  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    ctx.local2
   
  let branch ctx (exp:exp) (tv:bool) : D.t = 
    ctx.local2
  
  let body ctx (f:fundec) : D.t = 
    if f.svar.vname = "goblin_initfun" then ctx.local2 else D.push f.svar ctx.local2

  let return ctx (exp:exp option) (f:fundec) : D.t = 
    ctx.local2
  
  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local2,ctx.local2]
  
  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:D.t) : D.t =
    ctx.local2
  
  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local2

  let startstate v = D.bot ()
  let otherstate v = D.bot ()
  let exitstate  v = D.top ()
end

module SpecLoc =
struct
  include Analyses.DefaultSpec2

  let name = "stack trace"
  module D = StackDomain.Dom3
  module C = StackDomain.Dom3
  module G = Lattice.Unit
  
  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    ctx.local2
   
  let branch ctx (exp:exp) (tv:bool) : D.t = 
    ctx.local2
  
  let body ctx (f:fundec) : D.t = 
    ctx.local2

  let return ctx (exp:exp option) (f:fundec) : D.t = 
    ctx.local2
  
  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    [ctx.local2, D.push !Tracing.current_loc ctx.local2]
  
  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:D.t) : D.t =
    ctx.local2
  
  let query_lv ask exp = 
    match ask (Queries.MayPointTo exp) with
      | `LvalSet l when not (Queries.LS.is_top l) -> 
          Queries.LS.elements l
      | _ -> []

  let fork ctx lv f args = 
    match LF.classify f.vname args with 
      | `ThreadCreate (start,ptc_arg) -> 
          let nst = D.push !Tracing.current_loc ctx.local2 in
            List.map (fun (v,_) -> (v,nst)) (query_lv ctx.ask2 start)
      | _ ->  []

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    let forks = fork ctx lval f arglist in
    let spawn (x,y) = ctx.spawn2 x y in 
    let _ = List.iter spawn forks in 
      ctx.local2


  let startstate v = D.bot ()
  let otherstate v = D.bot ()
  let exitstate  v = D.top ()
end


module Spec1 = Spec (StackDomain.Dom)
module Spec2 = Spec (StackDomain.Dom2)
let _ = 
  MCP.register_analysis "stack_loc" (module SpecLoc : Spec2);        
  MCP.register_analysis "stack_trace" (module Spec1 : Spec2);        
  MCP.register_analysis "stack_trace_set" (module Spec2 : Spec2)         
