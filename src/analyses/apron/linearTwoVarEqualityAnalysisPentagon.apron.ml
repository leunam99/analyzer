(** {{!RelationAnalysis} Relational integer value analysis} using an OCaml implementation of the linear two-variable equalities domain ([lin2vareq]).

    @see <http://doi.acm.org/10.1145/2049706.2049710> A. Flexeder, M. Petter, and H. Seidl Fast Interprocedural Linear Two-Variable Equalities. *)

open Analyses
include RelationAnalysis

module NoIneq = LinearTwoVarEqualityDomainPentagon.D2(RepresentantDomains.NoInequalties)
module PentagonIneq = LinearTwoVarEqualityDomainPentagon.D2(RepresentantDomains.InequalityFunctor(RepresentantDomains.PentagonCoeffs))
module PentagonOffsetIneq = LinearTwoVarEqualityDomainPentagon.D2(RepresentantDomains.InequalityFunctor(RepresentantDomains.PentagonOffsetCoeffs))
module FullIneq = LinearTwoVarEqualityDomainPentagon.D2(RepresentantDomains.InequalityFunctor(RepresentantDomains.TwoVarInequalitySet))

let spec_module: (module MCPSpec) Lazy.t =
  lazy (
    let (module AD) = match GobConfig.get_string "ana.lin2vareq_p.inequalities" with 
      | "none" -> (module NoIneq : RelationDomain.RD)
      | "pentagon" -> (module PentagonIneq : RelationDomain.RD)
      | "pentagon_offset" -> (module PentagonOffsetIneq : RelationDomain.RD)
      | _ ->  (module FullIneq : RelationDomain.RD) (*Other options differ only in the limit function*)
    in
    let module Priv = (val RelationPriv.get_priv ()) in
    let module Spec =
    struct
      include SpecFunctor (Priv) (AD) (RelationPrecCompareUtil.DummyUtil)
      let name () = "lin2vareq_p"
    end
    in
    (module Spec)
  )

let get_spec (): (module MCPSpec) =
  Lazy.force spec_module

let after_config () =
  let module Spec = (val get_spec ()) in
  MCP.register_analysis (module Spec : MCPSpec);
  GobConfig.set_string "ana.path_sens[+]"  (Spec.name ())

let _ =
  AfterConfig.register after_config
