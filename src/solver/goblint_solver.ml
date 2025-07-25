(** Generic solvers for {{!Goblint_constraint} (side-effecting) constraint systems}. *)

(** {1 Top-down}

    The top-down solver family. *)

module Td3 = Td3
module Td_simplified = Td_simplified
module Td_simplified_ref = Td_simplified_ref
module TopDown = TopDown
module TopDown_term = TopDown_term
module TopDown_space_cache_term = TopDown_space_cache_term
module TopDown_deprecated = TopDown_deprecated

(** {1 SLR}

    The SLR solver family. *)

module SLRphased = SLRphased
module SLRterm = SLRterm
module SLR = SLR

(** {1 Other} *)

module EffectWConEq = EffectWConEq
module Worklist = Worklist
module Generic = Generic
module Selector = Selector

module PostSolver = PostSolver
module LocalFixpoint = LocalFixpoint
module SolverStats = SolverStats
module SolverBox = SolverBox

module SideWPointSelect = SideWPointSelect
module Td3UpdateRule = Td3UpdateRule
