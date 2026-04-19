import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.MetaHalt_Predicate
import OperatorKO7.Meta.MetaHalt_Regress
import OperatorKO7.Meta.MetaHalt_Soundness
import OperatorKO7.Meta.MetaHalt_Fracture

/-!
# META-HALT Paper Interface

Paper-facing forwarding layer over the META-HALT modules. Provides
short-name aliases for the theorems cited in the operational-incompleteness
paper.

This module is intentionally thin. It imports everything it needs, rebinds
the theorems under paper-friendly names, and adds no new mathematical
content.
-/

namespace OperatorKO7.MetaHalt.PaperInterface

/-- Paper alias: META-HALT consumes signatures, not proofs. -/
abbrev meta_halt_consumes_signatures_not_proofs :=
  OperatorKO7.MetaHalt.Predicate.metaHalt_consumes_signatures_not_proofs

/-- Paper alias: regress termination under a finite catalog. -/
abbrev meta_halt_regress_terminates :=
  OperatorKO7.MetaHalt.Regress.supervisoryLoop_terminates_in_catalog_budget

/-- Paper alias: no C1/C2 from a known-blocked witness class. -/
abbrev no_c1_c2_from_blocked_class :=
  OperatorKO7.MetaHalt.Soundness.no_c1_c2_from_blocked_class

/-- Paper alias: below-threshold confinement licenses only lift or C3. -/
abbrev below_threshold_only_c3_or_lift :=
  OperatorKO7.MetaHalt.Soundness.below_threshold_only_c3_or_lift

/-- Paper alias: Proposition 5.33. -/
abbrev below_threshold_forces_metahalt :=
  OperatorKO7.MetaHalt.Soundness.below_threshold_forces_metahalt

/-- Paper alias: no C4 verdict above a nonzero exhaustion gap. -/
abbrev no_c4_above_nonzero_gap :=
  OperatorKO7.MetaHalt.Fracture.no_c4_above_nonzero_gap

/-- Paper alias: budgeted catalog exhaustion gap. -/
abbrev catalog_exhaustion_gap :=
  OperatorKO7.MetaHalt.Fracture.catalogExhaustionGap

/-- Paper alias: valid T4 typed abstention requires full below-threshold
catalog exhaustion. -/
abbrev t4_requires_exhaustion_work :=
  OperatorKO7.MetaHalt.Fracture.t4_requires_exhaustion_work

/-- Paper alias: primitive-recursor exhaustion-gap lower bound. -/
abbrev exhaustion_gap_recursor :=
  OperatorKO7.MetaHalt.Fracture.exhaustion_gap_recursor

/-- Paper alias: primitive-recursor PRT supervisory lower bound. -/
abbrev exhaustion_gap_prt_lower_bound :=
  OperatorKO7.MetaHalt.Fracture.exhaustion_gap_prt_lower_bound

/-- Paper alias: Pre-Undecidability Fracture Theorem. -/
abbrev pre_undecidability_fracture :=
  OperatorKO7.MetaHalt.Fracture.pre_undecidability_fracture

/-- Paper alias: fault-line-complete architecture witness-transition layer
    necessity. -/
abbrev fault_line_complete_architecture_necessary_layers_witness_transition :=
  OperatorKO7.MetaHalt.Fracture.flc_layers_necessary_witness_transition

/-- Paper alias: fault-line-complete architecture META-HALT layer necessity. -/
abbrev fault_line_complete_architecture_necessary_layers_meta_halt :=
  OperatorKO7.MetaHalt.Fracture.flc_layers_necessary_meta_halt

end OperatorKO7.MetaHalt.PaperInterface
