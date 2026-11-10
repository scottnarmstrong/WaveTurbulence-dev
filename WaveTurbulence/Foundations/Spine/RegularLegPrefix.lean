/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAllOrderRemainder
public import WaveTurbulence.Foundations.Spine.CoherentPrefixPreserving
public import WaveTurbulence.Foundations.Spine.IncoherentAllOrderBound
public import WaveTurbulence.Foundations.Spine.IncoherentPrefixPreserving
/-! The two actual regular-couple contributions, assembled while preserving other source inputs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

abbrev RegularAnalyticSourcesAt (P : WTParams) : Prop :=
  ((LeafwiseCoherentApproximationOrder0At P ∧ SourceCoherentTaylorAt P) ∧
    (TaylorBoundAt P ∧ LowProfileAt P)) ∧ LeafwiseIncoherentDecayAt P

theorem regular_analytic_sources_prefix
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate)
    (hDecay : LeafwiseIncoherentDecayGate) : WTPrefix RegularAnalyticSourcesAt :=
  prefix_and (coherent_source_prefix hLeaf hTaylor)
    (show WTPrefix LeafwiseIncoherentDecayAt from hDecay)
    ((leafwiseCoherentApproximation_largeConstantMonotone.and sourceCoherentTaylor_largeConstantMonotone).and
      (taylorBound_largeConstantMonotone.and lowProfile_largeConstantMonotone))
    leafwiseIncoherentDecay_largeConstantMonotone

/-- The arbitrary retained proposition A is carried by the existing source prefix;
no extra analytic hypothesis is introduced by this assembly. -/
theorem prefix_add_regular_comparisons {A : WTParams → Prop}
    (hsource : WTPrefix (fun P => A P ∧ RegularAnalyticSourcesAt P)) :
    WTPrefix (fun P => A P ∧ CoherentRemainderAt P ∧ IncoherentRemainderAt P) := by
  have hc₀ : WTPrefix (fun P => ((A P ∧ LeafwiseIncoherentDecayAt P) ∧ LowProfileAt P) ∧
      ((LeafwiseCoherentApproximationOrder0At P ∧ SourceCoherentTaylorAt P) ∧
        (TaylorBoundAt P ∧ LowProfileAt P))) :=
    prefix_map (fun P h => ⟨⟨⟨h.1, h.2.2⟩, h.2.1.2.2⟩, h.2.1⟩) hsource
  have hc := prefix_add_coherent_comparison hc₀
  have hi₀ : WTPrefix (fun P => (A P ∧ CoherentEvenComparisonAt P) ∧
      (LeafwiseIncoherentDecayAt P ∧ LowProfileAt P)) :=
    prefix_map (fun P h => ⟨⟨h.1.1.1, h.2⟩, h.1.1.2, h.1.2⟩) hc
  have hi := prefix_add_incoherent_comparison hi₀
  exact prefix_map (fun P h => ⟨h.1.1.1,
      coherent_remainder_of_even_comparison P h.1.1.2 h.2,
      incoherent_remainder_of_even_comparison P h.1.2 h.2⟩)
    (prefix_with_coherent_small_parameters hi)

end WaveTurbulence.LGSpine
