/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpectralCoefficient
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalRemainderJoint

/-! # The actual leaf-only spectral remainder density -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal

/-- The two link modulation arrays computed from the actual leaf rows. -/
def leafModulations {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    (Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d) :=
  ((fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0))),
    (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))))

theorem continuous_leafModulations {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (d : ℕ) :
    Continuous (leafModulations hQ hG (d := d)) := by
  have hc : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      fun a => toLp 2 (α a)) := by fun_prop
  exact (continuous_pi (fun j => (continuous_sourceFrequencyPullback hQ hG (some (j,0))).comp hc)).prodMk
    (continuous_pi (fun j => (continuous_sourceFrequencyPullback hQ hG (some (j,1))).comp hc))

end WaveTurbulence.RA1Leafwise
