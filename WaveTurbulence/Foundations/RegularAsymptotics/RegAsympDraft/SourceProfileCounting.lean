/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceDensityIdentities
public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-! # Countable expansion of integrable original source profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- The same integral may be indexed directly by the original sigma type
of selected source cells. The embedding retains all integer centers. -/
theorem leafSpatial_integral_eq_sourceCellIndex {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (f : LeafSpatialSample d n m → ℂ)
    (hi : Integrable f (leafSpatialMeasure d n m))
    (hsupport : ∀ c z, z ∉ S c → ∀ α, f ((c,z),α) = 0) :
    (∫ p, f p ∂leafSpatialMeasure d n m) =
      ∑' u : SourceCellIndex S, ∫ α : Fin m → Fin d → ℝ, f ((u.1,u.2.val),α) := by
  classical
  unfold leafSpatialMeasure at hi ⊢
  rw [integral_prod _ hi]
  have hc := integral_countable hi.integral_prod_left
  simp only [Measure.real,Measure.count_singleton,ENNReal.toReal_one,one_smul] at hc
  rw [hc]
  let e : SourceCellIndex S → (Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ) :=
    fun u => (u.1,u.2.val)
  have he : Function.Injective e := by
    intro u v huv
    cases u with
    | mk c z =>
      cases v with
      | mk c' z' =>
        have hc' : c = c' := congrArg Prod.fst huv
        subst c'
        have hz : z = z' := Subtype.ext (congrArg Prod.snd huv)
        subst z'
        rfl
  exact (he.tsum_eq (by
    intro p hp
    by_cases hz : p.2 ∈ S p.1
    · exact ⟨⟨p.1,⟨p.2,hz⟩⟩,rfl⟩
    · exfalso
      exact hp (by simp only [hsupport p.1 p.2 hz,integral_zero]))).symm

end WaveTurbulence.RegAsymp
