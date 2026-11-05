/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceDensityIdentities
public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-! # Countable expansion of integrable original source profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- An integrable source sample function supported on the actual finite
link cover has precisely the original cell expansion. -/
theorem leafSpatial_integral_eq_cells {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (f : LeafSpatialSample d n m → ℂ)
    (hi : Integrable f (leafSpatialMeasure d n m))
    (hsupport : ∀ c z, z ∉ S c → ∀ α, f ((c,z),α) = 0) :
    (∫ p, f p ∂leafSpatialMeasure d n m) =
      ∑' c : Fin m → Fin d → ℤ, ∑ z ∈ S c,
        ∫ α : Fin m → Fin d → ℝ, f ((c,z),α) := by
  classical
  unfold leafSpatialMeasure at hi ⊢
  rw [integral_prod _ hi]
  have hc := integral_countable hi.integral_prod_left
  simp only [Measure.real,Measure.count_singleton,ENNReal.toReal_one,one_smul] at hc
  have hs := (integrable_count_iff.mp hi.integral_prod_left).of_norm
  rw [hc,hs.tsum_prod]
  apply tsum_congr
  intro c
  apply tsum_eq_sum
  intro z hz
  simp only [hsupport c z hz,integral_zero]

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

/-- Joint-L1 scalar source densities invert in time and expand on the
same actual countable cell cover. -/
theorem maskedLeafScalarProfile_eq_cells {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hi : Integrable (fun q => maskedLeafScalarDensity hQ hG R F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∫ p, maskedLeafScalarDensity hQ hG R F S (lam,p) k
      ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t =
    ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ, ∑ z ∈ S c,
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        pairedInverseProfile (fun lam => maskedLeafScalarDensity hQ hG R F S (lam,((c,z),α)) k) t := by
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  rw [pairedInverseProfile_integral_swap _ hi]
  apply leafSpatial_integral_eq_cells S _ (integrable_pairedInverseProfile_samples _ hi t)
  intro c z hz α
  simp only [pairedInverseProfile_maskedLeafScalarDensity,hz,ite_false]

end WaveTurbulence.RegAsymp
