/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSingularCellExpansion

/-! # Absolute output-cell Fubini for the actual source singular leading term -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Incoh WithLp Finset

/-- Uniform cell bounds give a geometric bound on the literal output product. -/
theorem norm_leafSingularCellOp_le {d n m : ℕ} (J : Finset (Fin n)) {Mcell : ℝ}
    (hb : ∀ (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ Mcell)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S) (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
    ‖leafSingularCellOp J S i τ‖ ≤ Mcell^n := by
  rw [leafSingularCellOp,norm_prod]
  calc
    _ ≤ ∏ _j : Fin n, Mcell := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb j _ _ _ _)
    _ = _ := by simp

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
  {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length) {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ}
  (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
  (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
  (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
    Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
  (J : Finset (Fin Q.links.length)) {Mcell : ℝ}
  (hb : ∀ (j : Fin Q.links.length) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ Mcell)

include hd hn hK hM hB hF hb

/-- Output cells preserve the actual joint absolute integrability. -/
theorem integrable_leafMaskedSingularCoefficient_mul_cellOp (k : Mom d)
    (i : LeafSingularCellIndex S) :
    Integrable (fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellOp J S i uv.2) := by
  have hbase : StronglyMeasurable (fun τ : (Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d) =>
      leafSingularCellOp J S i τ) := stronglyMeasurable_cellOp_array hd J i.2.2.val
  have hm : StronglyMeasurable (fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      leafSingularCellOp J S i uv.2) := hbase.comp_measurable measurable_snd
  exact (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k i).mul_bdd
    (c := Mcell^Q.links.length) hm.aestronglyMeasurable
      (ae_of_all _ (fun uv => norm_leafSingularCellOp_le J hb S i uv.2))

/-- The original absolute coefficient mass controls all output cell integrals. -/
theorem summable_leafSingularCellOutput_terms {C : ℝ}
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) (k : Mom d) :
    Summable (fun i : LeafSingularCellIndex S =>
      ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
        leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellOp J S i uv.2) := by
  apply Summable.of_norm_bounded
    ((summable_integral_norm_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S hS k).mul_left
      (Mcell^Q.links.length))
  intro i
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
    ((integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k i).norm.const_mul _)
  apply ae_of_all
  intro uv
  dsimp only
  rw [norm_mul,mul_comm (Mcell^Q.links.length)]
  exact mul_le_mul_of_nonneg_left (norm_leafSingularCellOp_le J hb S i uv.2) (norm_nonneg _)

/-- The original spectral integral of each masked localized source cell
is an absolutely convergent finite sum of ordinary joint Fourier integrals. -/
theorem leaf_leading_spectrum_eq_cell_ops (k : Mom d)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (z : S c)
    :
    (∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      sourceRootMask c k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) * leafSpectrumCoefficient F c α *
          singInt J (halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2))) =
    ∑ pq : halfCellOrdinaryCells z.val,
      ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
        leafMaskedSingularCoefficient hQ hG F S k ⟨c,⟨z,pq⟩⟩ uv *
          leafSingularCellOp J S ⟨c,⟨z,pq⟩⟩ uv.2 := by
  classical
  have := isFiniteMeasureOnCompacts_pairs (n := Q.links.length) (d := d)
  have he := integral_fintype_integral_eq_tsum_integral_prod volume volume
    (fun pq : halfCellOrdinaryCells z.val =>
      fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
        leafMaskedSingularCoefficient hQ hG F S k ⟨c,⟨z,pq⟩⟩ uv *
          leafSingularCellOp J S ⟨c,⟨z,pq⟩⟩ uv.2)
    (fun pq => integrable_leafMaskedSingularCoefficient_mul_cellOp hQ hG hd hn hK hM hB hF S J hb k ⟨c,⟨z,pq⟩⟩)
  rw [tsum_fintype] at he
  apply Eq.trans ?_ he
  apply integral_congr_ae
  apply ae_of_all
  intro α
  dsimp only
  let a : ℂ := sourceRootMask c k *
    ((Real.fourierChar (inner ℝ (∑ j, toLp 2 (α j)) k):ℂ)*leafSpectrumCoefficient F c α)
  let f := fun pq : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ) =>
    ∫ τ : (Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d),
      a*fourierW (halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2) τ.1 τ.2 *
        ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)
  calc
    _ = a*singInt J (halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2) := by
      dsimp only [a]
      ring
    _ = ∑ pq ∈ halfCellOrdinaryCells z.val, f pq := by
      rw [singInt_halfCellAmplitude_eq hd hn,mul_sum]
      apply sum_congr rfl
      intro pq _
      dsimp only [f]
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro τ
      dsimp only
      ring
    _ = ∑ pq : halfCellOrdinaryCells z.val, f pq.val := (sum_coe_sort _ _).symm
    _ = _ := by
      apply sum_congr rfl
      intro pq _
      apply integral_congr_ae
      apply ae_of_all
      intro τ
      dsimp only [f,a,leafMaskedSingularCoefficient,leafSingularCellCoefficient,leafSingularCellOp]
      ring

end WaveTurbulence.RA1Leafwise
