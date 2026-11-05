/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSingularCellFactors
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ActualLeafSpectralCells
public import WaveTurbulence.Foundations.RegAsymp.FiniteCellSingularFubini

/-! # Ordinary-cell Fubini for the original masked leaf spectral expansion -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Incoh WithLp Finset

/-- Unfold the actual countable index into its original leaf centers and
both finite covers, under the proved absolute summability hypothesis. -/
theorem tsum_leafSingularCellIndex {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {f : LeafSingularCellIndex S → ℂ} (hf : Summable f) :
    (∑' i, f i) = ∑' c : Fin m → Fin d → ℤ,
      ∑ z : S c, ∑ pq : halfCellOrdinaryCells z.val, f ⟨c,⟨z,pq⟩⟩ := by
  rw [hf.tsum_sigma]
  apply tsum_congr
  intro c
  rw [(hf.sigma_factor c).tsum_sigma]
  simp only [tsum_fintype]

variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
  {d K M : ℕ} (hn : 0 < Q.links.length) {F : Mom d → ℂ} {B : ℝ}
  (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
  (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
  (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
    Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

include hn hK hM hB hF

/-- The physical cell factors preserve absolute coefficient integrability. -/
theorem integrable_leafMaskedSingularCoefficient_mul_cellFn (k : Mom d)
    (i : LeafSingularCellIndex S) (x y : Fin Q.links.length → Mom d) :
    Integrable (fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellFn S i uv.2 x y) := by
  have hm : StronglyMeasurable (fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      leafSingularCellFn S i uv.2 x y) :=
    (stronglyMeasurable_leafSingularCellFn S i x y).comp_measurable measurable_snd
  exact (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k i).mul_bdd
    (c := 1) hm.aestronglyMeasurable (ae_of_all _ (fun uv => norm_leafSingularCellFn_le_one S i uv.2 x y))

/-- Original coefficient summability controls the actual complex cell
integrals at every physical point, before any singular integration. -/
theorem summable_leafSingularCellKernel_terms {C : ℝ}
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length)
    (k : Mom d) (x y : Fin Q.links.length → Mom d) :
    Summable (fun i : LeafSingularCellIndex S =>
      ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
        leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellFn S i uv.2 x y) := by
  apply Summable.of_norm_bounded
    (summable_integral_norm_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S hS k)
  intro i
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
    (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k i).norm
  apply ae_of_all
  intro uv
  dsimp only
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_leafSingularCellFn_le_one S i uv.2 x y)
    (norm_nonneg _)).trans_eq (mul_one _)

/-- The original spectral integral of each masked localized source cell
is an absolutely convergent finite sum of ordinary joint Fourier integrals. -/
theorem leaf_spectrum_eq_ordinary_cell_integrals (k : Mom d)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (z : S c)
    (x y : Fin Q.links.length → Mom d) :
    (∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      sourceRootMask c k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) * leafSpectrumCoefficient F c α *
          halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 x y)) =
    ∑ pq : halfCellOrdinaryCells z.val,
      ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
        leafMaskedSingularCoefficient hQ hG F S k ⟨c,⟨z,pq⟩⟩ uv *
          leafSingularCellFn S ⟨c,⟨z,pq⟩⟩ uv.2 x y := by
  classical
  have := isFiniteMeasureOnCompacts_pairs (n := Q.links.length) (d := d)
  have he := integral_fintype_integral_eq_tsum_integral_prod volume volume
    (fun pq : halfCellOrdinaryCells z.val =>
      fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
        leafMaskedSingularCoefficient hQ hG F S k ⟨c,⟨z,pq⟩⟩ uv *
          leafSingularCellFn S ⟨c,⟨z,pq⟩⟩ uv.2 x y)
    (fun pq => integrable_leafMaskedSingularCoefficient_mul_cellFn hQ hG hn hK hM hB hF S k ⟨c,⟨z,pq⟩⟩ x y)
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
        ∏ j, cellFn (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) (x j) (y j)
  calc
    _ = a*halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 x y := by
      dsimp only [a]
      ring
    _ = ∑ pq ∈ halfCellOrdinaryCells z.val, f pq := by
      rw [halfCellAmplitude_eq_sum_cellFn hn,mul_sum]
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
      dsimp only [f,a,leafMaskedSingularCoefficient,leafSingularCellCoefficient,leafSingularCellFn]
      ring

end WaveTurbulence.RegAsymp
