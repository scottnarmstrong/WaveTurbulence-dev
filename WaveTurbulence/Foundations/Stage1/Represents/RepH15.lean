/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH14
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep2

/-!
# S2 REPRESENTS, VINE-D (15): the uniform bound of a spliced kernel under the amplitude bounds

`norm_splicedKernel_le`: `‖K_G(D)‖ ≤ ‖coupling^{|G|}‖ · ((⌊2L⌋+2)^d)^{#pairs}` for every data `D` satisfying
`SplicedAmplitudeBounds`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ}

theorem abs_splicedGapIndicator_le (G : Garden w) (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → Fin d → ℤ) : |splicedGapIndicator G D L γ η base z| ≤ 1 := by
  classical
  unfold splicedGapIndicator
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun v _ => ?_
  rcases D.gapSpecification v with _ | q
  · simp
  · simp only
    split_ifs <;> simp

theorem norm_splicedKernel_summand_le (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) :
    ‖(splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegral G D L γ δ base z.1‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 := AsmCtxH.norm_splicedEpsilon_le G D.hinges z.1
  have h2 := abs_splicedGapIndicator_le G D L γ η base z.1
  have h3 : ‖∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun x hx =>
      snorm_le_one_pointwise (30 * d) _ (hD.2.1 x hx).1 _
  have h4 := hD.2.2.1 (fun x => base + latticePoint L (bondIndex G z.1 x.1))
  have h5 := norm_splicedTimeIntegral_le G D L γ δ base z.1
  refine le_trans (b := 1 * 1 * 1 * 1 * 1) ?_ (by norm_num)
  gcongr

open scoped Classical in
theorem norm_splicedKernel_le (G : Garden w) (hS : G.IsPlain) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (L : ℝ) (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    ‖splicedKernel G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ) ^ G.order‖ * (((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair G) : ℕ) := by
  set c : ReplacementSlot G → Mom d := fun s => if h : hasBond hS s then D.center (dartOfSlot hS s h) else 0
  obtain ⟨hF, hC⟩ := decoration_count hS L hL base roots c
  set F := hF.toFinset
  set f : GenDecoration G d roots 0 → ℂ := fun z =>
    (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D L γ η base z.1 : ℂ) *
      (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
      D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
      splicedTimeIntegral G D L γ δ base z.1 with hf
  have hsupp : ∀ z ∉ F, f z = 0 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    simp only [Set.mem_setOf_eq, not_forall] at hz
    obtain ⟨s, hs, hfar⟩ := hz
    have hz' : ∀ ℓ : GLeaf G.tree, z.1 ℓ.toNode = z.1 (G.pair ℓ).toNode := z.2.1.2
    set x := dartOfSlot hS s hs
    have hxb : x ∈ G.molecule.bonds := by
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact out_dartOfSlot hS s hs
    have hk : bondIndex G z.1 x = z.1 (slotNode hS s) := by
      rw [bondIndex_eq_slotNode hS z.1 hz' x, slotOfDart_dartOfSlot]
    have hc : c s = D.center x := by
      show (if h : hasBond hS s then D.center (dartOfSlot hS s h) else 0) = _
      rw [dif_pos hs]
    have hedge : D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) = 0 := by
      refine (hD.2.1 x hxb).2 _ ?_
      rw [hk, ← hc]
      exact lt_of_not_ge hfar
    have hprod : ∏ y ∈ G.molecule.bonds, D.edgeAmplitude y (base + latticePoint L (bondIndex G z.1 y)) = 0 :=
      Finset.prod_eq_zero hxb hedge
    simp only [hf, hprod, mul_zero, zero_mul]
  have htsum : ∑' z, f z = ∑ z ∈ F, f z := tsum_eq_sum (fun z hz => hsupp z hz)
  unfold splicedKernel
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  change ‖∑' z, f z‖ ≤ _
  rw [htsum]
  calc ‖∑ z ∈ F, f z‖ ≤ ∑ z ∈ F, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ F, (1 : ℝ) := Finset.sum_le_sum fun z _ =>
        norm_splicedKernel_summand_le G D hD L γ η δ base roots z
    _ = F.card := by simp
    _ ≤ _ := by
        have : F.card = (hF.toFinset : Finset _).card := rfl
        rw [this, ← Set.ncard_eq_toFinset_card _ hF]
        exact_mod_cast hC

end WaveTurbulence.Represents
