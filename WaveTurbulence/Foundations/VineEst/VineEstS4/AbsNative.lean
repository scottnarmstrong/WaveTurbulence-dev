/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeInputSummability
public import WaveTurbulence.Foundations.RegularAsymptotics.PairedTreeContinuity

/-! # Uniform and `ℓ¹` bounds for one native starred kernel (V5 Step 4b, absolute convergence)

For one layered garden `LG` and the input coset `base`, the majorant sum
`M(x) = ∑'_ρ inputLeafMajorant(base + x/L, ρ)` over the relative decorations `ρ` of the attachment coset `base + x/L` is
(a) bounded uniformly in `x` by `∏_ℓ ∑'_n |F_ℓ(base + n/L)|` (`majSum_le`), and
(b) for a plain garden, summable in `x` (`summable_majSum`): `(x, ρ) ↦ (x + ρ_ℓ)_{ℓ input}` is injective.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed MeasureTheory Finset
open scoped Classical

theorem norm_zeta_le_one {w : ℕ} (G : Garden w) : ‖G.zeta‖ ≤ 1 := by
  unfold Garden.zeta
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun b _ => ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or (G.sign b.toNode) with h | h <;> simp [h]

/-- `∑' z, ∏ f i (z i) ≤ ∏ ∑' f i` for nonnegative summable families. -/
theorem tsum_pi_prod_le {ι β : Type*} [Fintype ι] (f : ι → β → ℝ) (hf0 : ∀ i b, 0 ≤ f i b)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun z : ι → β => ∏ i, f i (z i)) ∧ ∑' z : ι → β, ∏ i, f i (z i) ≤ ∏ i, ∑' b, f i b := by
  have hs := summable_pi_prod f hf0 hf
  refine ⟨hs, hs.tsum_le_of_sum_le fun u => ?_⟩
  calc ∑ z ∈ u, ∏ i, f i (z i)
      ≤ ∑ z ∈ Fintype.piFinset (fun i => u.image fun z => z i), ∏ i, f i (z i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
          fun z _ _ => Finset.prod_nonneg fun i _ => hf0 i (z i)
        rw [Fintype.mem_piFinset]
        exact fun i => Finset.mem_image_of_mem _ hz
    _ = ∏ i, ∑ b ∈ u.image (fun z => z i), f i b := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' b, f i b := Finset.prod_le_prod₀
        (fun i _ => Finset.sum_nonneg fun b _ => hf0 i b)
        fun i _ => (hf i).sum_le_tsum _ fun b _ => hf0 i b

section Kernel
variable {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)

/-- `‖K‖ ≤ |coupling|^n · ∑' majorant`, uniformly in the time parameters. -/
theorem norm_kernelK_le (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    ‖kernelK L γ δ F LG up s k₀ nroot nfl‖ ≤
      |coupling d L γ δ| ^ LG.garden.order *
        ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ := by
  have hm := summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF
  unfold kernelK
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hz := norm_zeta_le_one LG.garden
  have hb : ‖∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)‖ ≤
      ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ := by
    have hn : Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
        ‖(epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden,
            (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun κ => norm_kernel_summand_le_inputLeafMajorant L γ δ F LG up s k₀ κ) hm
    exact (norm_tsum_le_tsum_norm hn).trans
      (hn.tsum_le_tsum (fun κ => norm_kernel_summand_le_inputLeafMajorant L γ δ F LG up s k₀ κ) hm)
  have hc : 0 ≤ |coupling d L γ δ| ^ LG.garden.order := by positivity
  calc |coupling d L γ δ| ^ LG.garden.order * ‖LG.garden.zeta‖ * ‖∑' κ : GenDecoration LG.garden d nroot nfl, _‖
      ≤ |coupling d L γ δ| ^ LG.garden.order * 1 * ∑' κ : GenDecoration LG.garden d nroot nfl,
          inputLeafMajorant L F LG k₀ κ := by
        gcongr
    _ = _ := by rw [mul_one]

end Kernel

section Majorant
variable {w d : ℕ} (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (base : Mom d)

/-- The input leaves of `LG`, as a type. -/
abbrev InLeaf := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}

/-- The sum of the input majorants over the relative decorations at the attachment label `x`. -/
@[expose] noncomputable def majSum (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (x : Fin d → ℤ) : ℝ :=
  ∑' ρ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG (base + latticePoint L x) ρ

/-- The input factor of leaf `ℓ` at the integer label `n`. -/
@[expose] noncomputable def inFac (ℓ : InLeaf LG) (n : Fin d → ℤ) : ℝ :=
  |F (LG.layer ℓ.1.toNode) (base + latticePoint L n)|

theorem majorant_shift (x : Fin d → ℤ) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (ρ : GenDecoration LG.garden d nroot nfl) :
    inputLeafMajorant L F LG (base + latticePoint L x) ρ =
      ∏ ℓ : InLeaf LG, inFac L F LG base ℓ (x + ρ.1 ℓ.1.toNode) := by
  unfold inputLeafMajorant inFac
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  simp only [cosetDecoration, latticePoint_add, add_assoc]

theorem inFac_summable (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (base + latticePoint L n)|) (ℓ : InLeaf LG) :
    Summable (inFac L F LG base ℓ) := hF ℓ.1 ℓ.2

theorem shift_injective (x : Fin d → ℤ) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) :
    Function.Injective (fun (ρ : GenDecoration LG.garden d nroot nfl) (ℓ : InLeaf LG) => x + ρ.1 ℓ.1.toNode) := by
  intro ρ ρ' h
  refine genDecoration_input_injective LG nroot nfl hlone ?_
  funext ℓ
  exact add_left_cancel (congrFun h ℓ)

/-- **Uniform bound** of the majorant sum in the attachment label. -/
theorem majSum_le (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (base + latticePoint L n)|)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (x : Fin d → ℤ) :
    majSum L F LG base nroot nfl x ≤ ∏ ℓ : InLeaf LG, ∑' n, inFac L F LG base ℓ n := by
  obtain ⟨hs, hle⟩ := tsum_pi_prod_le (fun (ℓ : InLeaf LG) n => inFac L F LG base ℓ n)
    (fun ℓ n => abs_nonneg _) (inFac_summable L F LG base hF)
  have h0 : ∀ y : InLeaf LG → (Fin d → ℤ), 0 ≤ ∏ ℓ : InLeaf LG, inFac L F LG base ℓ (y ℓ) :=
    fun y => Finset.prod_nonneg fun ℓ _ => abs_nonneg _
  unfold majSum
  simp_rw [majorant_shift L F LG base x]
  exact (tsum_comp_le_tsum_of_inj hs h0 (shift_injective LG x hlone)).trans hle

end Majorant

section Joint
variable {w d : ℕ} (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (base : Mom d)

/-- In a plain garden, the integer label `x` of the attachment and the relative decoration are jointly determined by the
input-leaf labels `x + ρ_ℓ` (the root label `x` is the alternating sum of the leaf labels). -/
theorem joint_injective (hG : LG.garden.IsPlain) (j0 : Fin w) :
    Function.Injective (fun (p : Σ _ : Fin d → ℤ, GenDecoration LG.garden d (fun _ => 0) 0) (ℓ : InLeaf LG) =>
      p.1 + p.2.1 ℓ.1.toNode) := by
  rintro ⟨x, ρ⟩ ⟨x', ρ'⟩ h
  let δ : GNode LG.garden.tree → (Fin d → ℤ) := fun a => (x + ρ.1 a) - (x' + ρ'.1 a)
  have hδb : ∀ b : GBranch LG.garden.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2) := by
    intro b
    simp only [δ, ρ.2.1.1 b, ρ'.2.1.1 b]
    abel
  have hin : ∀ ℓ ∈ inputLeaves LG.garden, δ ℓ.toNode = 0 := fun ℓ hℓ => by
    have := congrFun h ⟨ℓ, hℓ⟩
    simp only [δ]
    exact sub_eq_zero.mpr this
  have hleaf : ∀ ℓ : GLeaf LG.garden.tree, δ ℓ.toNode = 0 := by
    intro ℓ
    have hm : LG.garden.mark ℓ = none := hG ℓ
    by_cases hs : LG.garden.sign ℓ.toNode = 1
    · exact hin ℓ (by simp [inputLeaves, hs, hm])
    · have hne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
      have hs' : LG.garden.sign ℓ.toNode = -1 := by
        rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with h | h
        · exact absurd h hs
        · exact h
      have hpm : LG.garden.mark (LG.garden.pair ℓ) = none := hG _
      have hps : LG.garden.sign (LG.garden.pair ℓ).toNode = 1 := by
        have := LG.garden.pair_sign ℓ hne
        change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = -nodeSign LG.garden.sig ℓ.1 at this
        change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
        rw [this]
        change -LG.garden.sign ℓ.toNode = 1
        rw [hs']
        rfl
      have h0 := hin (LG.garden.pair ℓ) (by simp [inputLeaves, hps, hpm])
      simp only [δ] at h0 ⊢
      rw [ρ.2.1.2 ℓ, ρ'.2.1.2 ℓ]
      exact h0
  have hr := eq_zero_of_leaves_zero δ hδb (GNode.root LG.garden.tree j0) (fun ℓ _ => hleaf ℓ)
  have hx : x = x' := by
    simp only [δ, ρ.2.2.1 j0, ρ'.2.2.1 j0, add_zero] at hr
    exact sub_eq_zero.mp hr
  subst hx
  have hρ : ρ = ρ' := shift_injective LG x (lone_count_le_one_of_plain _ hG) (by
    funext ℓ
    exact congrFun h ℓ)
  rw [hρ]

/-- For a plain garden, the majorant sum is summable in the attachment label. -/
theorem summable_majSum (hG : LG.garden.IsPlain) (j0 : Fin w)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (base + latticePoint L n)|) :
    Summable (majSum L F LG base (fun _ => 0) 0) := by
  obtain ⟨hs, _⟩ := tsum_pi_prod_le (fun (ℓ : InLeaf LG) n => inFac L F LG base ℓ n)
    (fun ℓ n => abs_nonneg _) (inFac_summable L F LG base hF)
  have h1 := hs.comp_injective (joint_injective LG hG j0)
  have h2 : Summable (fun p : Σ _ : Fin d → ℤ, GenDecoration LG.garden d (fun _ => 0) 0 =>
      inputLeafMajorant L F LG (base + latticePoint L p.1) p.2) := by
    refine h1.congr fun p => ?_
    simp only [Function.comp, majorant_shift L F LG base p.1 p.2]
  exact h2.sigma

end Joint

end WaveTurbulence.VineEstS4
