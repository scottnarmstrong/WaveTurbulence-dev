/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Vocab
public import WaveTurbulence.Foundations.RegularAsymptotics.PairedTreeContinuity

/-! # V5W-B (ruling F2): the analytic API of the top-weighted rows, copied by source

Verbatim copy (statements, proofs and namespace `WaveTurbulence.Flower.V5W` unchanged) of V5W-0's
`Flower/V5W/Analytic.lean` (sha256 `193b8feb47ea998fe83647fd0b2c4f77fe4f26ba3050db1df806cd324306e93f`, lines 7–200),
so that the selected rows of the V5 tower can use it; only the imports differ (the vocabulary from
`VineEst/RowSel/Vocab` in place of the world's `Flower/V5W/Defs` and `Flower/Stage1W/TypeBound`, which these
lemmas do not otherwise use).  V5W-0's module docstring follows.
  V5W-0, row 0a: the analytic API of the incoherent rows `coupleLeavesTop` / `treeLeavesTop`

The incoherent rows of the pinned kernel carry their own top weight `rowTopWeight p g LG qr`, a product of
`topPsi p g` factors, inside the decoration sum of `kernelLeavesW` at the layer profiles.

* `norm_topPsi_le`, `norm_rowTopWeight_le`: `|g| ≤ cψ`, `1 ≤ cψ` give `|rowTopWeight| ≤ cψ ^ #nodes` (so a
  `GPresented (32d)` weight of mass `cψ ≥ 1` gives it, `Stage1W.GPresented.norm_le`).
* `norm_kernelLeavesW_summand_le`: the decoration summand at the layer profiles is dominated by the bound of the
  multiplier times main's uniform summable majorant `inputLeafMajorant` (independent of all times).
* `continuous_kernelLeavesW_layer`, `continuous_coupleLeavesTop_time`, `continuous_treeLeavesTop_time`: time
  continuity on the whole time plane (copies of main's `continuous_kernelK_time`, `continuous_KQstar_time`,
  `continuous_KTstar_time`, with the bounded multiplier inside the decoration sum).
* `norm_coupleLeavesTop_le`, `norm_treeLeavesTop_le`: the uniform majorant (bound independent of the times).
* `coupleLeavesTop_one`, `treeLeavesTop_one`: at `g ≡ 1` the incoherent rows are main's `KQstar`/`KTstar` (the bridge
  of the `g ≡ 1` reduction, through `kernelLeaves_layerProfiles`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W MeasureTheory Finset

section Bounds
variable {d : ℕ}

theorem norm_topPsi_le (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (q q' : ℕ)
    (k : Mom d) : ‖topPsi p g q q' k‖ ≤ cψ := by
  unfold topPsi
  split_ifs
  · exact hg k
  · simpa using hc

theorem norm_rowTopWeight_le {w : ℕ} (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (LG : LayeredGarden w) (qr : Fin w → ℕ) (k : GNode LG.garden.tree → Mom d) :
    ‖rowTopWeight p g LG qr k‖ ≤ cψ ^ Fintype.card (GNode LG.garden.tree) := by
  unfold rowTopWeight
  rw [norm_prod]
  calc ∏ a : GNode LG.garden.tree, ‖topPsi p g (LG.layer a) (rowParentLayer LG qr a) (k a)‖
      ≤ ∏ _a : GNode LG.garden.tree, cψ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => norm_topPsi_le p g cψ hc hg _ _ _)
    _ = cψ ^ Fintype.card (GNode LG.garden.tree) := by rw [Finset.prod_const, Finset.card_univ]

/-- The decoration summand of `kernelLeavesW` at the layer profiles is dominated by the bound of the multiplier times
main's uniform majorant. -/
theorem norm_kernelLeavesW_summand_le {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ k, ‖m k‖ ≤ C)
    (κ : GenDecoration LG.garden d nroot nfl) :
    ‖m (cosetDecoration LG.garden L k₀ κ.1) *
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (layerProfiles LG F ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))‖ ≤
      C * inputLeafMajorant L F LG k₀ κ := by
  have hprod : ∏ ℓ ∈ inputLeaves LG.garden,
      (layerProfiles LG F ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) :=
    Finset.prod_congr rfl fun ℓ _ => by rw [layerProfiles_leaf]
  rw [hprod, norm_mul]
  exact mul_le_mul (hm _) (norm_kernel_summand_le_inputLeafMajorant L γ δ F LG up s k₀ κ) (norm_nonneg _)
    ((norm_nonneg _).trans (hm (cosetDecoration LG.garden L k₀ κ.1)))

end Bounds

section Continuity
variable {d : ℕ}

/-- **Time continuity of the weighted kernel at the layer profiles** (copy of main's `continuous_kernelK_time` with a
bounded multiplier). -/
theorem continuous_kernelLeavesW_layer {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ)
    (hm : ∀ k, ‖m k‖ ≤ C)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelLeavesW L γ δ LG (layerProfiles LG F) x.1 x.2 k₀ nroot nfl m) := by
  unfold kernelLeavesW
  apply Continuous.mul continuous_const
  apply continuous_tsum (u := fun κ => C * inputLeafMajorant L F LG k₀ κ)
  · intro κ
    exact continuous_const.mul ((continuous_const.mul
      (continuous_phaseIntegral_no_flower L γ δ LG hflower (cosetDecoration LG.garden L k₀ κ.1))).mul
        continuous_const)
  · exact (summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF).mul_left C
  · intro κ x
    exact norm_kernelLeavesW_summand_le L γ δ F LG x.1 x.2 k₀ m C hm κ

/-- **The incoherent couple row is continuous in its two clocks** on the whole time plane. -/
theorem continuous_coupleLeavesTop_time (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain) (k : Mom d) (cψ : ℝ) (hc : 1 ≤ cψ)
    (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => coupleLeavesTop L γ δ p g q q' LG (layerProfiles LG F) (ts 0) (ts 1) k) := by
  have hc' := continuous_kernelLeavesW_layer L γ δ F LG k (fun _ => 0) 0 (rowTopWeight p g LG ![q, q'])
    (cψ ^ Fintype.card (GNode LG.garden.tree)) (fun k => norm_rowTopWeight_le p g cψ hc hg LG ![q, q'] k)
    (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
  have hu : Continuous u := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases h : b.1.1 = 0
    · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelLeavesW L γ δ LG (layerProfiles LG F) x.1 x.2 k (fun _ => 0) 0 (rowTopWeight p g LG ![q, q'])) ∘ u)
  exact hc'.comp hu

/-- **The incoherent tree row is continuous in its two clocks** on the whole time plane. -/
theorem continuous_treeLeavesTop_time (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden) (k : Mom d) (cψ : ℝ) (hc : 1 ≤ cψ)
    (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => treeLeavesTop L γ δ p g q LG (layerProfiles LG F) (ts 0) (ts 1) k) := by
  have hc' := continuous_kernelLeavesW_layer L γ δ F LG k (fun _ => 0) 0 (rowTopWeight p g LG ![q])
    (cψ ^ Fintype.card (GNode LG.garden.tree)) (fun k => norm_rowTopWeight_le p g cψ hc hg LG ![q] k)
    (no_flowerParent_of_pairedTree LG.garden hT)
    (card_lone_le_one (fun _ _ h h' => hT.eq_of_isLone h h')) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun _ => ts 0), ts 1)
  have hu : Continuous u := by fun_prop
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelLeavesW L γ δ LG (layerProfiles LG F) x.1 x.2 k (fun _ => 0) 0 (rowTopWeight p g LG ![q])) ∘ u)
  exact hc'.comp hu

end Continuity

section Majorant
variable {d : ℕ}

/-- **The uniform majorant of the weighted kernel at the layer profiles** (independent of all times). -/
theorem norm_kernelLeavesW_layer_le {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ k, ‖m k‖ ≤ C)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    ‖kernelLeavesW L γ δ LG (layerProfiles LG F) up s k₀ nroot nfl m‖ ≤
      ‖(coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta‖ *
        ∑' κ : GenDecoration LG.garden d nroot nfl, C * inputLeafMajorant L F LG k₀ κ := by
  unfold kernelLeavesW
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hs := (summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF).mul_left C
  have hb := fun κ => norm_kernelLeavesW_summand_le L γ δ F LG up s k₀ m C hm (nroot := nroot) (nfl := nfl) κ
  have hsn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hb hs)

end Majorant

section Bridge
variable {d : ℕ}

end Bridge

end WaveTurbulence.Flower.V5W
