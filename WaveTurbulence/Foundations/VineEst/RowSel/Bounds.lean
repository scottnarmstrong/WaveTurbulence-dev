/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Basic
public import WaveTurbulence.Foundations.VineEst.RowSel.Analytic
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsNative
public import WaveTurbulence.Foundations.Canon.Decomp
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.XChain.TreeLeafCard

/-! # V5W-B (ruling F2): the selected rows have the plain rows' majorant

The top weight `rowTopWeight p g LG qr` reads `g` only at the **top nodes** (layer `< p`, parent layer `= p`).  Layers
do not increase downwards, so below a top node every node has layer `< p` and parent layer `< p`: the top nodes form an
antichain (`rowTopNodes_antichain`), hence there are at most as many as leaves (`card_rowTopNodes_le`), i.e.
`2 n + w` for an object of order `n` with `w` roots.  With `‖g‖ ≤ cψ`, `1 ≤ cψ`:
`‖rowTopWeight‖ ≤ cψ ^ (2 n + w)` (`norm_rowTopWeight_le_leaves`).

So the normalization `cψ^{-(2n+2)}` (couples) / `cψ^{-(2n+1)}` (trees) of the incoherent selected rows makes them obey
**the same uniform majorant as `KQstar`/`KTstar`** (`norm_KQsel_le`, `norm_KTsel_le`, the bound of
`VineEstS4.norm_kernelK_le`), for every selector.  Time continuity and measurability of the selected rows
(`continuous_KQsel_time`, `measurable_KQsel_comp`, …) follow from main's and V5W-0's row continuity.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W MeasureTheory Finset

section TopCount
variable {w d : ℕ}

/-- The nodes at which `rowTopWeight p g LG qr` reads the weight `g`. -/
def rowTopNodes (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => LG.layer a < p ∧ rowParentLayer LG qr a = p

/-- A proper descendant of a node of layer `< p` has parent layer `< p`. -/
theorem rowParentLayer_lt_of_isDesc {p : ℕ} {LG : LayeredGarden w} {qr : Fin w → ℕ} {s s' : GNode LG.garden.tree}
    (h : s.IsDesc s') (hne : s ≠ s') (hs : LG.layer s < p) : rowParentLayer LG qr s' < p := by
  obtain ⟨hj, q, hq⟩ := h
  have hqne : q ≠ [] := by
    rintro rfl
    exact hne (Subtype.ext (Prod.ext hj (by simpa using hq)))
  have hroot : s'.1.2 ≠ [] := by
    rw [← hq]
    simp [hqne]
  unfold rowParentLayer LayeredGarden.parentLayer
  rw [if_neg hroot, if_neg hroot]
  generalize_proofs hmem
  have hd : s.IsDesc ⟨(s'.1.1, s'.1.2.dropLast), hmem⟩ := by
    refine ⟨hj, q.dropLast, ?_⟩
    show s.1.2 ++ q.dropLast = s'.1.2.dropLast
    rw [← hq, List.dropLast_append_of_ne_nil hqne]
  exact lt_of_le_of_lt (LayeredGarden.layer_le_of_isDesc LG hd) hs

/-- The top nodes form an antichain. -/
theorem rowTopNodes_antichain (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) :
    Canon.Rel.Antichain LG (rowTopNodes p LG qr) := by
  intro s hs s' hs' hne
  simp only [rowTopNodes, Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd hs'.2 (rowParentLayer_lt_of_isDesc h hne hs.1).ne
  · exact absurd hs.2 (rowParentLayer_lt_of_isDesc h (Ne.symm hne) hs'.1).ne

/-- There are at most as many top nodes as leaves. -/
theorem card_rowTopNodes_le (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) :
    (rowTopNodes p LG qr).card ≤ Fintype.card (GLeaf LG.garden.tree) := by
  classical
  have h1 := Canon.Rel.card_leavesBelowSet (rowTopNodes_antichain p LG qr)
  have h2 : (rowTopNodes p LG qr).card ≤ ∑ u ∈ rowTopNodes p LG qr, u.leavesBelow.card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun u _ => (Canon.odd_card_leavesBelow u).pos
  calc (rowTopNodes p LG qr).card ≤ _ := h2
    _ = _ := h1.symm
    _ ≤ _ := Finset.card_le_univ _

/-- The number of leaves of a garden of order `n` with `w` trees is `2 n + w`. -/
theorem card_gleaf_eq (G : Garden w) : Fintype.card (GLeaf G.tree) = 2 * G.order + w :=
  Induct.forest_card_leaves_eq G.tree

/-- **The top weight is bounded by `cψ` to the number of leaves.** -/
theorem norm_rowTopWeight_le_leaves (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (LG : LayeredGarden w) (qr : Fin w → ℕ) (k : GNode LG.garden.tree → Mom d) :
    ‖rowTopWeight p g LG qr k‖ ≤ cψ ^ (2 * LG.garden.order + w) := by
  classical
  rw [← card_gleaf_eq]
  unfold rowTopWeight
  rw [norm_prod]
  calc ∏ a : GNode LG.garden.tree, ‖topPsi p g (LG.layer a) (rowParentLayer LG qr a) (k a)‖
      ≤ ∏ a : GNode LG.garden.tree, (if a ∈ rowTopNodes p LG qr then cψ else 1) := by
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
        unfold topPsi
        by_cases h : LG.layer a < p ∧ rowParentLayer LG qr a = p
        · have ha : a ∈ rowTopNodes p LG qr := by simp [rowTopNodes, h]
          rw [if_pos h, if_pos ha]
          exact hg _
        · have ha : a ∉ rowTopNodes p LG qr := by simp [rowTopNodes, h]
          rw [if_neg h, if_neg ha, norm_one]
    _ = cψ ^ (rowTopNodes p LG qr).card := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    _ ≤ cψ ^ Fintype.card (GLeaf LG.garden.tree) := pow_le_pow_right₀ hc (card_rowTopNodes_le p LG qr)

theorem inputLeafMajorant_nonneg (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    0 ≤ inputLeafMajorant L F LG k₀ κ :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- The top-weighted kernel at the layer profiles is bounded by `cψ ^ (2 n + w)` times main's majorant. -/
theorem norm_kernelLeavesW_rowTop_le (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (qr : Fin w → ℕ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    ‖kernelLeavesW L γ δ LG (layerProfiles LG F) up s k₀ nroot nfl (rowTopWeight p g LG qr)‖ ≤
      cψ ^ (2 * LG.garden.order + w) * (|coupling d L γ δ| ^ LG.garden.order *
        ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ) := by
  have h := Flower.V5W.norm_kernelLeavesW_layer_le L γ δ F LG up s k₀ nroot nfl (rowTopWeight p g LG qr)
    (cψ ^ (2 * LG.garden.order + w)) (fun k => norm_rowTopWeight_le_leaves p g cψ hc hg LG qr k) hlone hF
  rw [tsum_mul_left] at h
  have hz : ‖(coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta‖ ≤ |coupling d L γ δ| ^ LG.garden.order := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (by positivity) (VineEstS4.norm_zeta_le_one LG.garden)
  have hS : 0 ≤ ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ :=
    tsum_nonneg fun κ => inputLeafMajorant_nonneg L F LG k₀ κ
  have hC : 0 ≤ cψ ^ (2 * LG.garden.order + w) := pow_nonneg (zero_le_one.trans hc) _
  calc _ ≤ _ := h
    _ ≤ |coupling d L γ δ| ^ LG.garden.order *
          (cψ ^ (2 * LG.garden.order + w) * ∑' κ : GenDecoration LG.garden d nroot nfl,
            inputLeafMajorant L F LG k₀ κ) := mul_le_mul_of_nonneg_right hz (mul_nonneg hC hS)
    _ = _ := by ring

end TopCount

private theorem norm_normalized_le {c B : ℝ} (hc : 1 ≤ c) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ c ^ n * B) :
    ‖(((c ^ n)⁻¹ : ℝ) : ℂ) * z‖ ≤ B := by
  have hpos : 0 < c ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hc) n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc (c ^ n)⁻¹ * ‖z‖ ≤ (c ^ n)⁻¹ * (c ^ n * B) := mul_le_mul_of_nonneg_left hz (inv_pos.mpr hpos).le
    _ = B := by field_simp

section Selected
variable {u : Unit} [S : RowSel u] {d : ℕ}

/-- **The selected couple row obeys `KQstar`'s majorant**, for every selector. -/
theorem norm_KQsel_le (incoh q q' : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ)
    (k : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    ‖KQsel incoh q q' L γ δ F LG t s k‖ ≤
      |coupling d L γ δ| ^ LG.garden.order *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, inputLeafMajorant L F LG k κ := by
  have hQ : ‖KQstar L γ δ F LG t s k‖ ≤ |coupling d L γ δ| ^ LG.garden.order *
      ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, inputLeafMajorant L F LG k κ :=
    VineEstS4.norm_kernelK_le L γ δ F LG _ _ _ _ _ hlone hF
  unfold KQsel
  cases S.weighted
  · exact hQ
  · simp only [cond_true]
    split_ifs
    · exact hQ
    · exact norm_normalized_le S.one_le_cψ _
        (norm_kernelLeavesW_rowTop_le L γ δ F LG _ 0 k (fun _ => 0) 0 S.p (S.g d) S.cψ S.one_le_cψ
          (S.norm_g_le d) ![q, q'] hlone hF)

/-- **The selected tree row obeys `KTstar`'s majorant**, for every selector. -/
theorem norm_KTsel_le (incoh q : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ)
    (k : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    ‖KTsel incoh q L γ δ F LG t s k‖ ≤
      |coupling d L γ δ| ^ LG.garden.order *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, inputLeafMajorant L F LG k κ := by
  have hT : ‖KTstar L γ δ F LG t s k‖ ≤ |coupling d L γ δ| ^ LG.garden.order *
      ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, inputLeafMajorant L F LG k κ :=
    VineEstS4.norm_kernelK_le L γ δ F LG _ _ _ _ _ hlone hF
  unfold KTsel
  cases S.weighted
  · exact hT
  · simp only [cond_true]
    split_ifs
    · exact hT
    · exact norm_normalized_le S.one_le_cψ _
        (norm_kernelLeavesW_rowTop_le L γ δ F LG _ s k (fun _ => 0) 0 S.p (S.g d) S.cψ S.one_le_cψ
          (S.norm_g_le d) ![q] hlone hF)

/-- The selected couple row is continuous in its two clocks. -/
theorem continuous_KQsel_time (incoh q q' : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (hplain : LG.garden.IsPlain) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => KQsel incoh q q' L γ δ F LG (ts 0) (ts 1) k) := by
  have hQ := continuous_KQstar_time L γ δ F LG hplain k hF
  unfold KQsel
  cases S.weighted
  · exact hQ
  · simp only [cond_true]
    split_ifs
    · exact hQ
    · exact continuous_const.mul (Flower.V5W.continuous_coupleLeavesTop_time L γ δ S.p (S.g d) q q' F LG hplain
        k S.cψ S.one_le_cψ (S.norm_g_le d) hF)

/-- The selected tree row is continuous in its two clocks. -/
theorem continuous_KTsel_time (incoh q : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)
    (hT : IsPairedTree LG.garden) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => KTsel incoh q L γ δ F LG (ts 0) (ts 1) k) := by
  have hc := continuous_KTstar_time L γ δ F LG hT k hF
  unfold KTsel
  cases S.weighted
  · exact hc
  · simp only [cond_true]
    split_ifs
    · exact hc
    · exact continuous_const.mul (Flower.V5W.continuous_treeLeavesTop_time L γ δ S.p (S.g d) q F LG hT
        k S.cψ S.one_le_cψ (S.norm_g_le d) hF)

theorem measurable_pair_rowSel {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun τ => (![f τ, g τ] : Fin 2 → ℝ)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · exact hf
  · exact hg

/-- The selected couple row is measurable along measurable clocks. -/
theorem measurable_KQsel_comp {α : Type*} [MeasurableSpace α] (incoh q q' : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|)
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun τ => KQsel incoh q q' L γ δ F LG (f τ) (g τ) k) := by
  have h1 := (continuous_KQsel_time incoh q q' L γ δ F LG hplain k hF).measurable.comp
    (measurable_pair_rowSel hf hg)
  exact h1

/-- The selected tree row is measurable along measurable clocks. -/
theorem measurable_KTsel_comp {α : Type*} [MeasurableSpace α] (incoh q : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|)
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun τ => KTsel incoh q L γ δ F LG (f τ) (g τ) k) := by
  have h1 := (continuous_KTsel_time incoh q L γ δ F LG hT k hF).measurable.comp
    (measurable_pair_rowSel hf hg)
  exact h1

end Selected

end WaveTurbulence.VineEst
