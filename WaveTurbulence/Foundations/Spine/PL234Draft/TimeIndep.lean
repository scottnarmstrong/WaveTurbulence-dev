/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitTree

/-!
# Time arguments outside the layer windows

The kernels see their time arguments only through the time domain `kDomain`: a branching node of layer `r` has
its time in `(r, r+1)`, so an upper time `≥ r+1` and a lower lone-leaf time `≤ r` impose nothing.

* `kernelLeaves_congr_domain`: equal domains give equal leafwise kernels (no flower parents);
* `coupleLeaves_upper_eq`: the `+` time of a couple is irrelevant above the `+` tree's layers;
* `treeLeaves_upper_eq`, `treeLeaves_lower_eq`: the same for trees, and the lone-leaf time below the lone
  parent's layer;
* `LeafApp.tree_lower_eq`: the leading term of a tree code only sees `max(s, r)` (the B2 definition of
  `𝒥ℬ*_𝒯`, FINDINGS F66).
-/

@[expose] public section

open MeasureTheory Set Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {w d : ℕ}

theorem extendTime_congr_s {G : Garden w} (hfl : ∀ b, ¬ G.IsFlowerParent b) (s s' : ℝ)
    (τ : G.FreeBranch → ℝ) : G.extendTime s τ = G.extendTime s' τ := by
  funext b
  unfold Garden.extendTime
  rw [dite_eq_right_of_eq_false (eq_false (hfl b)), dite_eq_right_of_eq_false (eq_false (hfl b))]

/-- **Equal time domains give equal kernels** (no flower parents). -/
theorem kernelLeaves_congr_domain (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {up up' : GBranch LG.garden.tree → ℝ} {s s' : ℝ}
    (hD : kDomain LG up s = kDomain LG up' s') (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl = kernelLeaves L γ δ LG H up' s' k₀ nroot nfl := by
  unfold kernelLeaves
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  unfold phaseIntegral
  rw [hD]
  congr 1
  funext τ
  rw [extendTime_congr_s hfl s s' τ]

/-- **The `+` time of a couple above its `+` tree's layers.** -/
theorem coupleLeaves_upper_eq (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {t t' : ℝ} (s : ℝ) (k : Mom d)
    (ht : ∀ b : GBranch LG.garden.tree, b.1.1 = 0 → (LG.layer b.toNode : ℝ) + 1 ≤ t ∧
      (LG.layer b.toNode : ℝ) + 1 ≤ t') :
    coupleLeaves L γ δ LG H t s k = coupleLeaves L γ δ LG H t' s k := by
  unfold coupleLeaves
  refine kernelLeaves_congr_domain L γ δ LG H hfl ?_ k _ _
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  by_cases hb : b.1.1 = 0
  · obtain ⟨h1, h2⟩ := ht b hb
    simp only [hb, ↓reduceIte]
    constructor
    · rintro ⟨a1, a2, a3, -, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h2, a5, a6⟩
    · rintro ⟨a1, a2, a3, -, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h1, a5, a6⟩
  · simp only [hb, ↓reduceIte]

/-- **The upper time of a tree above its layers.** -/
theorem treeLeaves_upper_eq (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {t t' : ℝ} (s : ℝ) (k : Mom d)
    (ht : ∀ b : GBranch LG.garden.tree, (LG.layer b.toNode : ℝ) + 1 ≤ t ∧
      (LG.layer b.toNode : ℝ) + 1 ≤ t') :
    treeLeaves L γ δ LG H t s k = treeLeaves L γ δ LG H t' s k := by
  unfold treeLeaves
  refine kernelLeaves_congr_domain L γ δ LG H hfl ?_ k _ _
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  obtain ⟨h1, h2⟩ := ht b
  constructor
  · rintro ⟨a1, a2, a3, -, a5, a6⟩
    exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h2, a5, a6⟩
  · rintro ⟨a1, a2, a3, -, a5, a6⟩
    exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h1, a5, a6⟩

/-- **The lone-leaf time of a tree below its lone parent's layer.** -/
theorem treeLeaves_lower_eq (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) (t : ℝ) {s s' : ℝ} (k : Mom d)
    (hs : ∀ b : GBranch LG.garden.tree, LG.garden.IsLoneParent b →
      s ≤ LG.layer b.toNode ∧ s' ≤ LG.layer b.toNode) :
    treeLeaves L γ δ LG H t s k = treeLeaves L γ δ LG H t s' k := by
  unfold treeLeaves
  refine kernelLeaves_congr_domain L γ δ LG H hfl ?_ k _ _
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, a5, fun hb => lt_of_le_of_lt (hs b hb).2 a1⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, a5, fun hb => lt_of_le_of_lt (hs b hb).1 a1⟩

theorem JBtree_lower_eq (r : ℝ) (X : RegChain) (t : ℝ) {s : ℝ} (h : s ≤ r) :
    X.JBtree r t s = X.JBtree r t r := by
  simp only [RegChain.JBtree, max_eq_right h, max_self]

/-- **The leading term of a tree code below its layer.** -/
theorem LeafApp.tree_lower_eq (δ r : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (t : ℝ)
    {s : ℝ} (h : s ≤ r) (k : Mom d) : LeafApp.tree δ r H X ζ t s k = LeafApp.tree δ r H X ζ t r k := by
  simp only [LeafApp.tree, JBtree_lower_eq r X t h]

end WaveTurbulence.PL234
