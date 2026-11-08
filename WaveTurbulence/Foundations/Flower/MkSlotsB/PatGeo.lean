/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Rest
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCount

/-! # B3s-HELPER3 B4 (1/4): the values and layers of the pattern pins

For an arbitrary pattern `pat` the intrinsic pins `fixCap LG J pat t s` take only the values `s` (capped flower
parents, `dParent`, `dChild`) and `t` (`dRoot`, at a root that is not a capped flower parent) (`fixCap_cases`,
`fixCap_value`). Every pinned branch is in layer `p` (`fixCap_layer`): capped flower parents and `dParent` pins lie
on the capped stem (`CapGeo.stem_layer`), `dChild` pins by `CapPatValid`, and `dRoot` roots because every non-cap
tree carries a capped flower (`exists_capFlower_of_card`: `2·|J| = w`, cap trees are single leaves, no two cap roots
paired, one capped flower per tree), so its root is on the capped stem. Hence, for `p < s < t < p + 1`:

* **`fixCap_val`**: a pinned value `v` at `b` has `layer b < v ≤ layer b + 1` and `v ≤ t`;
* **`fixCap_mono`**: along a strict descendant both pinned, the lower pin is `≤` the upper one (lower pins are `s`);
* on `G_sb` (`fixOf`, layers of the core branches): `fixOf_val`, **`fixOf_mono_child`** (adjacent version: a child
  atom of a `G_sb` atom is never a root, so its pin is `s`), and **`fixOf_hinge`** (hinge clocks are free: no unit
  atom is pinned, `Geo.fixCap_coreBranch_unit`);
* **`pieceRest_pat`** / **`pieceRest_patJ`**: the six B3s fields `PieceRestB3s` of the class piece with the pattern
  pins `fixOf J pat t s mkF a` (filter `none`, dagger indicator `sibIndOf`), generalizing `Rest.pieceRest_alpha`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## The four kinds of pins -/

/-- **The pins of a pattern**: a capped flower parent at `s`; otherwise the pattern's pin — a `dRoot` root at `t`, a
`dParent` parent of a capped flower parent at `s`, a `dChild i` child `i` of a capped flower parent at `s`. -/
theorem fixCap_cases {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    (IsCapFlowerParent LG J b ∧ v = s) ∨
    (¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dRoot ∧ b.1.2 = [] ∧ v = t) ∨
    (¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dParent ∧
      (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b) ∧ v = s) ∨
    (∃ i : Fin 3, ¬ IsCapFlowerParent LG J b ∧ pat b.1.1 = FixPat.dChild i ∧
      (∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]) ∧ v = s) := by
  unfold fixCap at h
  by_cases hc : IsCapFlowerParent LG J b
  · simp only [hc, ↓reduceIte] at h
    exact Or.inl ⟨hc, (Option.some.inj h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    right
    cases hp : pat b.1.1 with
    | plain => rw [hp] at h; exact absurd h (by simp)
    | dRoot =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inl ⟨hc, rfl, h0, (Option.some.inj h).symm⟩
    | dParent =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inr (Or.inl ⟨hc, rfl, h0, (Option.some.inj h).symm⟩)
    | dChild i =>
      rw [hp] at h
      simp only at h
      split_ifs at h with h0
      exact Or.inr (Or.inr ⟨i, hc, rfl, h0, (Option.some.inj h).symm⟩)

/-- The pinned values: `s`, or `t` at a root. -/
theorem fixCap_value {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    v = s ∨ (v = t ∧ b.1.2 = [] ∧ pat b.1.1 = FixPat.dRoot) := by
  rcases fixCap_cases h with ⟨-, hv⟩ | ⟨-, hp, h0, hv⟩ | ⟨-, -, -, hv⟩ | ⟨i, -, -, -, hv⟩
  · exact Or.inl hv
  · exact Or.inr ⟨hv, h0, hp⟩
  · exact Or.inl hv
  · exact Or.inl hv

/-! ## Every non-cap tree carries a capped flower (`2·|J| = w`) -/

/-- **No two cap roots are paired** in an irreducible plain garden with `2·|J| = w` and single-leaf cap trees. -/
theorem capPair_not_cap (G : Garden w) (hp : G.IsPlain) (hirr : G.Irreducible) (J : Finset (Fin w))
    (hJ : 2 * J.card = w) (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) :
    ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J := by
  intro ℓ h1 h2
  let A : Finset (Fin w) := {ℓ.1.1, (G.pair ℓ).1.1}
  have hAJ : A ⊆ J := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h1
    · rw [Finset.mem_singleton.mp hj]; exact h2
  refine hirr A ⟨ℓ.1.1, Finset.mem_insert_self _ _⟩ ?_ ?_
  · intro hA
    have hJu : J = Finset.univ := Finset.eq_univ_of_forall fun j => hAJ (hA ▸ Finset.mem_univ j)
    have hc : J.card = w := by rw [hJu, Finset.card_univ, Fintype.card_fin]
    have h0 : J.card = 0 := by omega
    exact absurd h1 (by rw [Finset.card_eq_zero.mp h0]; exact Finset.notMem_empty _)
  · intro ℓ' hℓ'
    have hne : G.pair ℓ' ≠ ℓ' := fun he => ((G.pair_eq_iff ℓ').mp he) (hp ℓ')
    refine ⟨hne, ?_⟩
    have hA' : ℓ'.1.1 ∈ A := (Finset.mem_filter.mp hℓ').2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hA' with he | he
    · have e1 := eq_rootLeaf (hcap _ h1) ℓ' he
      have e2 := eq_rootLeaf (hcap _ h1) ℓ rfl
      rw [e1, ← e2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · have he' : ℓ'.1.1 = (G.pair ℓ).1.1 := Finset.mem_singleton.mp he
      have e1 := eq_rootLeaf (hcap _ h2) ℓ' he'
      have e2 := eq_rootLeaf (hcap _ h2) (G.pair ℓ) rfl
      rw [e1, ← e2, G.pair_pair]
      exact Finset.mem_insert_self _ _

/-- **Every non-cap tree carries a capped flower** (`2·|J| = w`, single-leaf cap trees, no two cap roots paired, at
most one capped flower per tree): the trees of the partners of the `|J|` cap roots are pairwise distinct non-cap
trees, hence all of them. -/
theorem exists_capFlower_of_card (G : Garden w) (J : Finset (Fin w)) (hJ : 2 * J.card = w)
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J)
    (hone : ∀ ℓ ℓ' : GLeaf G.tree, ℓ.1.1 ∉ J → (G.pair ℓ).1.1 ∈ J → ℓ'.1.1 ∉ J → (G.pair ℓ').1.1 ∈ J →
      ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ') :
    ∀ j ∉ J, ∃ ℓ : GLeaf G.tree, ℓ.1.1 ∉ J ∧ (G.pair ℓ).1.1 ∈ J ∧ ℓ.1.1 = j := by
  intro j hj
  let f : ∀ j' ∈ J, Fin w := fun j' hj' => (G.pair (rootLeaf G j' (hcap j' hj'))).1.1
  have hf : ∀ j' (hj' : j' ∈ J), f j' hj' ∈ Finset.univ \ J := fun j' hj' =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcc _ hj'⟩
  have hfl : ∀ j' (hj' : j' ∈ J), (G.pair (G.pair (rootLeaf G j' (hcap j' hj')))).1.1 ∈ J := by
    intro j' hj'
    rw [G.pair_pair]
    exact hj'
  have hinj : ∀ j₁ j₂ (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J), f j₁ h₁ = f j₂ h₂ → j₁ = j₂ := by
    intro j₁ j₂ h₁ h₂ he
    have hl := hone _ _ (hcc _ h₁) (hfl j₁ h₁) (hcc _ h₂) (hfl j₂ h₂) he
    have hr := congrArg G.pair hl
    rw [G.pair_pair, G.pair_pair] at hr
    exact congrArg (fun ℓ : GLeaf G.tree => ℓ.1.1) hr
  have hcard : (Finset.univ \ J).card ≤ J.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j', hj', he⟩ := Finset.surj_on_of_inj_on_of_card_le f hf hinj hcard j
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
  exact ⟨G.pair (rootLeaf G j' (hcap j' hj')), hcc _ hj', hfl j' hj', he.symm⟩

/-- The capped-flower form of `exists_capFlower_of_card` on a capped component (`CapGeo`, irreducible, plain,
`2·|J| = w`). -/
theorem exists_capFlower_of_capGeo {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    (hp : LG.garden.IsPlain) (hirr : LG.garden.Irreducible) (hJ : 2 * J.card = w) :
    ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j := by
  intro j hj
  obtain ⟨ℓ, h1, h2, h3⟩ := exists_capFlower_of_card LG.garden J hJ hG.cap_leaf
    (capPair_not_cap LG.garden hp hirr J hJ hG.cap_leaf)
    (fun ℓ ℓ' a1 a2 a3 a4 he => hG.one_flower ℓ ℓ' ⟨a1, a2⟩ ⟨a3, a4⟩ he) j hj
  exact ⟨ℓ, ⟨h1, h2⟩, h3⟩

/-! ## Layers and values -/

/-- A branch never lies in a cap tree. -/
theorem branch_not_cap {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    (b : GBranch LG.garden.tree) : b.1.1 ∉ J := by
  intro hb
  have h := b.2
  rw [hG.cap_leaf _ hb] at h
  simp [TTree.branching] at h

/-- **Every pinned branch is in layer `p`.** `hroot`: every non-cap tree carries a capped flower
(`exists_capFlower_of_capGeo`). -/
theorem fixCap_layer {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat} {t s : ℝ}
    (hG : CapGeo LG J p) (hpat : CapPatValid LG J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j)
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    LG.layer b.toNode = p := by
  rcases fixCap_cases h with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨c, hc, hcb⟩, -⟩ | ⟨i, -, hpi, ⟨c, hc, h1, h2⟩, -⟩
  · exact layer_capFlowerParent hG hc
  · obtain ⟨ℓ, hℓ, hℓj⟩ := hroot b.1.1 (branch_not_cap hG b)
    refine hG.stem_layer _ ⟨ℓ, hℓ, hℓj.symm, ?_⟩
    show b.1.2 <+: ℓ.1.2
    rw [h0]
    exact List.nil_prefix
  · obtain ⟨ℓ, hℓ, hℓt, i, hℓp⟩ := hc
    obtain ⟨hcb1, i', hcb2⟩ := hcb
    refine hG.stem_layer _ ⟨ℓ, hℓ, (hℓt.trans hcb1).symm, ?_⟩
    show b.1.2 <+: ℓ.1.2
    rw [hℓp, hcb2, List.append_assoc]
    exact List.prefix_append _ _
  · refine hpat b c i hc ?_ (Prod.ext h1 h2)
    rw [← h1]
    exact hpi

/-- **`val` for the member pins**: a pinned value lies in the layer window of its branch and below the top time. -/
theorem fixCap_val {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat} {t s : ℝ}
    (hG : CapGeo LG J p) (hpat : CapPatValid LG J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1)
    {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) :
    (LG.layer b.toNode : ℝ) < v ∧ v ≤ LG.layer b.toNode + 1 ∧ v ≤ t := by
  rw [fixCap_layer hG hpat hroot h]
  rcases fixCap_value h with rfl | ⟨rfl, -, -⟩
  · exact ⟨hs.1, by linarith [hs.2], hs.2.le⟩
  · exact ⟨hs.1.trans hs.2, ht.le, le_rfl⟩

/-- **`mono` for the member pins**: if `b'` is a strict descendant of `b` (same tree, `b`'s address a proper prefix
of `b'`'s) and both are pinned, then the pin of `b'` is at most that of `b` (the lower pin is `s`, a non-root). -/
theorem fixCap_mono {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ} (hst : s ≤ t)
    {b b' : GBranch LG.garden.tree} (hdesc : b.toNode.IsDesc b'.toNode) (hne : b ≠ b') {v v' : ℝ}
    (h : fixCap LG J pat t s b = some v) (h' : fixCap LG J pat t s b' = some v') : v' ≤ v := by
  have hnr : b'.1.2 ≠ [] := by
    intro h0
    apply hne
    have hp : b.1.2 <+: b'.1.2 := hdesc.2
    rw [h0, List.prefix_nil] at hp
    exact Subtype.ext (Prod.ext hdesc.1 (hp.trans h0.symm))
  have hv' : v' = s := by
    rcases fixCap_value h' with hv | ⟨-, h0, -⟩
    · exact hv
    · exact absurd h0 hnr
  rcases fixCap_value h with hv | ⟨hv, -, -⟩
  · rw [hv', hv]
  · rw [hv', hv]; exact hst

/-! ## The pins of the class piece on `G_sb` -/

section Piece

variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (mkF : Stage1Mk.MarkFn w)
  (a : PrescribedPrimeGarden w)

/-- `val` on `G_sb` (layers of the core branches, root time `t`). -/
theorem fixOf_val {p : ℕ} (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf a.layered.garden.tree, IsCapFlower a.layered J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (c : GBranch (stA mkF a).G.tree) (v : ℝ)
    (h : fixOf J pat t s mkF a c = some v) :
    (a.layered.layer (coreOf mkF a c).toNode : ℝ) < v ∧ v ≤ a.layered.layer (coreOf mkF a c).toNode + 1 ∧ v ≤ t :=
  fixCap_val hG hpat hroot hs ht h

/-- The splice shape of the piece (main's `stShape`, whose branch map is the old-name map `M.ob`). -/
abbrev shapeOf : VineB.SpliceShape
    (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)) (stA mkF a).G :=
  VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)

theorem shapeOf_br : (shapeOf mkF a).br = (stA mkF a).M.ob := rfl

/-- The old name of a non-root `G_sb` branch is a non-root skeleton branch. -/
theorem ob_path_ne_nil {c : GBranch (stA mkF a).G.tree} (hc : c.1.2 ≠ []) : ((stA mkF a).M.ob c).1.2 ≠ [] := by
  intro h0
  apply hc
  have hn : (shapeOf mkF a).node c.toNode = (shapeOf mkF a).node (GNode.root (stA mkF a).G.tree c.1.1) := by
    rw [(shapeOf mkF a).root, ← (shapeOf mkF a).br_node]
    apply Subtype.ext
    exact Prod.ext (ob_fst mkF a c) h0
  have he := (shapeOf mkF a).inj hn
  exact congrArg (fun x : GNode (stA mkF a).G.tree => x.1.2) he

/-- The inflated position of a non-root skeleton node has a non-empty path. -/
theorem inflatedPosition_path_ne_nil {S : Garden w} (X : GBranch S.tree → RegChain) (y : GNode S.tree)
    (hy : y.1.2 ≠ []) : (Reg.Skeleton.inflatedPosition S X y).2 ≠ [] := by
  rw [Reg.Skeleton.inflatedPosition]
  simp [hy, addrExt]

/-- The core branch of a non-root `G_sb` branch is not a root. -/
theorem coreOf_path_ne_nil {c : GBranch (stA mkF a).G.tree} (hc : c.1.2 ≠ []) : (coreOf mkF a c).1.2 ≠ [] := by
  show (a.prime.data.corePosition ((stA mkF a).M.ob c)).2 ≠ []
  unfold Reg.Skeleton.ReconstructionData.corePosition
  have h := inflatedPosition_path_ne_nil a.prime.data.tree ((stA mkF a).M.ob c).toNode (ob_path_ne_nil mkF a hc)
  simp only [addrExt]
  intro h0
  exact h (List.append_eq_nil_iff.mp h0).1

/-- **`mono` on `G_sb`, adjacent version**: a pinned child atom of a pinned atom carries a pin `≤` the parent's. -/
theorem fixOf_mono_child (hst : s ≤ t) {c c' : GBranch (stA mkF a).G.tree} (hcc : c'.IsChildOf c) {v v' : ℝ}
    (h : fixOf J pat t s mkF a c = some v) (h' : fixOf J pat t s mkF a c' = some v') : v' ≤ v := by
  have hnr : c'.1.2 ≠ [] := by
    obtain ⟨-, i, hi⟩ := hcc
    rw [hi]; simp
  have hv' : v' = s := by
    rcases fixCap_value h' with hv | ⟨-, h0, -⟩
    · exact hv
    · exact absurd h0 (coreOf_path_ne_nil mkF a hnr)
  rcases fixCap_value h with hv | ⟨hv, -, -⟩
  · rw [hv', hv]
  · rw [hv', hv]; exact hst

/-- **Hinge clocks are free**: no hinge of `G_sb` (the upper atom of a unit) is pinned, for every pattern
(`Geo.fixCap_coreBranch_unit`). -/
theorem fixOf_hinge (kSel : Fin w → Option ℕ)
    (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (c : GBranch (stA mkF a).G.tree) (hc : c ∈ (stA mkF a).hinges) : fixOf J pat t s mkF a c = none := by
  rw [← VineB.stShape_hingesMk, VineB.SpliceShape.mem_hinges] at hc
  obtain ⟨j, hj⟩ := hc
  have hmem : VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j ∈
      unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a) := List.get_mem _ _
  have hy : (stA mkF a).M.ob c ∈
      (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j).atoms := by
    rw [← shapeOf_br, hj]
    exact VineB.upper_mem _
  exact fixCap_coreBranch_unit pat t s kSel mkF hsub a hmem hy

end Piece

/-! ## The six B3s fields with the pattern pins -/

/-- **The six B3s fields for the pattern data** (`Rest.pieceRest_alpha` for an arbitrary pattern). `hroot`: every
non-cap tree of the representative carries a capped flower (`pieceRest_patJ` derives it from `J.card = R`). -/
theorem pieceRest_pat (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (pat : Fin (2 * R) → FixPat)
    (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf a.layered.garden.tree, IsCapFlower a.layered J ℓ ∧ ℓ.1.1 = j)
    (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (kSel : Fin (2 * R) → Option ℕ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop) (cθ : ℝ) :
    PieceRestB3s (classPiece P mkF a (protOf J pat t s kSel mkF a) (protI a.layered J pat t s kSel).card
      (fixOf J pat t s mkF a) (fun _ => none) (sibIndOf J mkF a dag flw)) cθ where
  prot_card := (card_protOf_le J _ t s kSel mkF a).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  fix_prot b hb := fixOf_prot b hb
  fix_layer b x hb := by
    have hb' : fixOf J pat t s mkF a b = some x := hb
    have := fixOf_val J pat t s mkF a hG hpat hroot hs ht b x hb'
    exact ⟨this.1.le, this.2.1⟩
  filt_ok a q hq := by
    change (none : Option (ℝ × SchwartzMap ℝ ℂ)) = some q at hq
    exact absurd hq (by simp)
  ind_ok k := sibIndOf_mem J mkF a dag flw k
  ind_local k k' h := sibIndOf_local J pat t s kSel mkF a dag flw k k'
    fun c hc i => (h c (Finset.mem_union_right _ hc) i).1
  lb_free b hb := by
    change ((none : Option ℝ)).isSome = true at hb
    simp at hb
  lb_prot b hb := by
    change ((none : Option ℝ)).isSome = true at hb
    simp at hb
  lb_layer b x hb := by
    change (none : Option ℝ) = some x at hb
    simp at hb

/-- **`pieceRest_pat` from `J.card = R`** (with the plainness and irreducibility of the representative's garden). -/
theorem pieceRest_patJ (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (hJ : J.card = R) (p : ℕ)
    (pat : Fin (2 * R) → FixPat) (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p) (hpl : a.layered.garden.IsPlain)
    (hirr : a.layered.garden.Irreducible)
    (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (kSel : Fin (2 * R) → Option ℕ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop) (cθ : ℝ) :
    PieceRestB3s (classPiece P mkF a (protOf J pat t s kSel mkF a) (protI a.layered J pat t s kSel).card
      (fixOf J pat t s mkF a) (fun _ => none) (sibIndOf J mkF a dag flw)) cθ :=
  pieceRest_pat P J p pat mkF a hG hpat (exists_capFlower_of_capGeo hG hpl hirr (by rw [hJ])) t s hs ht kSel dag
    flw cθ

end WaveTurbulence.Flower.MkSlotsB
