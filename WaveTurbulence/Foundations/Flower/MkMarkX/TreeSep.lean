/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.SigmaZero

/-! # B2e MK-X: per-tree FL-SEP (R177, F-B4-5)

B2b's `crown_gap_of_unclean` / `weight_zero_of_unclean` (and the σ-forms `_vinesV0`, `_collapsed`) bound the non-flower
top leaves of EVERY tree by one frontier scale `r`. Only the tree `j₀ := (inflatedBranch A u.lower).1.1` of the crown
enters the conservation argument (CapSep's `stem_errorF` runs along the stem of tree `j₀`, and the off-stem bound
`norm_le_of_offStemF` at a sibling of a stem node reads only top leaves below that sibling, again in tree `j₀`).

Formally: the restriction `restrictTree j₀ k` (equal to `k` on tree `j₀`, `0` elsewhere) is branch consistent, satisfies
the global frontier bound as soon as `k` satisfies it on tree `j₀` (`hr0 : 0 ≤ r`), and agrees with `k` at the root,
the lower joint and the crown of tree `j₀`. The separation is re-run with the order bound at tree `j₀` only
(`separation_tree`, `crown_not_gap_tree`, copies of CapSep's `separationF`/`crown_not_gapF` with `hN` localized).

Exports (hypotheses weakened, conclusions verbatim B2b's): `crown_gap_of_unclean_tree`, `weight_zero_of_unclean_tree`,
`weight_zero_of_unclean_vinesV0_tree`, `weight_zero_of_unclean_collapsed_tree`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Flower.FlSep
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkMarkX

variable {w : ℕ}

/-! ## Restriction of a decoration to one tree -/

section Restrict
variable {T : Fin w → TTree} {d : ℕ}

/-- `k` on the tree `j`, `0` on the other trees. -/
def restrictTree (j : Fin w) (k : GNode T → Mom d) : GNode T → Mom d :=
  fun a => if a.1.1 = j then k a else 0

theorem restrictTree_of_eq (j : Fin w) (k : GNode T → Mom d) {a : GNode T} (h : a.1.1 = j) :
    restrictTree j k a = k a := by simp [restrictTree, h]

theorem restrictTree_of_ne (j : Fin w) (k : GNode T → Mom d) {a : GNode T} (h : a.1.1 ≠ j) :
    restrictTree j k a = 0 := by simp [restrictTree, h]

theorem isBranchConsistent_restrictTree (j : Fin w) {k : GNode T → Mom d} (hk : IsBranchConsistent k) :
    IsBranchConsistent (restrictTree j k) := by
  intro b
  have e : ∀ i : Fin 3, (b.child i).1.1 = b.toNode.1.1 := fun _ => rfl
  by_cases h : b.toNode.1.1 = j
  · rw [restrictTree_of_eq j k h, restrictTree_of_eq j k ((e 0).trans h), restrictTree_of_eq j k ((e 1).trans h),
      restrictTree_of_eq j k ((e 2).trans h)]
    exact hk b
  · rw [restrictTree_of_ne j k h, restrictTree_of_ne j k (fun h' => h ((e 0).symm.trans h')),
      restrictTree_of_ne j k (fun h' => h ((e 1).symm.trans h')), restrictTree_of_ne j k (fun h' => h ((e 2).symm.trans h'))]
    simp

end Restrict

/-! ## Separation with the order bound at one tree -/

section Sep
variable (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (p N : ℕ) {d : ℕ} (r : ℝ)
  (k : GNode LG.garden.tree → Mom d)

/-- CapSep's `separationF` with the order bound at the tree of `v` only (`w` in the same tree). -/
theorem separation_tree (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    {v x : GNode LG.garden.tree} (hv : OnStemF LG Fl v) (hx : IsTopNode LG p x) (hxs : ¬ OnStemF LG Fl x)
    (hxv : x.1.1 = v.1.1) (hN : LG.topOrder p v.1.1 ≤ N)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree v.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree v.1.1)‖ / 2 ≤ ‖k v - k x‖ := by
  obtain ⟨s, hs, hse⟩ := stem_errorF LG Fl p r k hk hU hlay hfl hr0 hfr v.1.1 _ v rfl rfl hv
  have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hcr : (LG.topCountBelow p (GNode.root LG.garden.tree v.1.1) : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p (GNode.root LG.garden.tree v.1.1)
    exact_mod_cast this.trans hN
  have hcx : (LG.topCountBelow p x : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p x
    rw [hxv] at this
    exact_mod_cast this.trans hN
  have hxb := norm_le_of_offStemF LG Fl p r k hk hlay hr0 hfr x hx hxs
  have hkv : ‖k (GNode.root LG.garden.tree v.1.1)‖ - 2 * N * r ≤ ‖k v‖ := by
    have h1 : ‖k (GNode.root LG.garden.tree v.1.1)‖ ≤
        ‖k (GNode.root LG.garden.tree v.1.1) - s • k v‖ + ‖s • k v‖ := by
      have := norm_add_le (k (GNode.root LG.garden.tree v.1.1) - s • k v) (s • k v)
      simpa using this
    rw [norm_smul, hs1, one_mul] at h1
    have : 2 * ((LG.topCountBelow p (GNode.root LG.garden.tree v.1.1) : ℝ) - LG.topCountBelow p v) * r ≤
        2 * N * r := by
      have := Nat.cast_nonneg (α := ℝ) (LG.topCountBelow p v)
      nlinarith
    linarith
  have h2 : ‖k v‖ - ‖k x‖ ≤ ‖k v - k x‖ := norm_sub_norm_le (k v) (k x)
  nlinarith

/-- CapSep's `crown_not_gapF` with the order bound at the tree of `b` only. -/
theorem crown_not_gap_tree (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    (b : GBranch LG.garden.tree) (hN : LG.topOrder p b.1.1 ≤ N) {i j : Fin 3} (hij : i ≠ j)
    (hi : OnStemF LG Fl (b.child i))
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree b.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree b.1.1)‖ / 2 ≤ ‖k (b.child i) - k (b.child j)‖ := by
  have hbst : OnStemF LG Fl b.toNode := by
    obtain ⟨ℓ, hℓ, hd⟩ := hi
    exact ⟨ℓ, hℓ, (GBranch.isDesc_child b i).trans hd⟩
  have hbl : LG.layer b.toNode = p := layer_eq_of_onStemF LG Fl p hlay hfl hbst
  have e : (b.child i).1.1 = b.1.1 := rfl
  have := separation_tree LG Fl p N r k hk hU hlay hfl hr0 hfr hi (isTopNode_child LG p hlay b hbl j)
    (not_onStemF_sibling LG Fl hU b hij hi) rfl (by rw [e]; exact hN) (by rw [e]; exact hK)
  rwa [e] at this

end Sep

/-! ## The per-tree FL-SEP for stem-unclean pairs -/

/-- **Per-tree zero-weight core.** As `crown_gap_of_unclean`, with the frontier bound only on the non-flower top leaves
of the crown's tree `j₀` and the order bound only at `j₀`. -/
theorem crown_gap_of_unclean_tree {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d) (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
      ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2 ≤
      ‖k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)‖ := by
  set b := inflatedBranch A u.lower with hb
  set j₀ := b.1.1
  set k' := restrictTree j₀ k
  have hk' : IsBranchConsistent k' := isBranchConsistent_restrictTree j₀ hk
  have hfr' : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k' a‖ ≤ r := by
    intro a ha hna
    show ‖restrictTree j₀ k a‖ ≤ r
    by_cases h : a.1.1 = j₀
    · rw [restrictTree_of_eq j₀ k h]
      exact hfr a h ha hna
    · rw [restrictTree_of_ne j₀ k h, norm_zero]
      exact hr0
  have eR : k' (GNode.root LG.garden.tree j₀) = k (GNode.root LG.garden.tree j₀) := restrictTree_of_eq j₀ k rfl
  have eC : ∀ i : Fin 3, k' (b.child i) = k (b.child i) := fun i => restrictTree_of_eq j₀ k rfl
  have hK' : (2 * (N : ℝ) + 2) * r ≤ ‖k' (GNode.root LG.garden.tree b.1.1)‖ / 4 := by
    rw [eR]
    exact hK
  unfold StemCleanAt at hun
  push Not at hun
  obtain ⟨a, ha, hA⟩ := hun
  rcases stem_through_crown A J u a ha hA with h | h
  · have := crown_not_gap_tree LG (IsCapFlower LG J) p N r k' hk' hU hlay hfl hr0 hfr' b hN
      (VineB.regionOf u).distinct h hK'
    rwa [eR, eC, eC] at this
  · have := crown_not_gap_tree LG (IsCapFlower LG J) p N r k' hk' hU hlay hfl hr0 hfr' b hN
      (VineB.regionOf u).distinct.symm h hK'
    rw [eR, eC, eC, norm_sub_rev] at this
    exact this

/-- **Per-tree zero weight for stem-unclean pairs** (`weight_zero_of_unclean` with `hW` reading only tree `j₀`). -/
theorem weight_zero_of_unclean_tree {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 →
      (∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
        ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    (hSel : ∀ k, Sel k → ‖k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)‖ <
      ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  intro k hk hs
  by_contra hW0
  obtain ⟨hfr, hK⟩ := hW k hW0
  have := crown_gap_of_unclean_tree A J u hun p N r k hk hU hlay hfl hN hr0 hfr hK
  linarith [hSel k hs]

/-- **Per-tree zero weight under the σ-restriction** (`weight_zero_of_unclean_vinesV0`, `hW` at tree `j₀`). -/
theorem weight_zero_of_unclean_vinesV0_tree {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 →
      (∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
        ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ vinesV0 A.skeleton σ, V.atoms = u.atoms)
    (hSel : ∀ k, Sel k → ∃ (z : GNode A.skeleton.tree → (Fin d → ℤ)) (k₀ : Mom d), IsDecoration A.skeleton z ∧
      VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z ∧
      skDec A k = cosetDecoration A.skeleton L k₀ z)
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean_tree A J u hun p N r hr0 hU hlay hfl hN W Sel hW ?_
  intro k hk
  obtain ⟨z, k₀, hz, hsel, he⟩ := hSel k hk
  obtain ⟨V, hV, hVU⟩ := hu
  rw [crown_gap_skDec, he]
  exact lt_of_le_of_lt (crown_gap_le_of_vinesV0 A.prime.1 hL γ η base z hz σ hsel hV hVU u.isBlock
    (VineB.regionOf u) k₀).2 (hθ k hk)

/-- **Per-tree zero weight, collapsed form** (`weight_zero_of_unclean_collapsed`, `hW` at tree `j₀`). -/
theorem weight_zero_of_unclean_collapsed_tree {LG : LayeredGarden w} (A : VineA.PrimeData LG)
    (J : Finset (Fin w)) (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 →
      (∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
        ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ vinesV0 A.skeleton σ, V.atoms = u.atoms) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (hSel : ∀ k, Sel k → ∃ (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (k₀ : Mom d),
      VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base
        (collapseGenDecoration A.data A.prime.1 κ).1 ∧
      ∀ x, k x = k₀ + latticePoint L (ofForest A κ.1 x))
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean_vinesV0_tree A J u hun p N r hr0 hU hlay hfl hN W Sel hW hL γ η base σ hu ?_ hθ
  intro k hk
  obtain ⟨κ, k₀, hsel, he⟩ := hSel k hk
  exact ⟨(collapseGenDecoration A.data A.prime.1 κ).1, k₀, (collapseGenDecoration A.data A.prime.1 κ).2.1, hsel,
    skDec_coset_collapse A κ L k₀ k he⟩

end WaveTurbulence.Flower.MkMarkX
