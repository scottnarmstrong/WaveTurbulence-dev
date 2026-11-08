/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Decoded
public import WaveTurbulence.Foundations.Flower.MkMark.CapSep
public import WaveTurbulence.Foundations.Vine.B.Geom
public import WaveTurbulence.Foundations.Molecule.CLLeafRealization

/-! # B2b MK-MARK (c): stem-unclean pairs have zero weight (o75 Lemma 2(d), FL-SEP)

The twist-active set `𝐀(𝕍)` of a (CL) block `u` of the skeleton (o75 Def. 2.3) is the set of addresses of the
inflated garden whose owner is a node of the realization `G_sk[𝕍]` other than the upper joint `u₁`
(`activeSet`). A pair `(LG, σ)` is *stem-clean* at `u` when the capped stem avoids `𝐀(u)` (`StemCleanAt`).

* `stem_through_crown`: if the capped stem meets `𝐀(u)`, then the capped flower lies below one of the two lower
  crown nodes `u₂₁, u₂₂` (inflated), i.e. the capped stem passes through the inflated lower joint into one of
  its two external children. (A capped flower is paired across trees, while the leaves owned by the realization
  are paired inside one tree: `owner_pair`, main `cl_realization_completely_paired`.)
* `crown_gap_of_unclean`: hence, on decorations with capped frontier momenta at most `r` and a high root
  (FL-SEP hypotheses), the inflated crown gap is large: `‖k_root‖/2 ≤ ‖k(u₂₁) − k(u₂₂)‖`
  (`crown_not_gapF`, the capped FL-SEP).
* `weight_zero_of_unclean`: so every weight that vanishes off the FL-SEP support, restricted to decorations
  whose crown gap is below `‖k_root‖/2` (in particular the SG restriction at `u` when `L^{-γ+η} < ‖k_root‖/2`),
  vanishes identically. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-! ## Owner monotonicity -/

section Mono
variable (S : Garden w) (X : GBranch S.tree → RegChain)

/-- The tree index of an owner is the tree index of the address. -/
theorem owner_fst (y : Address w) : (owner S X y).1.1 = y.1 := by
  have h := (mem_ownRegion_owner S X y).1.1
  rw [inflatedPosition_fst] at h
  exact h

/-- Owners are monotone: an address below another has a descendant owner. -/
theorem owner_isDesc_of_addrBelow {x y : Address w} (h : AddrBelow x y) :
    (owner S X x).IsDesc (owner S X y) := by
  have hx := mem_ownRegion_owner S X x
  have hy := mem_ownRegion_owner S X y
  have hxy : AddrBelow (inflatedPosition S X (owner S X x)) y := addrBelow_trans hx.1 h
  rcases le_total (inflatedPosition S X (owner S X x)).2.length
      (inflatedPosition S X (owner S X y)).2.length with hle | hle
  · exact isDesc_of_addrBelow S X ⟨hxy.1.trans hy.1.1.symm,
      List.prefix_of_prefix_length_le hxy.2 hy.1.2 hle⟩
  · have hd : (owner S X y).IsDesc (owner S X x) := isDesc_of_addrBelow S X
      ⟨hy.1.1.trans hxy.1.symm, List.prefix_of_prefix_length_le hy.1.2 hxy.2 hle⟩
    by_cases he : owner S X x = owner S X y
    · rw [he]
      exact GNode.isDesc_refl _
    · exact absurd hxy (hy.2 _ hd he)

end Mono

/-! ## The twist-active set and stem cleanliness -/

/-- **The twist-active set `𝐀(𝕍)`** (o75 Def. 2.3) of the block with atoms `U` and upper joint `u` of the skeleton
`S`, in inflated addresses: owned by a realization node other than `u`. -/
def activeSet (S : Garden w) (X : GBranch S.tree → RegChain) (U : Finset (GBranch S.tree)) (u : GBranch S.tree) :
    Set (Address w) :=
  {y | owner S X y ∈ clRealizationNodes S U ∧ owner S X y ≠ u.toNode}

/-- The capped stem of `LG` avoids the twist-active set of the block `(U, u)` of a prime reconstruction. -/
def StemCleanAt {LG : LayeredGarden w} (J : Finset (Fin w)) (A : VineA.PrimeData LG)
    (U : Finset (GBranch A.skeleton.tree)) (u : GBranch A.skeleton.tree) : Prop :=
  ∀ a : GNode LG.garden.tree, OnCapStem LG J a → a.1 ∉ activeSet A.skeleton A.data.tree U u

/-- The (CL) block of a (CL) vine. -/
def clBlockOf {S : Garden w} (c : Stage1.CLVine S) : CLBlock S where
  atoms := c.atoms
  upper := c.upper
  lower := c.lower
  isBlock := c.isVine.choose_spec.1
  cl := ⟨c.notParentUpper, c.parentLower⟩

/-! ## The inflated lower joint and its crown children -/

section Crown
variable {LG : LayeredGarden w} (A : VineA.PrimeData LG)

theorem corePosition_mem_branching (b : GBranch A.skeleton.tree) :
    (A.data.corePosition b).2 ∈ (LG.garden.tree (A.data.corePosition b).1).branching := by
  have hbr := (A.data.coreBranch A.prime.1 b).2
  change (A.data.corePosition b).2 ∈ (A.data.forest A.prime.1 (A.data.corePosition b).1).branching at hbr
  rwa [decodes_tree A.decodes] at hbr

/-- The branch of the inflated garden at the core position of the skeleton branch `b`. -/
def inflatedBranch (b : GBranch A.skeleton.tree) : GBranch LG.garden.tree :=
  ⟨A.data.corePosition b, corePosition_mem_branching A b⟩

/-- Its children sit at the inflated positions of the skeleton children. -/
theorem inflatedBranch_child (b : GBranch A.skeleton.tree) (i : Fin 3) :
    ((inflatedBranch A b).child i).1 = inflatedPosition A.skeleton A.data.tree (b.child i) := by
  rw [ReconstructionData.core_child_position]
  rfl

end Crown

/-! ## Two ancestor facts -/

section Anc
variable {tree : Fin w → TTree}

/-- Two ancestors of one node are comparable. -/
theorem isDesc_total_of_common (x y : GNode tree) {z : GNode tree} (hx : x.IsDesc z) (hy : y.IsDesc z) :
    x.IsDesc y ∨ y.IsDesc x := by
  rcases le_total x.1.2.length y.1.2.length with h | h
  · exact Or.inl ⟨hx.1.trans hy.1.symm, List.prefix_of_prefix_length_le hx.2 hy.2 h⟩
  · exact Or.inr ⟨hy.1.trans hx.1.symm, List.prefix_of_prefix_length_le hy.2 hx.2 h⟩

/-- A node between a branch and one of its children is one of the two. -/
theorem ancestor_child_cases (b : GBranch tree) (i : Fin 3) {x : GNode tree} (h1 : b.toNode.IsDesc x)
    (h2 : x.IsDesc (b.child i)) (hne : x ≠ b.toNode) (hni : ¬ (b.child i).IsDesc x) : False := by
  have hp : x.1.2 <+: b.1.2 ++ [i] := h2.2
  rcases List.prefix_concat_iff.mp hp with he | he
  · exact hni ⟨h2.1.symm, by rw [he]; exact List.prefix_refl _⟩
  · have hb : b.1.2 <+: x.1.2 := h1.2
    have : x.1.2 = b.1.2 := (he.eq_of_length (le_antisymm he.length_le hb.length_le))
    exact hne (gnode_eq_of_val h1.1.symm this)

end Anc

/-! ## The capped stem passes through the crown -/

/-- **If the capped stem meets `𝐀(u)`, it passes through one of the two lower crown nodes.** -/
theorem stem_through_crown {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (a : GNode LG.garden.tree) (ha : OnCapStem LG J a)
    (hA : a.1 ∈ activeSet A.skeleton A.data.tree u.atoms u.upper) :
    OnCapStem LG J ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) ∨
      OnCapStem LG J ((inflatedBranch A u.lower).child (VineB.regionOf u).negative) := by
  obtain ⟨ℓ, hℓ, hd⟩ := ha
  obtain ⟨hreal, hne⟩ := hA
  have hbelow : AddrBelow a.1 ℓ.1 := ⟨hd.1, hd.2⟩
  have hmono := owner_isDesc_of_addrBelow A.skeleton A.data.tree hbelow
  -- the flower's owner is not in the realization
  have hf : owner A.skeleton A.data.tree ℓ.1 ∉ clRealizationNodes A.skeleton u.atoms := by
    intro hfr
    have hpo := owner_pair A.decodes ℓ
    have hJ1 : ℓ.1.1 ∉ J := hℓ.1
    have hJ2 : (LG.garden.pair ℓ).1.1 ∈ J := hℓ.2
    rcases hpo with he | ⟨l, hl1, hl2⟩
    · have e1 := owner_fst A.skeleton A.data.tree ℓ.1
      have e2 := owner_fst A.skeleton A.data.tree (LG.garden.pair ℓ).1
      rw [he] at e1
      exact hJ1 (e1.symm.trans e2 ▸ hJ2)
    · have hreal_l : Mole.InCLPrunedRegion A.skeleton u.atoms u.upper u.lower l.toNode := by
        rw [hl1]
        have := (RegRed.mem_clRealizationNodes _).mp hfr
        rw [← hl1] at this ⊢
        exact (Mole.cl_leaf_realization_iff A.skeleton u.isBlock u.cl l).mp
          ((Mole.leaf_incidence_realization_iff A.skeleton u.atoms l).mp this)
      have hpair := (Mole.cl_realization_completely_paired A.skeleton u.isBlock u.cl l hreal_l).2
      have t1 : l.toNode.1.1 = u.upper.toNode.1.1 := hreal_l.1.1.symm
      have t2 : (A.skeleton.pair l).toNode.1.1 = u.upper.toNode.1.1 := hpair.1.1.symm
      have e1 := owner_fst A.skeleton A.data.tree ℓ.1
      have e2 := owner_fst A.skeleton A.data.tree (LG.garden.pair ℓ).1
      rw [← hl1] at e1
      rw [← hl2] at e2
      apply hJ1
      rw [← e1, t1, ← t2, e2]
      exact hJ2
  -- the flower's owner lies below a lower crown node
  have hra := (VineB.real_iff u (owner A.skeleton A.data.tree a.1)).mp hreal
  have hup : u.upper.toNode.IsDesc (owner A.skeleton A.data.tree ℓ.1) := hra.1.trans hmono
  have hcrown : (u.upper.child (VineB.regionOf u).excluded).IsDesc (owner A.skeleton A.data.tree ℓ.1) ∨
      (u.lower.child (VineB.regionOf u).positive).IsDesc (owner A.skeleton A.data.tree ℓ.1) ∨
      (u.lower.child (VineB.regionOf u).negative).IsDesc (owner A.skeleton A.data.tree ℓ.1) := by
    by_contra hcon
    push Not at hcon
    exact hf ((VineB.real_iff u _).mpr ⟨hup, hcon.1, hcon.2.1, hcon.2.2⟩)
  have hflower : ∀ c : GNode A.skeleton.tree, c.IsDesc (owner A.skeleton A.data.tree ℓ.1) →
      AddrBelow (inflatedPosition A.skeleton A.data.tree c) ℓ.1 := fun c hc =>
    addrBelow_trans (addrBelow_inflatedPosition A.skeleton A.data.tree hc) (mem_ownRegion_owner A.skeleton A.data.tree ℓ.1).1
  have hnode : ∀ i, (u.lower.child i).IsDesc (owner A.skeleton A.data.tree ℓ.1) →
      OnCapStem LG J ((inflatedBranch A u.lower).child i) := by
    intro i hi
    have hb := hflower _ hi
    rw [← inflatedBranch_child A u.lower i] at hb
    exact ⟨ℓ, hℓ, hb.1, hb.2⟩
  rcases hcrown with h | h | h
  · exfalso
    have hcmp := isDesc_total_of_common (u.upper.child (VineB.regionOf u).excluded) (owner A.skeleton A.data.tree a.1) h hmono
    rcases hcmp with h1 | h1
    · exact hra.2.1 h1
    · exact ancestor_child_cases u.upper (VineB.regionOf u).excluded hra.1 h1 hne hra.2.1
  · exact Or.inl (hnode _ h)
  · exact Or.inr (hnode _ h)

/-! ## The crown gap of a stem-unclean pair is large -/

/-- **Zero-weight core (o75 Lemma 2(d), FL-SEP).** If the capped stem meets `𝐀(u)`, then on every decoration
with capped frontier momenta at most `r` and a high root, the inflated crown gap `k(u₂₁) − k(u₂₂)` has size at
least `‖k_root‖/2`. -/
theorem crown_gap_of_unclean {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d) (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2 ≤
      ‖k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)‖ := by
  unfold StemCleanAt at hun
  push Not at hun
  obtain ⟨a, ha, hA⟩ := hun
  rcases stem_through_crown A J u a ha hA with h | h
  · exact crown_not_gapF LG (IsCapFlower LG J) p N r k hk hU hlay hfl hN hr0 hfr _ (VineB.regionOf u).distinct h hK
  · rw [norm_sub_rev]
    exact crown_not_gapF LG (IsCapFlower LG J) p N r k hk hU hlay hfl hN hr0 hfr _
      (VineB.regionOf u).distinct.symm h hK

/-- In particular the inflated crown gap of a stem-unclean pair is a large gap (`LG`) as soon as
`L^{-γ+η} < ‖k_root‖/2`: it is neither `SG` nor `ZG`. -/
theorem crown_gapKind_of_unclean {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d) (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    (L γ η : ℝ) (hL : 0 ≤ L)
    (hθ : L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    Molecule.gapKind L γ η (k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)) = .LG := by
  have hg := crown_gap_of_unclean A J u hun p N r k hk hU hlay hfl hN hr0 hfr hK
  have hpos : (0 : ℝ) ≤ L ^ (-γ + η) := Real.rpow_nonneg hL _
  unfold Molecule.gapKind
  have hne : k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
      k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hg
    have hn := norm_nonneg (k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1))
    linarith
  have hlt : ¬ ‖k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
      k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)‖ ≤ L ^ (-γ + η) := by
    intro h
    linarith
  simp [hne, hlt]

/-- **Zero weight for stem-unclean pairs.** A weight `W` that vanishes off the FL-SEP support (capped frontier
momenta at most `r`, high root), restricted to decorations whose inflated crown gap at `u` is below
`‖k_root‖/2`, vanishes. -/
theorem weight_zero_of_unclean {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 → (∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    (hSel : ∀ k, Sel k → ‖k ((inflatedBranch A u.lower).child (VineB.regionOf u).positive) -
        k ((inflatedBranch A u.lower).child (VineB.regionOf u).negative)‖ <
      ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  intro k hk hs
  by_contra hW0
  obtain ⟨hfr, hK⟩ := hW k hW0
  have := crown_gap_of_unclean A J u hun p N r k hk hU hlay hfl hN hr0 hfr hK
  linarith [hSel k hs]

end WaveTurbulence.Flower.MkMark
