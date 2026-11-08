/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedBase
public import WaveTurbulence.Foundations.Molecule.TwistBondLabels
public import WaveTurbulence.Foundations.Molecule.UnitTwistMolecule
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw4DecEq

/-! # V5-SPACE-EXT: the bond weight of a CL region and its exact twist transport

`bondW ψ L base G lay U x` is the product, over the darts of the molecule of `G` with both ends in `U`
(`Molecule.InGroup`), of `ψ (far-end layer) (near-end layer) (bond momentum)`. The layer function `lay` is
the skeleton (core) layering of a class member. A unit twist is a directed-molecule isomorphism
(`twistDartEquiv`) preserving every bond label (`twist_bond_labels`), so the product is transported exactly;
no single factor is (TARGET Remark twistexplain (a),(d), L1449/L1452). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist

variable {w d : ℕ}

/-- The darts of the atomic group `U` (both ends in `U`). -/
def regionDarts (G : Garden w) (U : Finset (GBranch G.tree)) : Finset (GardenDart G) :=
  Finset.univ.filter (G.molecule.InGroup U)

theorem mem_regionDarts {G : Garden w} {U : Finset (GBranch G.tree)} {y : GardenDart G} :
    y ∈ regionDarts G U ↔ G.molecule.InGroup U y := by
  simp [regionDarts]

theorem inGroup_mate_iff {G : Garden w} {U : Finset (GBranch G.tree)} (y : GardenDart G) :
    G.molecule.InGroup U (G.molecule.mate y) ↔ G.molecule.InGroup U y := by
  unfold Molecule.InGroup
  rw [G.molecule.mate_mate]
  exact and_comm

/-- **The bond weight of the region `U`.** Each dart contributes `ψ` of the layer at its far end, the layer at
its own end and the momentum of its bond. -/
def bondW (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (G : Garden w)
    (lay : GBranch G.tree → ℕ) (U : Finset (GBranch G.tree)) (x : GNode G.tree → Fin d → ℤ) : ℂ :=
  ∏ y ∈ regionDarts G U, ψ (lay (G.molecule.atom (G.molecule.mate y))) (lay (G.molecule.atom y))
    (cosetDecoration G L base x (Mole.dartNode G y))

theorem norm_bondW_le (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (G : Garden w)
    (lay : GBranch G.tree → ℕ) (U : Finset (GBranch G.tree)) (x : GNode G.tree → Fin d → ℤ)
    (C : ℝ) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C) :
    ‖bondW ψ L base G lay U x‖ ≤ C ^ (regionDarts G U).card := by
  unfold bondW
  rw [norm_prod]
  calc ∏ y ∈ regionDarts G U, ‖ψ (lay (G.molecule.atom (G.molecule.mate y))) (lay (G.molecule.atom y))
        (cosetDecoration G L base x (Mole.dartNode G y))‖
      ≤ ∏ _y ∈ regionDarts G U, C := by
        gcongr with y hy
        exact hψ _ _ _
    _ = C ^ (regionDarts G U).card := Finset.prod_const _

theorem bondW_congr (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (G : Garden w)
    {lay lay' : GBranch G.tree → ℕ} (U : Finset (GBranch G.tree)) {x x' : GNode G.tree → Fin d → ℤ}
    (hl : ∀ v ∈ U, lay v = lay' v) (hx : ∀ y ∈ regionDarts G U, x (Mole.dartNode G y) = x' (Mole.dartNode G y)) :
    bondW ψ L base G lay U x = bondW ψ L base G lay' U x' := by
  unfold bondW
  refine Finset.prod_congr rfl fun y hy => ?_
  have hy' := mem_regionDarts.mp hy
  rw [hl _ hy'.1, hl _ hy'.2]
  unfold cosetDecoration
  rw [hx y hy]

/-- **Exact transport along any unit twist**, given the bond labels and the layers at the atoms. -/
theorem bondW_transport (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) {G : Garden w} (P : CorePlacement G)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ) (U : Finset (GBranch G.tree))
    (κ : GNode G.tree → Fin d → ℤ) (κ' : GNode (unitTwistGarden G P).tree → Fin d → ℤ)
    (hlab : ∀ y ∈ regionDarts G U,
      Mole.restrictLabels (unitTwistGarden G P) κ' (twistDartEquiv G P y) = Mole.restrictLabels G κ y)
    (hlay : ∀ v ∈ U, lay' (coreBranchEquiv G P v) = lay v) :
    bondW ψ L base (unitTwistGarden G P) lay' (twistedAtoms G P U) κ' = bondW ψ L base G lay U κ := by
  unfold bondW
  symm
  refine Finset.prod_equiv (twistDartEquiv G P) (fun y => ?_) (fun y hy => ?_)
  · simp only [mem_regionDarts, Molecule.InGroup, twistDartEquiv_atom, twistDartEquiv_mate]
    exact and_congr (mem_twistedAtoms G P U _).symm (mem_twistedAtoms G P U _).symm
  · have hy' := mem_regionDarts.mp hy
    rw [twistDartEquiv_mate, twistDartEquiv_atom, twistDartEquiv_atom, hlay _ hy'.1, hlay _ hy'.2]
    unfold cosetDecoration
    have h := hlab y hy
    unfold Mole.restrictLabels at h
    rw [h]

/-- The S-side and bottom-vine twist: the concrete twisted labels on a paired decoration. -/
theorem bondW_twist (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) {G : Garden w} (P : CorePlacement G)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ) (U : Finset (GBranch G.tree))
    (κ : GNode G.tree → Fin d → ℤ) (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode)
    (hlay : ∀ v ∈ U, lay' (coreBranchEquiv G P v) = lay v) :
    bondW ψ L base (unitTwistGarden G P) lay' (twistedAtoms G P U) (twistNodeLabels G P κ) =
      bondW ψ L base G lay U κ :=
  bondW_transport ψ L base P lay lay' U κ _ (fun y _ => twist_bond_labels G P κ hpair y) hlay

/-- Off the four exceptional incidences the twist dart map is the naive carrier transport. -/
theorem twistDartEquiv_eq_naive {G : Garden w} (P : CorePlacement G) (y : GardenDart G)
    (hpc : ∀ s, y ≠ lowerPC G P s) (hlp : y ≠ retainedLP G P) (hlp' : y ≠ G.molecule.mate (retainedLP G P)) :
    twistDartEquiv G P y = naiveDartEquiv G P y := by
  change naiveDartEquiv G P (exceptionalDartSwap G P y) = _
  congr 1
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    refine exceptionalDartSwap_otherPC G P c (fun hc => hpc s ?_) s
    have he : c = ⟨P.lower, P.nonroot⟩ := Subtype.ext hc
    subst he
    rfl
  | inr l =>
    refine exceptionalDartSwap_otherLP G P l (fun hl => hlp ?_) (fun hp => hlp' ?_)
    · have he : l = ⟨P.retained, P.unmarked, retained_nonroot G P, P.paired_nonroot⟩ := Subtype.ext hl
      subst he
      rfl
    · change Sum.inr l = Sum.inr _
      apply congrArg Sum.inr
      exact Subtype.ext hp

/-- The naive carrier transport moves the carried node naively. -/
theorem dartNode_naive {G : Garden w} (P : CorePlacement G) (y : GardenDart G) :
    Mole.dartNode (unitTwistGarden G P) (naiveDartEquiv G P y) = naiveNodeEquiv G P (Mole.dartNode G y) := by
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    change (coreBranchEquiv G P c.1).toNode = naiveNodeEquiv G P c.1.toNode
    rw [naiveNodeEquiv_branch]
  | inr l =>
    change (coreLeafEquiv G P l.1).toNode = naiveNodeEquiv G P l.1.toNode
    rw [naiveNodeEquiv_leaf]

theorem atom_lowerPC_false {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (lowerPC G P false) = P.lower := rfl

theorem atom_lowerPC_true {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (lowerPC G P true) = GNode.parent P.lower.toNode P.nonroot := rfl

theorem mate_lowerPC {G : Garden w} (P : CorePlacement G) (s : Bool) :
    G.molecule.mate (lowerPC G P s) = lowerPC G P (!s) := rfl

theorem atom_retainedLP {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (retainedLP G P) = P.lower :=
  retained_parent G P

/-- **Rigid transport** (an operation at a member below the block): no exceptional bond lies in `U`. -/
theorem bondW_naive (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) {G : Garden w} (P : CorePlacement G)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ) {U : Finset (GBranch G.tree)}
    (hlow : P.lower ∉ U) (κ' : GNode (unitTwistGarden G P).tree → Fin d → ℤ)
    (hlay : ∀ v ∈ U, lay' (coreBranchEquiv G P v) = lay v) :
    bondW ψ L base (unitTwistGarden G P) lay' (twistedAtoms G P U) κ' =
      bondW ψ L base G lay U (fun n => κ' (naiveNodeEquiv G P n)) := by
  refine bondW_transport ψ L base P lay lay' U _ κ' (fun y hy => ?_) hlay
  have hy' := mem_regionDarts.mp hy
  have hpc : ∀ s, y ≠ lowerPC G P s := by
    intro s he
    subst he
    cases s
    · exact hlow hy'.1
    · exact hlow hy'.2
  have hlp : y ≠ retainedLP G P := by
    intro he
    subst he
    exact hlow (atom_retainedLP P ▸ hy'.1)
  have hlp' : y ≠ G.molecule.mate (retainedLP G P) := by
    intro he
    subst he
    have h2 := hy'.2
    rw [G.molecule.mate_mate] at h2
    exact hlow (atom_retainedLP P ▸ h2)
  unfold Mole.restrictLabels
  rw [twistDartEquiv_eq_naive P y hpc hlp hlp', dartNode_naive]

/-- **The lower-block transport** (`K^T` at the member whose lower joint is the top of `T`): the labels are
read through `twNode`. Requires that neither exceptional bond is a bond of `T`. -/
theorem bondW_twNode (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) {G : Garden w} (P : CorePlacement G)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ) {T : Finset (GBranch G.tree)}
    (hpar : GNode.parent P.lower.toNode P.nonroot ∉ T) (hret : ¬ G.molecule.InGroup T (retainedLP G P))
    (κ' : GNode (unitTwistGarden G P).tree → Fin d → ℤ)
    (hlay : ∀ v ∈ T, lay' (coreBranchEquiv G P v) = lay v) :
    bondW ψ L base (unitTwistGarden G P) lay' (twistedAtoms G P T) κ' =
      bondW ψ L base G lay T (fun n => κ' (VineEstS4.twNode P n)) := by
  refine bondW_transport ψ L base P lay lay' T _ κ' (fun y hy => ?_) hlay
  have hy' := mem_regionDarts.mp hy
  have hpc : ∀ s, y ≠ lowerPC G P s := by
    intro s he
    subst he
    cases s
    · exact hpar hy'.2
    · exact hpar hy'.1
  have hlp : y ≠ retainedLP G P := by
    intro he
    subst he
    exact hret hy'
  have hlp' : y ≠ G.molecule.mate (retainedLP G P) := by
    intro he
    subst he
    exact hret ((inGroup_mate_iff _).mp hy')
  have hn : Mole.dartNode G y ≠ P.lower.toNode ∧ Mole.dartNode G y ≠ P.retained.toNode := by
    cases y with
    | inl c =>
      obtain ⟨c, s⟩ := c
      have hc : c.1 ≠ P.lower := by
        intro hc
        have he : c = ⟨P.lower, P.nonroot⟩ := Subtype.ext hc
        subst he
        exact hpc s rfl
      exact ⟨fun h => hc (Mole.branch_toNode_injective h), Mole.branch_toNode_ne_leaf _ _⟩
    | inr l =>
      refine ⟨(Mole.branch_toNode_ne_leaf _ _).symm, fun h => hlp ?_⟩
      have hl : l.1 = P.retained := Mole.leaf_toNode_injective h
      have he : l = ⟨P.retained, P.unmarked, retained_nonroot G P, P.paired_nonroot⟩ := Subtype.ext hl
      subst he
      rfl
  unfold Mole.restrictLabels
  rw [twistDartEquiv_eq_naive P y hpc hlp hlp', dartNode_naive]
  beta_reduce
  rw [VineEstS4.twNode_apply, Equiv.swap_apply_of_ne_of_ne hn.1 hn.2]

end WaveTurbulence.VineSpaceB
