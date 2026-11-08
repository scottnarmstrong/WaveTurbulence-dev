/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Path
public import WaveTurbulence.Foundations.Flower.MkMark.TwistStep

/-! # CAPS-STABLE: where an LF operation acts, seen from an unmarked vertex

Let `𝕍` be a core (CL) vine of the skeleton `S` with upper joint `a`, atoms `A` and placement `P` (lower joint
`u₂ = P.lower`, retained leaf `u₂₃`, partner `u₀`). An LF operation at `𝕍` replaces the region `R` of addresses owned
by `{u₂, u₂₃, u₀}` (`replacedNodes P`). Let `κ` be the hole of `a` (the inflated position of `a` followed by the lone
path of its regular tree), the address below which all children of `a` hang.

* `below_hole`: every address of `R` lies below `κ`;
* `addrBelow_hole`: an address `z` whose owner is neither replaced nor a non-upper atom of `𝕍`, and which lies above
  some address of `R`, lies above `κ`.

Hence such a `z` lies either above all of `R` or above none of it (`dichotomy`). This is the geometric content of
o75 Lemma 2(b) (proof L248–262): the realization of a (CL) vine is the pruned subtree below `u₁`
(`Mole.cl_branch_realization_iff`), so every skeleton node strictly between `u₁` and a replaced node is an atom. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.Links

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

section Skel
variable {S : Garden w}

theorem isDesc_trans {a b c : GNode S.tree} (h1 : a.IsDesc b) (h2 : b.IsDesc c) : a.IsDesc c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem isDesc_child (b : GBranch S.tree) (i : Fin 3) : b.toNode.IsDesc (b.child i) :=
  ⟨rfl, List.prefix_append _ _⟩

/-- Two ancestors of one node are comparable. -/
theorem isDesc_total {a b c : GNode S.tree} (ha : a.IsDesc c) (hb : b.IsDesc c) : a.IsDesc b ∨ b.IsDesc a := by
  rcases List.prefix_or_prefix_of_prefix ha.2 hb.2 with h | h
  · exact Or.inl ⟨ha.1.trans hb.1.symm, h⟩
  · exact Or.inr ⟨hb.1.trans ha.1.symm, h⟩

theorem gnode_eq_of_isDesc {a b : GNode S.tree} (h : a.IsDesc b) (hl : b.1.2.length ≤ a.1.2.length) : a = b :=
  Subtype.ext (Prod.ext h.1 (h.2.eq_of_length (le_antisymm h.2.length_le hl)))

/-- A proper ancestor of a branch is below one of its children. -/
theorem exists_child_isDesc (b : GBranch S.tree) {o : GNode S.tree} (h : b.toNode.IsDesc o) (hne : b.toNode ≠ o) :
    ∃ i : Fin 3, (b.child i).IsDesc o := by
  obtain ⟨h1, r, hr⟩ := h
  cases r with
  | nil =>
    exact absurd (Subtype.ext (Prod.ext h1 (by simpa using hr))) hne
  | cons i r =>
    refine ⟨i, h1, r, ?_⟩
    show b.1.2 ++ [i] ++ r = o.1.2
    rw [← hr, List.append_assoc, List.singleton_append]
    rfl

/-- A node with a proper descendant is a branching node. -/
theorem branching_of_isDesc {o c : GNode S.tree} (h : o.IsDesc c) (hne : o ≠ c) :
    o.1.2 ∈ (S.tree o.1.1).branching := by
  obtain ⟨h1, r, hr⟩ := h
  cases r with
  | nil => exact absurd (Subtype.ext (Prod.ext h1 (by simpa using hr))) hne
  | cons i r =>
    have hc : o.1.2 ++ [i] ∈ (S.tree o.1.1).nodes := by
      have h2 := c.2
      rw [← h1] at h2
      exact TTree.mem_nodes_of_prefix _ h2 ⟨r, by rw [← hr]; simp⟩
    exact TTree.branching_of_append_mem _ hc

end Skel

section Vine
variable {S : Garden w} (P : CorePlacement S) {Xv : VineType} {A : Finset (GBranch S.tree)} {a : GBranch S.tree}
  (hcore : IsCoreCLVine S Xv A a P.lower) (hP : IsPlacementAt S A P.lower P)
include hcore

theorem upper_isDesc_lower : a.toNode.IsDesc P.lower.toNode ∧ a.1.2.length < P.lower.1.2.length :=
  Mole.cl_parent_strict_descendant S hcore.1.1 hcore.2.1

theorem lower_pruned : Mole.InCLPrunedRegion S A a P.lower P.lower.toNode :=
  (Mole.cl_branch_realization_iff S hcore.1.1 hcore.2.1 P.lower).mp hcore.1.1.2.2.1

include hP in
theorem pair_pruned : Mole.InCLPrunedRegion S A a P.lower (S.pair P.retained).toNode :=
  (Mole.cl_leaf_realization_iff S hcore.1.1 hcore.2.1 _).mp
    ((Mole.leaf_incidence_realization_iff S A _).mp (placement_pair_in_realization S P hcore.1.1 hP))

include hP in
theorem retained_pruned : Mole.InCLPrunedRegion S A a P.lower P.retained.toNode := by
  have hl := lower_pruned P hcore
  obtain ⟨hal, hlen⟩ := upper_isDesc_lower P hcore
  have hlr : P.lower.toNode.IsDesc P.retained.toNode := by rw [P.child]; exact isDesc_child _ _
  refine ⟨isDesc_trans hal hlr, ?_⟩
  intro j hj i hi hd
  rcases Finset.mem_insert.mp hj with hja | hj
  · -- `a.child i` is above `u₂₃`, hence above `u₂`
    rw [hja] at hd hi
    have hlen' : (a.child i).1.2.length ≤ P.lower.toNode.1.2.length := by
      simp only [GBranch.child, GBranch.toNode, List.length_append, List.length_singleton]
      omega
    have hcl : (a.child i).IsDesc P.lower.toNode :=
      ⟨hd.1.trans hlr.1.symm, List.prefix_of_prefix_length_le hd.2 hlr.2 hlen'⟩
    exact hl.2 a (Finset.mem_insert_self _ _) i hi hcl
  · rw [Finset.mem_singleton] at hj
    rw [hj] at hd hi
    have he : P.lower.child i = P.lower.child P.keep := by
      rw [← P.child]
      exact gnode_eq_of_isDesc hd (by rw [P.child]; simp [GBranch.child])
    have hik : i = P.keep := by
      have := congrArg (fun x : GNode S.tree => x.1.2.getLast?) he
      simpa [GBranch.child] using this
    exact hi ((hP.2 i).mpr hik)

include hP in
theorem replaced_pruned {o : GNode S.tree} (ho : o ∈ replacedNodes P) : Mole.InCLPrunedRegion S A a P.lower o := by
  rcases (mem_replacedNodes P o).mp ho with rfl | rfl | rfl
  · exact lower_pruned P hcore
  · exact retained_pruned P hcore hP
  · exact pair_pruned P hcore hP

theorem replaced_ne_upper {o : GNode S.tree} (ho : o ∈ replacedNodes P) : o ≠ a.toNode := by
  rcases (mem_replacedNodes P o).mp ho with rfl | rfl | rfl
  · intro h
    have h1 := (upper_isDesc_lower P hcore).2
    have h2 : P.lower.1.2.length = a.1.2.length := congrArg (fun x : GNode S.tree => x.1.2.length) h
    omega
  · exact leaf_ne_branch _ _
  · exact leaf_ne_branch _ _

/-- A node strictly between the upper joint and a pruned node is an atom. -/
theorem mem_atoms_of_between {o c : GNode S.tree} (hc : Mole.InCLPrunedRegion S A a P.lower c)
    (hao : a.toNode.IsDesc o) (hoc : o.IsDesc c) (hne : o ≠ c) :
    ∃ b ∈ A, b.toNode = o := by
  have hbr := branching_of_isDesc hoc hne
  let b : GBranch S.tree := ⟨o.1, hbr⟩
  refine ⟨b, ?_, rfl⟩
  apply (Mole.cl_branch_realization_iff S hcore.1.1 hcore.2.1 b).mpr
  exact ⟨hao, fun j hj i hi hd => hc.2 j hj i hi (isDesc_trans hd hoc)⟩

end Vine

/-! ## The hole of the upper joint -/

section Hole
variable {S : Garden w} (X : GBranch S.tree → RegChain)

/-- The hole of a branch: below it hang the regions of its children. -/
def holeAddr (b : GBranch S.tree) : Address w := addrExt (inflatedPosition S X b.toNode) (X b).lonePath

theorem holeAddr_child (b : GBranch S.tree) (i : Fin 3) :
    inflatedPosition S X (b.child i) = addrExt (holeAddr X b) [i] := by
  rw [inflatedPosition_child, holeAddr, addrExt_append]

theorem addrBelow_addrExt' (z : Address w) (q : TTree.Path) : AddrBelow z (addrExt z q) :=
  ⟨rfl, List.prefix_append _ _⟩

/-- An address below a proper descendant of `b` lies below the hole of `b`. -/
theorem holeAddr_below {b : GBranch S.tree} {o : GNode S.tree} (h : b.toNode.IsDesc o) (hne : b.toNode ≠ o)
    {y : Address w} (hy : AddrBelow (inflatedPosition S X o) y) : AddrBelow (holeAddr X b) y := by
  obtain ⟨i, hi⟩ := exists_child_isDesc b h hne
  have h1 := addrBelow_inflatedPosition S X hi
  rw [holeAddr_child] at h1
  exact addrBelow_trans (addrBelow_addrExt' _ _) (addrBelow_trans h1 hy)

end Hole

section Key
variable {S : Garden w} (X : GBranch S.tree → RegChain) (P : CorePlacement S) {Xv : VineType}
  {A : Finset (GBranch S.tree)} {a : GBranch S.tree}
  (hcore : IsCoreCLVine S Xv A a P.lower) (hP : IsPlacementAt S A P.lower P)
include hcore hP

/-- **Every replaced address lies below the hole of the upper joint.** -/
theorem below_hole {y : Address w} (hy : y ∈ ownedBy S X (replacedNodes P)) : AddrBelow (holeAddr X a) y := by
  have ho : owner S X y ∈ replacedNodes P := hy
  have hpr := replaced_pruned P hcore hP ho
  exact holeAddr_below X hpr.1 (replaced_ne_upper P hcore ho).symm (mem_ownRegion_owner S X y).1

/-- **An unmarked address above a replaced address lies above the hole of the upper joint.** -/
theorem addrBelow_hole {z y : Address w} (hzR : owner S X z ∉ replacedNodes P)
    (hU : ∀ c ∈ A, c ≠ a → owner S X z ≠ c.toNode)
    (hy : y ∈ ownedBy S X (replacedNodes P)) (hzy : AddrBelow z y) : AddrBelow z (holeAddr X a) := by
  have hoy : owner S X y ∈ replacedNodes P := hy
  have hpr := replaced_pruned P hcore hP hoy
  have hzo := owner_isDesc_of_addrBelow S X hzy
  have hκy := below_hole X P hcore hP hy
  have key : (owner S X z).IsDesc a.toNode → AddrBelow z (holeAddr X a) := by
    intro hoa
    rcases List.prefix_or_prefix_of_prefix hzy.2 hκy.2 with h | h
    · exact ⟨hzy.1.trans hκy.1.symm, h⟩
    · obtain ⟨r, hr⟩ := h
      cases r with
      | nil => exact ⟨hzy.1.trans hκy.1.symm, by simp [← hr]⟩
      | cons i r =>
        exfalso
        have hb : AddrBelow (inflatedPosition S X (a.child i)) z := by
          rw [holeAddr_child]
          refine ⟨hκy.1.trans hzy.1.symm, r, ?_⟩
          show (holeAddr X a).2 ++ [i] ++ r = z.2
          rw [← hr]
          simp
        have hd := owner_isDesc_of_addrBelow S X hb
        rw [owner_inflatedPosition] at hd
        have := (isDesc_trans hd hoa).2.length_le
        simp [GBranch.child, GBranch.toNode] at this
  rcases isDesc_total hpr.1 hzo with hao | hoa
  · by_cases he : a.toNode = owner S X z
    · exact key (by rw [← he]; exact ⟨rfl, List.prefix_refl _⟩)
    · exfalso
      have hne : owner S X z ≠ owner S X y := fun h => hzR (h ▸ hoy)
      obtain ⟨b, hb, hbo⟩ := mem_atoms_of_between P hcore hpr hao hzo hne
      exact hU b hb (fun h => he (by rw [← hbo, h])) hbo.symm
  · exact key hoa

/-- **The dichotomy.** An unmarked unreplaced address lies above all of `R` or above none of it. -/
theorem dichotomy {z : Address w} (hzR : owner S X z ∉ replacedNodes P)
    (hU : ∀ c ∈ A, c ≠ a → owner S X z ≠ c.toNode) :
    (AddrBelow z (holeAddr X a) ∧ ∀ y ∈ ownedBy S X (replacedNodes P), AddrBelow z y) ∨
      (∀ y ∈ ownedBy S X (replacedNodes P), ¬ AddrBelow z y) := by
  by_cases h : AddrBelow z (holeAddr X a)
  · exact Or.inl ⟨h, fun y hy => addrBelow_trans h (below_hole X P hcore hP hy)⟩
  · exact Or.inr fun y hy hzy => h (addrBelow_hole X P hcore hP hzR hU hy hzy)

end Key

end WaveTurbulence.Flower.CapsStable
