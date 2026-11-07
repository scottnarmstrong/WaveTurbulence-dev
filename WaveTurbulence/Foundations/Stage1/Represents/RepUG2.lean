/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.Vine.B.Src4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (2): external darts of a unit sit on its boundary nodes

`dartNode`: the node carrying the bond of a dart (`bondIndex G z x = z (dartNode G x)`).  An external dart of a unit
`u` at its upper joint sits on `u1` or `u11` (boundary nodes `0, 1`), at its lower joint on `u21` or `u22` (nodes `2, 3`);
two distinct external darts at one joint sit on the two boundary nodes of the joint.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine

variable {w : ℕ} {S : Garden w}

/-- The node carrying the bond of a dart. -/
def dartNode (G : Garden w) : GardenDart G → GNode G.tree
  | .inl (c, _) => c.1.toNode
  | .inr l => l.1.toNode

theorem bondIndex_eq_dartNode {d : ℕ} (G : Garden w) (z : GNode G.tree → (Fin d → ℤ)) (x : GardenDart G) :
    bondIndex G z x = z (dartNode G x) := by
  cases x <;> rfl

theorem parent_ne_self (c : {c : GBranch S.tree // c.1.2 ≠ []}) :
    GNode.parent c.1.toNode c.2 ≠ c.1 := by
  intro h
  have h1 := congrArg (fun b : GBranch S.tree => b.1.2.length) h
  have h2 : c.1.1.2.length ≠ 0 := fun h0 => c.2 (List.length_eq_zero_iff.mp h0)
  simp only [GNode.parent, GBranch.toNode, List.length_dropLast] at h1
  omega

theorem dartNode_inj_of_atom (x y : GardenDart S) (h : S.molecule.atom x = S.molecule.atom y)
    (hn : dartNode S x = dartNode S y) : x = y := by
  rcases x with ⟨c, b⟩ | l <;> rcases y with ⟨c', b'⟩ | l'
  · have hc : c = c' := Subtype.ext (branch_toNode_injective hn)
    subst hc
    cases b <;> cases b'
    · rfl
    · exact absurd h.symm (parent_ne_self c)
    · exact absurd h (parent_ne_self c)
    · rfl
  · exact absurd hn (branch_toNode_ne_leaf _ _)
  · exact absurd hn.symm (branch_toNode_ne_leaf _ _)
  · have : l = l' := Subtype.ext (leaf_toNode_injective hn)
    rw [this]

/-- The boundary nodes of a unit. -/
noncomputable abbrev bnodes (u : CLBlock S) : Fin 4 → GNode S.tree := clBoundaryNodes (regionOf u)

/-- **An external dart of a unit sits on a boundary node of its joint.** -/
theorem extDart_node (u : CLBlock S) (x : GardenDart S) (hx : S.molecule.atom x ∈ u.atoms)
    (hn : ¬ S.molecule.InGroup u.atoms x) :
    (S.molecule.atom x = u.upper ∧ (dartNode S x = bnodes u 0 ∨ dartNode S x = bnodes u 1)) ∨
      (S.molecule.atom x = u.lower ∧ (dartNode S x = bnodes u 2 ∨ dartNode S x = bnodes u 3)) := by
  have hm : S.molecule.atom (S.molecule.mate x) ∉ u.atoms := fun h => hn ⟨hx, h⟩
  have key : ∀ (v : GBranch S.tree) (n : GNode S.tree) (hv : v ∈ u.atoms) (hnr : n.1.2 ≠ []),
      GNode.parent n hnr = v → n ∉ clRealizationNodes S u.atoms →
      (v = u.upper ∧ (n = bnodes u 0 ∨ n = bnodes u 1)) ∨ (v = u.lower ∧ (n = bnodes u 2 ∨ n = bnodes u 3)) := by
    intro v n hv hnr hp hnreal
    obtain ⟨i, hi⟩ := child_parent n hnr
    rw [hp] at hi
    rw [← hi] at hnreal
    rcases ext_child u hv i hnreal with ⟨rfl, rfl⟩ | ⟨rfl, h | h⟩
    · exact Or.inl ⟨rfl, Or.inr (by rw [← hi]; rfl)⟩
    · exact Or.inr ⟨rfl, Or.inl (by rw [← hi, h]; rfl)⟩
    · exact Or.inr ⟨rfl, Or.inr (by rw [← hi, h]; rfl)⟩
  rcases x with ⟨c, b⟩ | l
  · cases b
    · -- the dart at the child end of its bond: parent bond of the atom `c`
      change c.1 ∈ u.atoms at hx
      change GNode.parent c.1.toNode c.2 ∉ u.atoms at hm
      have hup : c.1 = u.upper := by
        by_contra hne
        obtain ⟨hn', hp⟩ := real_parent u ((branch_real_iff u c.1).mpr hx)
          (fun h => hne (branch_toNode_injective h))
        exact hm hp
      exact Or.inl ⟨hup, Or.inl (by show c.1.toNode = _; rw [hup]; rfl)⟩
    · change GNode.parent c.1.toNode c.2 ∈ u.atoms at hx
      change c.1 ∉ u.atoms at hm
      have := key _ c.1.toNode hx c.2 rfl (fun h => hm ((branch_real_iff u c.1).mp h))
      simpa [dartNode, Garden.molecule] using this
  · change GNode.parent l.1.toNode l.2.2.1 ∈ u.atoms at hx
    have hnl : l.1.toNode ∉ clRealizationNodes S u.atoms := by
      intro h
      obtain ⟨hm', hn', hp', hg⟩ := (leaf_mem_clRealizationNodes l.1).mp h
      exact hn hg
    have := key _ l.1.toNode hx l.2.2.1 rfl hnl
    simpa [dartNode, Garden.molecule] using this

/-- Two distinct external darts at one joint sit on the two boundary nodes of the joint. -/
theorem extPair_nodes (u : CLBlock S) {x y : GardenDart S} {j : GBranch S.tree} (hj : j = u.upper ∨ j = u.lower)
    (hx : S.molecule.atom x = j) (hy : S.molecule.atom y = j) (hxn : ¬ S.molecule.InGroup u.atoms x)
    (hyn : ¬ S.molecule.InGroup u.atoms y) (hxy : x ≠ y) :
    (j = u.upper ∧ ((dartNode S x = bnodes u 0 ∧ dartNode S y = bnodes u 1) ∨
        (dartNode S x = bnodes u 1 ∧ dartNode S y = bnodes u 0))) ∨
      (j = u.lower ∧ ((dartNode S x = bnodes u 2 ∧ dartNode S y = bnodes u 3) ∨
        (dartNode S x = bnodes u 3 ∧ dartNode S y = bnodes u 2))) := by
  have hjm : j ∈ u.atoms := by rcases hj with rfl | rfl; exact u.isBlock.2.1; exact u.isBlock.2.2.1
  have hab : u.upper ≠ u.lower := u.isBlock.2.2.2.1
  have hne : dartNode S x ≠ dartNode S y := fun h => hxy (dartNode_inj_of_atom x y (hx.trans hy.symm) h)
  have h1 := extDart_node u x (hx ▸ hjm) hxn
  have h2 := extDart_node u y (hy ▸ hjm) hyn
  rw [hx] at h1
  rw [hy] at h2
  rcases h1 with ⟨e1, a1 | a1⟩ | ⟨e1, a1 | a1⟩ <;> rcases h2 with ⟨e2, a2 | a2⟩ | ⟨e2, a2 | a2⟩
  all_goals first
    | (exfalso; exact hab (e1.symm.trans e2))
    | (exfalso; exact hab (e2.symm.trans e1))
    | (exfalso; exact hne (a1.trans a2.symm))
    | skip
  · exact Or.inl ⟨e1, Or.inl ⟨a1, a2⟩⟩
  · exact Or.inl ⟨e1, Or.inr ⟨a1, a2⟩⟩
  · exact Or.inr ⟨e1, Or.inl ⟨a1, a2⟩⟩
  · exact Or.inr ⟨e1, Or.inr ⟨a1, a2⟩⟩

end WaveTurbulence.Represents
