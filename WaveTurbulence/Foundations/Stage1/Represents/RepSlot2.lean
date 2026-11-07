/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot1
public import WaveTurbulence.Foundations.Stage1.Represents.RepTime
import Mathlib.Tactic

/-!
# S2 REPRESENTS: replacement slots of the skeleton, their clocks, momentum nodes and bonds
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed

variable {w : ℕ} (S : Garden w)

/-- Clock sources: a root time `tt j` or a branch time `τ b`. -/
abbrev ClkSrc : Type := Fin w ⊕ GBranch S.tree

/-- The clock source of the parent clock of a node. -/
def clkOfNode (ν : GNode S.tree) : ClkSrc S :=
  match nodeToSlot ν with
  | .inl j => .inl j
  | .inr (b, _) => .inr b

def clockOf (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) : ClkSrc S → ℝ := Sum.elim tt τ

theorem parentClockWith_eq_clockOf (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (ν : GNode S.tree) :
    parentClockWith tt τ ν = clockOf S tt τ (clkOfNode S ν) := by
  unfold parentClockWith clkOfNode clockOf
  rcases nodeToSlot ν with j | ⟨b, i⟩ <;> rfl

variable {S}

/-- The node whose momentum is the argument of the slot kernel. -/
def slotNode (hS : S.IsPlain) : ReplacementSlot S → GNode S.tree
  | .inl p => (p.firstLeaf hS).toNode
  | .inr b => b.toNode

/-- The clock sources of the two time arguments of the slot kernel. -/
def argSrc (hS : S.IsPlain) : ReplacementSlot S → Fin 2 → ClkSrc S
  | .inl p, i => if i = 0 then clkOfNode S (p.firstLeaf hS).toNode else clkOfNode S (p.secondLeaf hS).toNode
  | .inr b, i => if i = 0 then clkOfNode S b.toNode else .inr b


theorem pair_second (hS : S.IsPlain) (p : SourcePair S) : S.pair (p.secondLeaf hS) = p.firstLeaf hS := by
  have h := pairOfLeaf_sides_neg S hS (p.secondLeaf hS)
    (by rw [sourcePair_second_sign]; decide)
  rw [pairOfLeaf_secondLeaf] at h
  exact h.1.symm

/-- Whether the slot kernel carries a molecule bond (not when a root leaf or a root branch is involved). -/
def hasBond (hS : S.IsPlain) : ReplacementSlot S → Prop
  | .inl p => (p.firstLeaf hS).1.2 ≠ [] ∧ (p.secondLeaf hS).1.2 ≠ []
  | .inr b => b.1.2 ≠ []

/-- The outgoing dart of the bond of a slot. -/
def dartOfSlot (hS : S.IsPlain) : (s : ReplacementSlot S) → hasBond hS s → GardenDart S
  | .inl p, h => .inr ⟨p.secondLeaf hS, ⟨hS _, h.2, by rw [pair_second]; exact h.1⟩⟩
  | .inr b, h => .inl (⟨b, h⟩, decide (S.sign b.toNode ≠ 1))

/-- The slot of a dart. -/
def slotOfDart (hS : S.IsPlain) : GardenDart S → ReplacementSlot S
  | .inl (c, _) => .inr c.1
  | .inr ℓ => .inl (pairOfLeaf S hS ℓ.1)

theorem slotOfDart_dartOfSlot (hS : S.IsPlain) (s : ReplacementSlot S) (h : hasBond hS s) :
    slotOfDart hS (dartOfSlot hS s h) = s := by
  rcases s with p | b
  · simp only [dartOfSlot, slotOfDart]
    rw [pairOfLeaf_secondLeaf]
  · rfl

theorem slotOfDart_mate (hS : S.IsPlain) (x : GardenDart S) :
    slotOfDart hS (S.molecule.mate x) = slotOfDart hS x := by
  rcases x with ⟨c, b⟩ | ℓ
  · rfl
  · simp only [Garden.molecule, slotOfDart]
    rw [pairOfLeaf_partner]

theorem out_dartOfSlot (hS : S.IsPlain) (s : ReplacementSlot S) (h : hasBond hS s) :
    S.molecule.out (dartOfSlot hS s h) = true := by
  rcases s with p | b
  · simp only [dartOfSlot, Garden.molecule]
    have : S.sign (p.secondLeaf hS).toNode = -1 := sourcePair_second_sign S hS p
    simp [this]
  · simp only [dartOfSlot, Garden.molecule]
    by_cases hb : S.sign b.toNode = 1
    · simp [hb]
    · simp [hb]

theorem dartOfSlot_slotOfDart (hS : S.IsPlain) (x : GardenDart S) (hx : S.molecule.out x = true) :
    ∃ h : hasBond hS (slotOfDart hS x), dartOfSlot hS (slotOfDart hS x) h = x := by
  rcases x with ⟨c, b⟩ | ℓ
  · refine ⟨c.2, ?_⟩
    simp only [dartOfSlot, slotOfDart]
    congr 1
    simp only [Garden.molecule] at hx
    cases b <;> simp at hx ⊢ <;> simp [hx]
  · have hsn : S.sign ℓ.1.toNode ≠ 1 := by
      simpa [Garden.molecule] using hx
    have h2 := pairOfLeaf_second_of_negative S hS ℓ.1 hsn
    have h1 := pairOfLeaf_sides_neg S hS ℓ.1 hsn
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((pairOfLeaf S hS ℓ.1).firstLeaf hS).1.2 ≠ []
      rw [h1.1]; exact ℓ.2.2.2
    · show ((pairOfLeaf S hS ℓ.1).secondLeaf hS).1.2 ≠ []
      rw [h2]; exact ℓ.2.2.1
    · simp only [dartOfSlot, slotOfDart]
      congr 1
      exact Subtype.ext h2

theorem bondIndex_eq_slotNode (hS : S.IsPlain) {d : ℕ} (z : GNode S.tree → (Fin d → ℤ))
    (hz : ∀ ℓ : GLeaf S.tree, z ℓ.toNode = z (S.pair ℓ).toNode) (x : GardenDart S) :
    bondIndex S z x = z (slotNode hS (slotOfDart hS x)) := by
  rcases x with ⟨c, b⟩ | ℓ
  · rfl
  · simp only [bondIndex, slotOfDart, slotNode]
    by_cases hsn : nodeSign S.sig ℓ.1.1 = 1
    · have := pairOfLeaf_first_of_positive S hS ℓ.1 hsn
      rw [this]
    · have h1 := (pairOfLeaf_sides_neg S hS ℓ.1 hsn).1
      rw [h1]
      exact hz ℓ.1


open scoped Classical in
theorem prod_bonds_eq (hS : S.IsPlain) {M : Type*} [CommMonoid M] (g : ReplacementSlot S → M) :
    ∏ x ∈ S.molecule.bonds, g (slotOfDart hS x) =
      ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), g s := by
  have hmem : ∀ x, x ∈ S.molecule.bonds ↔ S.molecule.out x = true := by
    intro x; simp [Molecule.bonds]
  refine Finset.prod_nbij (slotOfDart hS) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    (fun s hs => ?_) (fun x _ => rfl)
  · obtain ⟨h, -⟩ := dartOfSlot_slotOfDart hS x ((hmem x).1 hx)
    simpa using h
  · obtain ⟨h1, e1⟩ := dartOfSlot_slotOfDart hS x ((hmem x).1 hx)
    obtain ⟨h2, e2⟩ := dartOfSlot_slotOfDart hS y ((hmem y).1 hy)
    rw [← e1, ← e2]
    congr 1
  · have hs' : hasBond hS s := by simpa using hs
    refine ⟨dartOfSlot hS s hs', ?_, slotOfDart_dartOfSlot hS s hs'⟩
    simp only [Finset.mem_coe]
    exact (hmem _).2 (out_dartOfSlot hS s hs')

end WaveTurbulence.Represents
