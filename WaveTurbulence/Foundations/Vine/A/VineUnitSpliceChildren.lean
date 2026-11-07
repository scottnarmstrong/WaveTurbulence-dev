/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceNodes
public import WaveTurbulence.Foundations.Molecule.ChildSigns
/-! The actual full node map acts at each surviving branch by a child
permutation fixing the negative middle slot. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- The actual target slot occupied by a surviving source child. -/
noncomputable def unitSpliceChildSlot (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) (i : Fin 3) : Fin 3 :=
  (unitSpliceNodeEquiv Z σ hsel (b.child i)).1.2.getLast
    (fun h => child_nonroot (stSt G σ).G b i ((unitSpliceNodeEquiv_root Z σ hsel (b.child i)).mp h))

/-- Every actual mapped child is the target branch's child at the corresponding slot. -/
theorem unitSpliceNodeEquiv_child (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) (i : Fin 3) :
    unitSpliceNodeEquiv Z σ hsel (b.child i) = ((unitSpliceMolIso Z σ hsel).e b).child (unitSpliceChildSlot Z σ hsel b i) := by
  have hn := child_nonroot (stSt G σ).G b i
  have hm : (unitSpliceNodeEquiv Z σ hsel (b.child i)).1.2 ≠ [] :=
    fun h => hn ((unitSpliceNodeEquiv_root Z σ hsel (b.child i)).mp h)
  have hp0 : GNode.parent (b.child i) hn = b := by
    apply Subtype.ext
    change (b.1.1, (b.1.2 ++ [i]).dropLast) = b.1
    rw [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
  have hp : GNode.parent (unitSpliceNodeEquiv Z σ hsel (b.child i)) hm = (unitSpliceMolIso Z σ hsel).e b :=
    (unitSpliceNodeEquiv_parent Z σ hsel (b.child i) hn).symm.trans
      (congrArg (unitSpliceMolIso Z σ hsel).e hp0)
  exact (parent_child_eq_node (unitSpliceNodeEquiv Z σ hsel (b.child i)) hm).symm.trans
    (congrArg (fun a => a.child (unitSpliceChildSlot Z σ hsel b i)) hp)

/-- Distinct source child slots occupy distinct actual target child slots. -/
theorem unitSpliceChildSlot_injective (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    Function.Injective (unitSpliceChildSlot Z σ hsel b) := by
  intro i j hij
  apply Molecpl.child_injective (stSt G σ).G b
  apply (unitSpliceNodeEquiv Z σ hsel).injective
  exact (unitSpliceNodeEquiv_child Z σ hsel b i).trans
    ((congrArg ((unitSpliceMolIso Z σ hsel).e b).child hij).trans
      (unitSpliceNodeEquiv_child Z σ hsel b j).symm)

/-- The actual map on the three children is a permutation. -/
noncomputable def unitSpliceChildEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (unitSpliceChildSlot Z σ hsel b)
    ⟨unitSpliceChildSlot_injective Z σ hsel b, Finite.surjective_of_injective (unitSpliceChildSlot_injective Z σ hsel b)⟩

/-- The actual child permutation fixes the negative middle child. -/
theorem unitSpliceChildSlot_middle (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    unitSpliceChildSlot Z σ hsel b 1 = 1 := by
  let H := (stSt Z.target (transportPrescription Z.iso σ)).G
  let c := (unitSpliceMolIso Z σ hsel).e b
  have hs : H.sign (c.child (unitSpliceChildSlot Z σ hsel b 1)) = -H.sign c.toNode :=
    (congrArg H.sign (unitSpliceNodeEquiv_child Z σ hsel b 1)).symm.trans
      ((unitSpliceNodeEquiv_sign Z σ hsel (b.child 1)).trans
        ((Molecpl.child_signs (stSt G σ).G b).2.1.trans
          (congrArg Neg.neg (unitSpliceMolIso_branch_sign Z σ hsel b).symm)))
  have hne : H.sign c.toNode ≠ -H.sign c.toNode := by
    rcases Int.units_eq_one_or (H.sign c.toNode) with h | h
    · rw [h]; decide
    · rw [h]; decide
  generalize unitSpliceChildSlot Z σ hsel b 1 = k at hs ⊢
  fin_cases k
  · exact (hne ((Molecpl.child_signs H c).1.symm.trans hs)).elim
  · rfl
  · exact (hne ((Molecpl.child_signs H c).2.2.symm.trans hs)).elim

end WaveTurbulence.VineA
