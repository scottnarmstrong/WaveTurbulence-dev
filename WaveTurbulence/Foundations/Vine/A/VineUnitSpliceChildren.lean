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

/-- B1b-2 (Mk-general form of `unitSpliceChildSlot`). -/
noncomputable def unitSpliceChildSlotMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) (i : Fin 3) : Fin 3 :=
  (unitSpliceNodeEquivMk Z σ hT hsel (b.child i)).1.2.getLast
    (fun h => child_nonroot (stSt G σ Mk).G b i ((unitSpliceNodeEquiv_rootMk Z σ hT hsel (b.child i)).mp h))

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_child`). -/
theorem unitSpliceNodeEquiv_childMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) (i : Fin 3) :
    unitSpliceNodeEquivMk Z σ hT hsel (b.child i) = ((unitSpliceMolIsoMk Z σ hT hsel).e b).child (unitSpliceChildSlotMk Z σ hT hsel b i) := by
  have hn := child_nonroot (stSt G σ Mk).G b i
  have hm : (unitSpliceNodeEquivMk Z σ hT hsel (b.child i)).1.2 ≠ [] :=
    fun h => hn ((unitSpliceNodeEquiv_rootMk Z σ hT hsel (b.child i)).mp h)
  have hp0 : GNode.parent (b.child i) hn = b := by
    apply Subtype.ext
    change (b.1.1, (b.1.2 ++ [i]).dropLast) = b.1
    rw [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
  have hp : GNode.parent (unitSpliceNodeEquivMk Z σ hT hsel (b.child i)) hm = (unitSpliceMolIsoMk Z σ hT hsel).e b :=
    (unitSpliceNodeEquiv_parentMk Z σ hT hsel (b.child i) hn).symm.trans
      (congrArg (unitSpliceMolIsoMk Z σ hT hsel).e hp0)
  exact (parent_child_eq_node (unitSpliceNodeEquivMk Z σ hT hsel (b.child i)) hm).symm.trans
    (congrArg (fun a => a.child (unitSpliceChildSlotMk Z σ hT hsel b i)) hp)

/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_injective`). -/
theorem unitSpliceChildSlot_injectiveMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) :
    Function.Injective (unitSpliceChildSlotMk Z σ hT hsel b) := by
  intro i j hij
  apply Molecpl.child_injective (stSt G σ Mk).G b
  apply (unitSpliceNodeEquivMk Z σ hT hsel).injective
  exact (unitSpliceNodeEquiv_childMk Z σ hT hsel b i).trans
    ((congrArg ((unitSpliceMolIsoMk Z σ hT hsel).e b).child hij).trans
      (unitSpliceNodeEquiv_childMk Z σ hT hsel b j).symm)

/-- B1b-2 (Mk-general form of `unitSpliceChildEquiv`). -/
noncomputable def unitSpliceChildEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (unitSpliceChildSlotMk Z σ hT hsel b)
    ⟨unitSpliceChildSlot_injectiveMk Z σ hT hsel b, Finite.surjective_of_injective (unitSpliceChildSlot_injectiveMk Z σ hT hsel b)⟩

/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_middle`). -/
theorem unitSpliceChildSlot_middleMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) :
    unitSpliceChildSlotMk Z σ hT hsel b 1 = 1 := by
  let H := (stSt Z.target (transportPrescription Z.iso σ) Mk').G
  let c := (unitSpliceMolIsoMk Z σ hT hsel).e b
  have hs : H.sign (c.child (unitSpliceChildSlotMk Z σ hT hsel b 1)) = -H.sign c.toNode :=
    (congrArg H.sign (unitSpliceNodeEquiv_childMk Z σ hT hsel b 1)).symm.trans
      ((unitSpliceNodeEquiv_signMk Z σ hT hsel (b.child 1)).trans
        ((Molecpl.child_signs (stSt G σ Mk).G b).2.1.trans
          (congrArg Neg.neg (unitSpliceMolIso_branch_signMk Z σ hT hsel b).symm)))
  have hne : H.sign c.toNode ≠ -H.sign c.toNode := by
    rcases Int.units_eq_one_or (H.sign c.toNode) with h | h
    · rw [h]; decide
    · rw [h]; decide
  generalize unitSpliceChildSlotMk Z σ hT hsel b 1 = k at hs ⊢
  fin_cases k
  · exact (hne ((Molecpl.child_signs H c).1.symm.trans hs)).elim
  · rfl
  · exact (hne ((Molecpl.child_signs H c).2.2.symm.trans hs)).elim

end WaveTurbulence.VineA
