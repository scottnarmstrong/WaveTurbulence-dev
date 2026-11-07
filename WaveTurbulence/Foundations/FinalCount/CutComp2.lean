/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutComponents
/-! Component count of a cut, part 2 (FINALCOUNT-G2 step 1). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The identification `v₂ ↦ v`. -/
def piV (v v₂ a : V) : V := if a = v₂ then v else a

theorem cutAdj_pi (hcd : M.IsCutData v v₂ x₁ x₂) {a b : V} (h : (M.cut v v₂ x₁ x₂).Adj a b) :
    M.Adj (piV v v₂ a) (piV v v₂ b) := by
  obtain ⟨z, hz1, hz2⟩ := h
  have key : ∀ y, piV v v₂ ((M.cut v v₂ x₁ x₂).atom y) = M.atom y := by
    intro y
    rw [cut_atom]
    unfold piV
    split_ifs with h1 h2 h2
    · exact h1.1.symm
    · exact absurd rfl h2
    · exact absurd h2 (fun e => hcd.2.1 (e ▸ M.atom_mem y))
    · rfl
  refine ⟨z, ?_, ?_⟩
  · rw [← key z, hz1]
  · have := key (M.mate z)
    rw [← this]
    have e : (M.cut v v₂ x₁ x₂).atom (M.mate z) = (M.cut v v₂ x₁ x₂).atom ((M.cut v v₂ x₁ x₂).mate z) := rfl
    rw [e, hz2]

theorem cutSC_pi (hcd : M.IsCutData v v₂ x₁ x₂) {a b : V} (h : (M.cut v v₂ x₁ x₂).SameComponent a b) :
    M.SameComponent (piV v v₂ a) (piV v v₂ b) := by
  induction h with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ (cutAdj_pi M hcd h)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Adjacent atoms of `M` are, up to moving `v ↦ v₂`, adjacent in the cut. -/
theorem adj_cut_cases (hcd : M.IsCutData v v₂ x₁ x₂) {a b : V} (h : M.Adj a b) :
    ∃ a' b', (a' = a ∨ (a = v ∧ a' = v₂)) ∧ (b' = b ∨ (b = v ∧ b' = v₂)) ∧
      (M.cut v v₂ x₁ x₂).Adj a' b' := by
  obtain ⟨z, hz1, hz2⟩ := h
  refine ⟨(M.cut v v₂ x₁ x₂).atom z, (M.cut v v₂ x₁ x₂).atom (M.mate z), ?_, ?_, ⟨z, rfl, rfl⟩⟩
  · rw [cut_atom]; split_ifs with h1
    · exact Or.inr ⟨hz1 ▸ h1.1, rfl⟩
    · exact Or.inl hz1
  · rw [cut_atom]; split_ifs with h1
    · exact Or.inr ⟨hz2 ▸ h1.1, rfl⟩
    · exact Or.inl hz2

/-- `CutU a`: `a` is cut-connected to `v` or to `v₂`. -/
def CutU (M : Molecule V D) (v v₂ : V) (x₁ x₂ : D) (a : V) : Prop :=
  (M.cut v v₂ x₁ x₂).SameComponent a v ∨ (M.cut v v₂ x₁ x₂).SameComponent a v₂

theorem CutU_of_sc {a b : V} (h : (M.cut v v₂ x₁ x₂).SameComponent a b) (hb : CutU M v v₂ x₁ x₂ b) :
    CutU M v v₂ x₁ x₂ a := by
  rcases hb with hb | hb
  · exact Or.inl (Relation.EqvGen.trans _ _ _ h hb)
  · exact Or.inr (Relation.EqvGen.trans _ _ _ h hb)

theorem CutU_v : CutU M v v₂ x₁ x₂ v := Or.inl (Relation.EqvGen.refl _)

theorem CutU_v₂ : CutU M v v₂ x₁ x₂ v₂ := Or.inr (Relation.EqvGen.refl _)

/-- `M`-components are the cut components with the two halves glued. -/
theorem sc_glue (hcd : M.IsCutData v v₂ x₁ x₂) {a b : V} (h : M.SameComponent a b) :
    (M.cut v v₂ x₁ x₂).SameComponent a b ∨ (CutU M v v₂ x₁ x₂ a ∧ CutU M v v₂ x₁ x₂ b) := by
  induction h with
  | rel a b hab =>
    obtain ⟨a', b', ha, hb, hadj⟩ := adj_cut_cases M hcd hab
    have hr : (M.cut v v₂ x₁ x₂).SameComponent a' b' := Relation.EqvGen.rel _ _ hadj
    rcases ha with rfl | ⟨rfl, rfl⟩
    · rcases hb with rfl | ⟨rfl, rfl⟩
      · exact Or.inl hr
      · exact Or.inr ⟨CutU_of_sc M hr (CutU_v₂ M), CutU_v M⟩
    · rcases hb with rfl | ⟨rfl, rfl⟩
      · exact Or.inr ⟨CutU_v M, CutU_of_sc M (Relation.EqvGen.symm _ _ hr) (CutU_v₂ M)⟩
      · exact Or.inr ⟨CutU_v M, CutU_v M⟩
  | refl a => exact Or.inl (Relation.EqvGen.refl _)
  | symm a b _ ih =>
    rcases ih with h | h
    · exact Or.inl (Relation.EqvGen.symm _ _ h)
    · exact Or.inr ⟨h.2, h.1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1
    · rcases ih2 with h2 | h2
      · exact Or.inl (Relation.EqvGen.trans _ _ _ h1 h2)
      · exact Or.inr ⟨CutU_of_sc M h1 h2.1, h2.2⟩
    · rcases ih2 with h2 | h2
      · exact Or.inr ⟨h1.1, CutU_of_sc M (Relation.EqvGen.symm _ _ h2) h1.2⟩
      · exact Or.inr ⟨h1.1, h2.2⟩

end WaveTurbulence.FinalCount
