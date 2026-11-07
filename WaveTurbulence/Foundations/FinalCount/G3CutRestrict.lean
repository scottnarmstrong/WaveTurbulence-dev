/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
public import WaveTurbulence.Foundations.FinalCount.CutRank
/-! **FINALCOUNT-G3: `α`-cuts of a component.**  A cut of `compMol M a₀` that does not separate the two halves is
the restriction of the same cut of `M` (with a fresh name for the new atom).  Used to restrict `NoBetaCut` to a
component. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

section cr
variable (M : Molecule V D) (a₀ : V) {v v₂ v₂' : V} {x₁ x₂ : PDart M (compP M a₀)}

/-- `S`: the component of `a₀` together with the fresh atom. -/
def Sset (M : Molecule V D) (a₀ v₂' : V) (x : V) : Prop := x = v₂' ∨ M.SameComponent a₀ x

theorem cutatom_A (hv : M.SameComponent a₀ v) (hv₂' : v₂' ∉ M.atoms) (z : D) :
    Sset M a₀ v₂' ((M.cut v v₂' x₁.1 x₂.1).atom z) ↔ M.SameComponent a₀ (M.atom z) := by
  show Sset M a₀ v₂' (if M.atom z = v ∧ z ≠ x₁.1 ∧ z ≠ x₂.1 then v₂' else M.atom z) ↔ _
  by_cases hc : M.atom z = v ∧ z ≠ x₁.1 ∧ z ≠ x₂.1
  · rw [if_pos hc]; exact ⟨fun _ => hc.1 ▸ hv, fun _ => Or.inl rfl⟩
  · rw [if_neg hc]
    constructor
    · rintro (h | h)
      · exact absurd (h ▸ M.atom_mem z) hv₂'
      · exact h
    · exact fun h => Or.inr h

theorem atom_BA (hv₂' : v₂' ∉ M.atoms) (z : PDart M (compP M a₀)) :
    ((compMol M a₀).cut v v₂ x₁ x₂).atom z =
      if (M.cut v v₂' x₁.1 x₂.1).atom z.1 = v₂' then v₂ else (M.cut v v₂' x₁.1 x₂.1).atom z.1 := by
  show (if M.atom z.1 = v ∧ z ≠ x₁ ∧ z ≠ x₂ then v₂ else M.atom z.1) =
    if (if M.atom z.1 = v ∧ z.1 ≠ x₁.1 ∧ z.1 ≠ x₂.1 then v₂' else M.atom z.1) = v₂' then v₂ else
      (if M.atom z.1 = v ∧ z.1 ≠ x₁.1 ∧ z.1 ≠ x₂.1 then v₂' else M.atom z.1)
  have e1 : (z ≠ x₁) ↔ (z.1 ≠ x₁.1) := by rw [ne_eq, ne_eq, Subtype.ext_iff]
  have e2 : (z ≠ x₂) ↔ (z.1 ≠ x₂.1) := by rw [ne_eq, ne_eq, Subtype.ext_iff]
  have hc' : (M.atom z.1 = v ∧ z ≠ x₁ ∧ z ≠ x₂) ↔ (M.atom z.1 = v ∧ z.1 ≠ x₁.1 ∧ z.1 ≠ x₂.1) := by rw [e1, e2]
  by_cases hc : M.atom z.1 = v ∧ z.1 ≠ x₁.1 ∧ z.1 ≠ x₂.1
  · rw [if_pos (hc'.2 hc), if_pos hc, if_pos rfl]
  · rw [if_neg (fun h => hc (hc'.1 h)), if_neg hc, if_neg (fun h => hv₂' (by rw [← h]; exact M.atom_mem z.1))]

theorem pathlift (hcd : M.IsCutData v v₂' x₁.1 x₂.1) (hv : M.SameComponent a₀ v) {a b : V}
    (hab : Relation.EqvGen (M.cut v v₂' x₁.1 x₂.1).Adj a b) :
    Sset M a₀ v₂' a → Sset M a₀ v₂' b ∧
      Relation.EqvGen ((compMol M a₀).cut v v₂ x₁ x₂).Adj (if a = v₂' then v₂ else a) (if b = v₂' then v₂ else b) := by
  have hv₂' := hcd.2.1
  have hPcl := compP_closed M a₀
  have adjS : ∀ {a b : V}, (M.cut v v₂' x₁.1 x₂.1).Adj a b → (Sset M a₀ v₂' a ↔ Sset M a₀ v₂' b) := by
    rintro a b ⟨z, rfl, rfl⟩
    rw [cutatom_A M a₀ hv hv₂' z]
    refine Iff.trans ?_ (cutatom_A M a₀ hv hv₂' (M.mate z)).symm
    constructor
    · exact fun h => hPcl z h
    · intro h
      have := hPcl (M.mate z) h
      rwa [M.mate_mate] at this
  have scS : ∀ {a b : V}, Relation.EqvGen (M.cut v v₂' x₁.1 x₂.1).Adj a b →
      (Sset M a₀ v₂' a ↔ Sset M a₀ v₂' b) := by
    intro a b h
    induction h with
    | rel a b h => exact adjS h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have adjB : ∀ {a b : V}, (M.cut v v₂' x₁.1 x₂.1).Adj a b → Sset M a₀ v₂' a →
      ((compMol M a₀).cut v v₂ x₁ x₂).Adj (if a = v₂' then v₂ else a) (if b = v₂' then v₂ else b) := by
    rintro a b ⟨z, rfl, rfl⟩ ha
    have hz : compP M a₀ (M.atom z) := (cutatom_A M a₀ hv hv₂' z).1 ha
    have hz' : compP M a₀ (M.atom (M.mate z)) := hPcl z hz
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · exact atom_BA M a₀ hv₂' ⟨z, hz⟩
    · exact atom_BA M a₀ hv₂' (z := ⟨M.mate z, hz'⟩) 
  induction hab with
  | rel a b h =>
    intro ha
    exact ⟨(adjS h).1 ha, Relation.EqvGen.rel _ _ (adjB h ha)⟩
  | refl a => intro ha; exact ⟨ha, Relation.EqvGen.refl _⟩
  | symm a b hab ih =>
    intro hb
    have ha := (scS hab).2 hb
    obtain ⟨-, e⟩ := ih ha
    exact ⟨ha, Relation.EqvGen.symm _ _ e⟩
  | trans a b c hab hbc ih1 ih2 =>
    intro ha
    obtain ⟨hb, e1⟩ := ih1 ha
    obtain ⟨hc, e2⟩ := ih2 hb
    exact ⟨hc, Relation.EqvGen.trans _ _ _ e1 e2⟩

theorem cutData_ambient (hcdQ : (compMol M a₀).IsCutData v v₂ x₁ x₂) (hv₂' : v₂' ∉ M.atoms) :
    M.IsCutData v v₂' x₁.1 x₂.1 := by
  obtain ⟨hvQ, hv₂Q, hx1, hx2, hne, ho1, ho2⟩ := hcdQ
  exact ⟨((mem_compMol M a₀).1 hvQ).1, hv₂', hx1, hx2, fun e => hne (Subtype.ext e), ho1, ho2⟩

/-- **A cut of a component that does not separate the halves is an `α`-cut of the ambient molecule too** (the
direction needed to restrict `NoBetaCut`: ambient `α`-cut ⟹ component `α`-cut). -/
theorem alphaCut_comp_of_ambient (hcdQ : (compMol M a₀).IsCutData v v₂ x₁ x₂) (hv₂' : v₂' ∉ M.atoms)
    (hα : M.IsAlphaCut v v₂' x₁.1 x₂.1) : (compMol M a₀).IsAlphaCut v v₂ x₁ x₂ := by
  obtain ⟨hvQ, hv₂Q, hx1, hx2, hne, ho1, ho2⟩ := hcdQ
  have hvM := (mem_compMol M a₀).1 hvQ
  have hcdM : M.IsCutData v v₂' x₁.1 x₂.1 :=
    ⟨hvM.1, hv₂', hx1, hx2, fun e => hne (Subtype.ext e), ho1, ho2⟩
  rw [isAlphaCut_iff M hcdM] at hα
  rw [isAlphaCut_iff _ ⟨hvQ, hv₂Q, hx1, hx2, hne, ho1, ho2⟩]
  have hvv : v ≠ v₂' := fun e => hv₂' (e ▸ hvM.1)
  obtain ⟨-, e⟩ := pathlift M a₀ (v₂ := v₂) hcdM hvM.2 hα (Or.inr hvM.2)
  rwa [if_neg hvv, if_pos rfl] at e

end cr

end WaveTurbulence.FinalCountG3
