/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutComp2
/-! Component count of a cut, part 3 (FINALCOUNT-G2 step 1): the cardinalities. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

section
variable (hcd : M.IsCutData v v₂ x₁ x₂)
include hcd

theorem piV_mem {a : V} (ha : a ∈ (M.cut v v₂ x₁ x₂).atoms) : piV v v₂ a ∈ M.atoms := by
  unfold piV
  split_ifs with h
  · exact hcd.1
  · have : a ∈ insert v₂ M.atoms := ha
    exact (Finset.mem_insert.mp this).resolve_left h

/-- The gluing map from cut components to components. -/
def phi : Quot (fun u w : (M.cut v v₂ x₁ x₂).atoms => (M.cut v v₂ x₁ x₂).Adj u.1 w.1) →
    Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
  Quot.lift (fun a => Quot.mk _ ⟨piV v v₂ a.1, piV_mem M hcd a.2⟩)
    (fun _ _ h => Quot.sound (cutAdj_pi M hcd h))

theorem phi_eq_iff (a b : V) (ha : a ∈ (M.cut v v₂ x₁ x₂).atoms) (hb : b ∈ (M.cut v v₂ x₁ x₂).atoms) :
    phi M hcd (Quot.mk _ ⟨a, ha⟩) = phi M hcd (Quot.mk _ ⟨b, hb⟩) ↔
      M.SameComponent (piV v v₂ a) (piV v v₂ b) :=
  quot_mk_eq_iff M _ _ (piV_mem M hcd ha) (piV_mem M hcd hb)

theorem phi_surjective : Function.Surjective (phi M hcd) := by
  intro q
  induction q using Quot.ind with
  | _ a =>
    obtain ⟨a, ha⟩ := a
    have ha' : a ∈ (M.cut v v₂ x₁ x₂).atoms := Finset.mem_insert_of_mem ha
    refine ⟨Quot.mk _ ⟨a, ha'⟩, ?_⟩
    have : piV v v₂ a = a := by
      unfold piV
      rw [if_neg]
      rintro rfl
      exact hcd.2.1 ha
    simp only [phi, Quot.lift_mk]
    congr 2

theorem v₂_mem : v₂ ∈ (M.cut v v₂ x₁ x₂).atoms := Finset.mem_insert_self _ _

theorem v_mem' : v ∈ (M.cut v v₂ x₁ x₂).atoms := Finset.mem_insert_of_mem hcd.1

theorem piV_of_ne' {a : V} (h : a ≠ v₂) : piV v v₂ a = a := by unfold piV; rw [if_neg h]

/-- Injectivity of the gluing away from the class of `v₂`. -/
theorem inj_aux {a b : V} (ha : a ∈ (M.cut v v₂ x₁ x₂).atoms) (hb : b ∈ (M.cut v v₂ x₁ x₂).atoms)
    (ha2 : ¬ (M.cut v v₂ x₁ x₂).SameComponent a v₂) (hb2 : ¬ (M.cut v v₂ x₁ x₂).SameComponent b v₂)
    (h : M.SameComponent (piV v v₂ a) (piV v v₂ b)) : (M.cut v v₂ x₁ x₂).SameComponent a b := by
  have ha' : a ≠ v₂ := fun e => ha2 (e ▸ Relation.EqvGen.refl _)
  have hb' : b ≠ v₂ := fun e => hb2 (e ▸ Relation.EqvGen.refl _)
  rw [piV_of_ne' M hcd ha', piV_of_ne' M hcd hb'] at h
  rcases sc_glue M hcd h with h | ⟨h1, h2⟩
  · exact h
  · have h1' := h1.resolve_right ha2
    have h2' := h2.resolve_right hb2
    exact Relation.EqvGen.trans _ _ _ h1' (Relation.EqvGen.symm _ _ h2')

theorem numComponents_cut_ge : M.numComponents ≤ (M.cut v v₂ x₁ x₂).numComponents := by
  unfold Molecule.numComponents
  have : Finite (M.cut v v₂ x₁ x₂).atoms := inferInstance
  exact Nat.card_le_card_of_surjective _ (phi_surjective M hcd)

/-- The classes other than that of `v₂` embed in the components of `M`. -/
theorem numComponents_cut_le_succ : (M.cut v v₂ x₁ x₂).numComponents ≤ M.numComponents + 1 := by
  classical
  unfold Molecule.numComponents
  set Qc := Quot (fun u w : (M.cut v v₂ x₁ x₂).atoms => (M.cut v v₂ x₁ x₂).Adj u.1 w.1)
  set p : Qc := Quot.mk _ ⟨v₂, v₂_mem M hcd⟩
  have : Finite Qc := inferInstance
  have : Finite (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) := inferInstance
  have e : Nat.card (Option {q : Qc // q ≠ p}) = Nat.card Qc :=
    Nat.card_congr (Equiv.optionSubtypeNe p)
  have h1 : Nat.card {q : Qc // q ≠ p} ≤ Nat.card (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) := by
    refine Nat.card_le_card_of_injective (fun q => phi M hcd q.1) ?_
    rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    induction q using Quot.ind with
    | _ a =>
    induction q' using Quot.ind with
    | _ b =>
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have hq1 : ¬ (M.cut v v₂ x₁ x₂).SameComponent a v₂ := fun h =>
      hq ((quot_mk_eq_iff _ _ _ ha (v₂_mem M hcd)).2 h)
    have hq1' : ¬ (M.cut v v₂ x₁ x₂).SameComponent b v₂ := fun h =>
      hq' ((quot_mk_eq_iff _ _ _ hb (v₂_mem M hcd)).2 h)
    have := (phi_eq_iff M hcd a b ha hb).1 h
    exact Subtype.ext ((quot_mk_eq_iff _ _ _ ha hb).2 (inj_aux M hcd ha hb hq1 hq1' this))
  have h2 : Nat.card (Option {q : Qc // q ≠ p}) = Nat.card {q : Qc // q ≠ p} + 1 := by
    have : Finite {q : Qc // q ≠ p} := inferInstance
    simp
  omega

theorem numComponents_cut_of_same (hs : (M.cut v v₂ x₁ x₂).SameComponent v v₂) :
    (M.cut v v₂ x₁ x₂).numComponents = M.numComponents := by
  refine le_antisymm ?_ (numComponents_cut_ge M hcd)
  unfold Molecule.numComponents
  have : Finite (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) := inferInstance
  refine Nat.card_le_card_of_injective (phi M hcd) ?_
  intro q q' h
  induction q using Quot.ind with
  | _ a =>
  induction q' using Quot.ind with
  | _ b =>
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have h' := (phi_eq_iff M hcd a b ha hb).1 h
  have hpa : (M.cut v v₂ x₁ x₂).SameComponent (piV v v₂ a) a := by
    unfold piV; split_ifs with e
    · subst e; exact hs
    · exact Relation.EqvGen.refl _
  have hpb : (M.cut v v₂ x₁ x₂).SameComponent (piV v v₂ b) b := by
    unfold piV; split_ifs with e
    · subst e; exact hs
    · exact Relation.EqvGen.refl _
  have hU : ∀ x, CutU M v v₂ x₁ x₂ x → (M.cut v v₂ x₁ x₂).SameComponent x v := fun x hx =>
    hx.elim id fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hs)
  have : (M.cut v v₂ x₁ x₂).SameComponent a b := by
    rcases sc_glue M hcd h' with h1 | ⟨h1, h2⟩
    · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpa) (Relation.EqvGen.trans _ _ _ h1 hpb)
    · have e1 := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpa) (hU _ h1)
      have e2 := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpb) (hU _ h2)
      exact Relation.EqvGen.trans _ _ _ e1 (Relation.EqvGen.symm _ _ e2)
  exact (quot_mk_eq_iff _ _ _ ha hb).2 this

theorem numComponents_cut_of_not_same (hs : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂) :
    (M.cut v v₂ x₁ x₂).numComponents = M.numComponents + 1 := by
  classical
  have hle := numComponents_cut_le_succ M hcd
  unfold Molecule.numComponents at hle ⊢
  set Qc := Quot (fun u w : (M.cut v v₂ x₁ x₂).atoms => (M.cut v v₂ x₁ x₂).Adj u.1 w.1)
  set p : Qc := Quot.mk _ ⟨v₂, v₂_mem M hcd⟩
  have : Finite Qc := inferInstance
  have : Finite (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) := inferInstance
  have e : Nat.card (Option {q : Qc // q ≠ p}) = Nat.card Qc :=
    Nat.card_congr (Equiv.optionSubtypeNe p)
  have h2 : Nat.card (Option {q : Qc // q ≠ p}) = Nat.card {q : Qc // q ≠ p} + 1 := by
    have : Finite {q : Qc // q ≠ p} := inferInstance
    simp
  have h3 : Nat.card (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) ≤ Nat.card {q : Qc // q ≠ p} := by
    refine Nat.card_le_card_of_surjective (fun q => phi M hcd q.1) ?_
    intro q
    induction q using Quot.ind with
    | _ a =>
    obtain ⟨a, haM⟩ := a
    have ha : a ∈ (M.cut v v₂ x₁ x₂).atoms := Finset.mem_insert_of_mem haM
    have hne : a ≠ v₂ := fun e => hcd.2.1 (e ▸ haM)
    by_cases hr : (M.cut v v₂ x₁ x₂).SameComponent a v₂
    · refine ⟨⟨Quot.mk _ ⟨v, v_mem' M hcd⟩, fun h => hs ((quot_mk_eq_iff _ _ _ (v_mem' M hcd) (v₂_mem M hcd)).1 h)⟩, ?_⟩
      have := cutSC_pi M hcd hr
      rw [piV_of_ne' M hcd hne] at this
      have h4 : piV v v₂ v₂ = v := by unfold piV; simp
      rw [h4] at this
      show phi M hcd _ = _
      simp only [phi, Quot.lift_mk]
      have hv : piV v v₂ v = v := piV_of_ne' M hcd (fun e => hcd.2.1 (e ▸ hcd.1))
      exact (quot_mk_eq_iff M _ _ _ haM).2 (by rw [hv]; exact Relation.EqvGen.symm _ _ this)
    · refine ⟨⟨Quot.mk _ ⟨a, ha⟩, fun h => hr ((quot_mk_eq_iff _ _ _ ha (v₂_mem M hcd)).1 h)⟩, ?_⟩
      show phi M hcd _ = _
      simp only [phi, Quot.lift_mk]
      congr 2
      exact piV_of_ne' M hcd hne
  omega

end

end WaveTurbulence.FinalCount
