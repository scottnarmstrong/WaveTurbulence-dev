/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
public import WaveTurbulence.Foundations.FinalCount.G3EraseSt
/-! **FINALCOUNT-G3: class-aware balance** `BalS`.  After an erasure the neighbours of the erased atom can be
`ε`-atoms of degree `2` with two incoming (or two outgoing) darts, so the balance of the degree-`2` atoms is only
claimed for `α`- and `β`-atoms (this is all the cycle/chain arguments use). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

section bal
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Degree bounds, and balance of the degree-`2` atoms satisfying `E`. -/
def BalP (M : Molecule V D) (E : V → Prop) : Prop :=
  (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) ∧
    ∀ a ∈ M.atoms, E a → M.deg a = 2 → M.outdeg a = 1 ∧ M.indeg a = 1

theorem BalP.mono {M : Molecule V D} {E E' : V → Prop} (hB : BalP M E) (h : ∀ a ∈ M.atoms, E' a → E a) :
    BalP M E' := ⟨hB.1, fun a ha he hd => hB.2 a ha (h a ha he) hd⟩

theorem BalP.cut {M : Molecule V D} {E E' : V → Prop} {v v₂ : V} {x₁ x₂ : D} (hB : BalP M E)
    (hcd : M.IsCutData v v₂ x₁ x₂) (hE : ∀ a, a ≠ v → a ≠ v₂ → E' a → E a) :
    BalP (M.cut v v₂ x₁ x₂) E' := by
  have hv : v ∈ M.atoms := hcd.1
  have hv₂ : v₂ ∉ M.atoms := hcd.2.1
  have hout₂ := cut_outdeg_v₂ hcd
  have hin₂ := cut_indeg_v₂ hcd
  have hdeg₂ := cut_deg_v₂ hcd
  have hb := hB.1 v hv
  have hdv := deg_eq M v
  have hd2 := deg_eq (M.cut v v₂ x₁ x₂) v₂
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : a ∈ insert v₂ M.atoms := ha
    by_cases h1 : a = v₂
    · subst h1; omega
    · by_cases h2 : a = v
      · subst h2; rw [cut_outdeg_v hcd, cut_indeg_v hcd]; omega
      · rw [cut_outdeg_other hcd h2 h1, cut_indeg_other hcd h2 h1]
        exact hB.1 a ((Finset.mem_insert.1 ha').resolve_left h1)
  · intro a ha he hd
    have ha' : a ∈ insert v₂ M.atoms := ha
    by_cases h1 : a = v₂
    · subst h1; omega
    · by_cases h2 : a = v
      · subst h2; rw [cut_outdeg_v hcd, cut_indeg_v hcd]; omega
      · rw [cut_outdeg_other hcd h2 h1, cut_indeg_other hcd h2 h1]
        rw [cut_deg_other hcd h2 h1] at hd
        exact hB.2 a ((Finset.mem_insert.1 ha').resolve_left h1) (hE a h2 h1 he) hd

theorem BalP.restrict {M : Molecule V D} {E : V → Prop} (hB : BalP M E) (P : V → Prop) [DecidablePred P]
    (h : PClosed M P) : BalP (restrictP M P h) E := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : a ∈ M.atoms.filter P := ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ha'
    rw [restrictP_outdeg M P h h2, restrictP_indeg M P h h2]
    exact hB.1 a h1
  · intro a ha he hd
    have ha' : a ∈ M.atoms.filter P := ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ha'
    rw [restrictP_deg M P h h2] at hd
    rw [restrictP_outdeg M P h h2, restrictP_indeg M P h h2]
    exact hB.2 a h1 he hd

/-- Erasing an atom: atoms satisfying `E` have degree `≤ 2`, so a neighbour of the erased atom (degree drops by `≥ 1`)
never has degree `2` afterwards. -/
theorem BalP.erase {M : Molecule V D} {E : V → Prop} (hB : BalP M E) (v : V)
    (hE2 : ∀ a ∈ M.atoms, E a → M.deg a ≤ 2) : BalP (eraseAt M v) E := by
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ⟨(eraseAt_outdeg_le a).trans (hB.1 a (Finset.mem_of_mem_erase ha)).1,
      (eraseAt_indeg_le a).trans (hB.1 a (Finset.mem_of_mem_erase ha)).2⟩
  · intro a ha he hd
    have haM : a ∈ M.atoms := Finset.mem_of_mem_erase ha
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    have hsum := eraseAt_dartsAt_card M v hav
    have hm : mult M v a = 0 := by
      have := hE2 a haM he
      have hd' : (eraseAt M v).deg a = 2 := hd
      omega
    -- the darts are unchanged
    have hD : (eraseAt M v).outdeg a = M.outdeg a ∧ (eraseAt M v).indeg a = M.indeg a := by
      have h1 := eraseAt_sum M v hav (fun x => if M.out x = true then 1 else 0)
      have h2 := eraseAt_sum M v hav (fun x => if M.out x = false then 1 else 0)
      have hfil : (M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) = v) = M.dartsAt a := by
        refine Finset.filter_true_of_mem fun x hx hxv => ?_
        have : x ∈ (M.dartsAt a).filter fun x => M.atom (M.mate x) = v := Finset.mem_filter.2 ⟨hx, hxv⟩
        have h0 : ((M.dartsAt a).filter fun x => M.atom (M.mate x) = v).card = 0 := hm
        rw [Finset.card_eq_zero] at h0
        rw [h0] at this; simp at this
      rw [hfil] at h1 h2
      refine ⟨?_, ?_⟩
      · rw [outdeg_eq_sum, outdeg_eq_sum]; exact h1
      · rw [indeg_eq_sum, indeg_eq_sum]; exact h2
    rw [hD.1, hD.2]
    have hdd : M.deg a = 2 := by omega
    exact hB.2 a haM he hdd

end bal

/-- Class-aware balance of a state: `α`/`β`-atoms of degree `2` have one incoming and one outgoing dart. -/
def BalS (s : St.{u} V D₀) : Prop := BalP s.M (fun a => s.cls a ≠ .eps)

variable {s s' : St.{u} V D₀}

theorem BalS.ofM (hB : BalM s.M) : BalS s := ⟨hB.1, fun a ha _ hd => hB.2 a ha hd⟩

theorem BalS.cutSt (hB : BalS s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) :
    BalS (s.cutSt v v₂ x₁ x₂ c₁ c₂) :=
  BalP.cut hB hcd (fun a h1 h2 he => by
    have : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = s.cls a := cutSt_cls_other c₁ c₂ h1 h2
    rw [← this]; exact he)

theorem BalS.delSt (hB : BalS s) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) : BalS (s.delSt P h) :=
  BalP.restrict hB P h

theorem BalS.withCls (hB : BalS s) (c : V → Cls) (h : ∀ a ∈ s.M.atoms, c a ≠ .eps → s.cls a ≠ .eps) :
    BalS (s.withCls c) := BalP.mono hB h

theorem BalS.eraseSt {R : ℕ} (hB : BalS s) (hg : Good R s) (v : V) : BalS (s.eraseSt v) :=
  BalS.delSt (s := s.erase0 v) (BalP.erase hB v (fun a ha he => (hg.1.ab a ha he).1)) _ (keepE_closed s v)

end WaveTurbulence.FinalCountG3
