/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.FinalCount.Prop95Statement
/-! **FINALCOUNT-G3: no triple bond in `𝕄_fin`** (DH23 L1806, L1816: "any triple bond is destroyed in Step 1").

`EpsLe s₁ s`: the `ε`-atoms of `s` are `ε`-atoms of `s₁` and the number of bonds between two of them did not
increase.  It holds along Steps 2-4; an atom of class `≠ ε` has degree `≤ 2`, so no triple bond involves it. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

theorem bondsBetween_le_deg {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (a b : V) :
    M.bondsBetween a b ≤ M.deg a := by
  unfold Molecule.bondsBetween Molecule.deg
  refine Finset.card_le_card_of_injOn (fun x => if M.atom x = a then x else M.mate x) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.bonds, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    obtain ⟨ho, he⟩ := hx
    simp only [Finset.mem_coe, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Molecule.ends at he
    by_cases hxa : M.atom x = a
    · simp [hxa]
    · simp only [hxa, if_false]
      rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 hxa
      · exact h2
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.bonds, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx hy
    by_cases hxa : M.atom x = a <;> by_cases hya : M.atom y = a
    · simpa [hxa, hya] using hxy
    · simp only [hxa, hya, ite_true, ite_false] at hxy
      have h1 := M.out_mate y
      rw [hy.1] at h1
      have h2 : M.out (M.mate y) = false := by simpa using h1.symm
      rw [← hxy, hx.1] at h2
      exact absurd h2 (by simp)
    · simp only [hxa, hya, ite_true, ite_false] at hxy
      have h1 := M.out_mate x
      rw [hx.1] at h1
      have h2 : M.out (M.mate x) = false := by simpa using h1.symm
      rw [hxy, hy.1] at h2
      exact absurd h2 (by simp)
    · simp only [hxa, hya, if_false] at hxy
      simpa [M.mate_mate] using congrArg M.mate hxy


theorem bondsBetween_restrict_le {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (P : V → Prop)
    [DecidablePred P] (h : PClosed M P) (a b : V) :
    (restrictP M P h).bondsBetween a b ≤ M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

/-- The `ε`-atoms of `s` are `ε`-atoms of `s₁` and bonds between them did not multiply. -/
def EpsLe (s₁ s : St.{u} V D₀) : Prop :=
  ∀ a ∈ s.M.atoms, ∀ b ∈ s.M.atoms, s.cls a = .eps → s.cls b = .eps →
    (a ∈ s₁.M.atoms ∧ s₁.cls a = .eps) ∧ (b ∈ s₁.M.atoms ∧ s₁.cls b = .eps) ∧
      s.M.bondsBetween a b ≤ s₁.M.bondsBetween a b

theorem EpsLe.refl (s : St.{u} V D₀) : EpsLe s s := fun _ ha _ hb hca hcb => ⟨⟨ha, hca⟩, ⟨hb, hcb⟩, le_rfl⟩

theorem EpsLe.trans {s₁ s₂ s₃ : St.{u} V D₀} (h12 : EpsLe s₁ s₂) (h23 : EpsLe s₂ s₃) : EpsLe s₁ s₃ := by
  intro a ha b hb hca hcb
  obtain ⟨⟨a2, ca2⟩, ⟨b2, cb2⟩, l23⟩ := h23 a ha b hb hca hcb
  obtain ⟨⟨a1, ca1⟩, ⟨b1, cb1⟩, l12⟩ := h12 a a2 b b2 ca2 cb2
  exact ⟨⟨a1, ca1⟩, ⟨b1, cb1⟩, l23.trans l12⟩

theorem EpsLe.cutSt (s : St.{u} V D₀) {v v₂ : V} (x₁ x₂ : s.D) (hv : v ∈ s.M.atoms) (hv₂ : v₂ ∉ s.M.atoms)
    (c₁ c₂ : Cls) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps) : EpsLe s (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  have key : ∀ a ∈ (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms, (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = .eps →
      a ≠ v ∧ a ≠ v₂ ∧ a ∈ s.M.atoms ∧ s.cls a = .eps := by
    intro a ha hae
    have ha' : a ∈ insert v₂ s.M.atoms := ha
    have e2 : a ≠ v₂ := by rintro rfl; rw [cutSt_cls_v₂] at hae; exact h₂ hae
    have e1 : a ≠ v := by rintro rfl; rw [cutSt_cls_v _ _ hne] at hae; exact h₁ hae
    rw [cutSt_cls_other _ _ e1 e2] at hae
    exact ⟨e1, e2, (Finset.mem_insert.1 ha').resolve_left e2, hae⟩
  intro a ha b hb hca hcb
  obtain ⟨a1, a2, a3, a4⟩ := key a ha hca
  obtain ⟨b1, b2, b3, b4⟩ := key b hb hcb
  refine ⟨⟨a3, a4⟩, ⟨b3, b4⟩, ?_⟩
  exact (cut_bondsBetween_eq s.M a1 a2 b1 b2).le

theorem EpsLe.delSt (s : St.{u} V D₀) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) :
    EpsLe s (s.delSt P h) := by
  intro a ha b hb hca hcb
  exact ⟨⟨(Finset.mem_filter.1 ha).1, hca⟩, ⟨(Finset.mem_filter.1 hb).1, hcb⟩,
    bondsBetween_restrict_le s.M P h a b⟩

theorem EpsLe.withCls (s : St.{u} V D₀) (c : V → Cls) (hc : ∀ a ∈ s.M.atoms, (c a = .eps ↔ s.cls a = .eps)) :
    EpsLe s (s.withCls c) := by
  intro a ha b hb hca hcb
  exact ⟨⟨ha, (hc a ha).1 hca⟩, ⟨hb, (hc b hb).1 hcb⟩, le_rfl⟩

theorem Step1.epsLe {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') : EpsLe s s' := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    have hab := Cls.ne_eps_of_isAB (alphaOrBeta_isAB K.post.numComponents s.M.numComponents R kp)
    have e1 := EpsLe.cutSt s K.x₁ K.x₂ K.cut_a.1 K.cut_a.2.1 _ _ hab hab
    have e2 := EpsLe.cutSt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ (alphaOrBeta K.post.numComponents s.M.numComponents R kp)
      (alphaOrBeta K.post.numComponents s.M.numComponents R kp)) K.y₁ K.y₂ K.cut_b.1 K.cut_b.2.1 _ _ hab hab
    exact (e1.trans e2).trans (EpsLe.delSt _ _ K.closed)

theorem Step2.epsLe {s s' : St.{u} V D₀} (h : Step2 L γ η w κ s s') : EpsLe s s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 =>
    have c0 : (if s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c1 : (if s.cls (T.t 1) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c2 : (if s.cls (T.t 2) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have h1 := EpsLe.cutSt s (T.a 0) (T.b 0) (T.t_mem 0) (T.f_fresh 0) .beta
      (if s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost) (by simp) c0
    have h2 := EpsLe.cutSt (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost)) (T.a 1) (T.b 1) (T.t_mem_m1 1)
      T.f_fresh_m1 .beta (if s.cls (T.t 1) = .eps then Cls.beta else Cls.ghost) (by simp) c1
    have h3 := EpsLe.cutSt ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1)
      .beta (if s.cls (T.t 1) = .eps then Cls.beta else Cls.ghost)) (T.a 2) (T.b 2) (T.t_mem_m2 2) T.f_fresh_m2
      .beta (if s.cls (T.t 2) = .eps then Cls.beta else Cls.ghost) (by simp) c2
    have h4 := EpsLe.delSt (triCuts s T) T.TP T.pclosed
    have h5 := EpsLe.withCls (((triCuts s T).delSt T.TP T.pclosed)) (triCls s T Q kp) (fun a ha => by
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact (tri_cls_agree T Q kp a ha'.1 ha'.2).2.1)
    have h6 := EpsLe.delSt (((triCuts s T).delSt T.TP T.pclosed).withCls (triCls s T Q kp)) _ hcl
    exact (((h1.trans h2).trans h3).trans h4).trans (h5.trans h6)

theorem Step3.epsLe {s s' : St.{u} V D₀} (h : Step3 L γ η w κ s s') : EpsLe s s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim h3 =>
    have hab : (if s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by
      split_ifs <;> trivial
    exact EpsLe.cutSt s x₁ x₂ hcd.1 hcd.2.1 _ _ (Cls.ne_eps_of_isAB hab) (Cls.ne_eps_of_isAB hab)

theorem Step4.epsLe {s s' : St.{u} V D₀} (h : Step4 s s') : EpsLe s s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact EpsLe.cutSt s x₁ x₂ hcd.1 hcd.2.1 _ _ (by simp) (by simp)

end WaveTurbulence.FinalCountG3
