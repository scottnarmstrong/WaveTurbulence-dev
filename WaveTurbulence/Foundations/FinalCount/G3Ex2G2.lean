/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2G1
/-! **FINALCOUNT-G3: bridges for the charged ghost triangle bound (part 2).**  The true increments of a triangle step with
ghosts: `F(post) = F(kept) - g` and `#β(post) - #β(pre) = 3 - #newα - g - g_β`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section tri
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem f_mem_m3 (j : Fin 3) : T.f j ∈ T.m3.atoms := by
  rw [TriData.m3_atoms]; fin_cases j <;> simp

/-- The atoms of the state after a triangle step: the new atoms `f j` of the non-ghost positions and the old atoms off the
triangle. -/
theorem triSt_atoms_gen (hcl : PClosed T.kept (triKeep s T)) :
    (triSt s T Q kp hcl).M.atoms =
      (Finset.univ.filter fun j => s.cls (T.t j) = .eps).image T.f ∪ s.M.atoms.filter T.TP := by
  show ((T.m3.atoms.filter T.TP).filter (triKeep s T)) = _
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, triKeep]
  constructor
  · rintro ⟨⟨hm, hP⟩, hk⟩
    rw [TriData.m3_atoms] at hm
    simp only [Finset.mem_insert] at hm
    rcases hm with rfl | rfl | rfl | h
    · refine Or.inl ⟨2, ?_, rfl⟩
      by_contra hc; exact hk 2 hc rfl
    · refine Or.inl ⟨1, ?_, rfl⟩
      by_contra hc; exact hk 1 hc rfl
    · refine Or.inl ⟨0, ?_, rfl⟩
      by_contra hc; exact hk 0 hc rfl
    · exact Or.inr ⟨h, hP⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨hm, hP⟩)
    · refine ⟨⟨f_mem_m3 T j, T.TP_f j⟩, fun i hi e => hi ?_⟩
      have := T.f_inj e
      rw [← this]; exact hj
    · refine ⟨⟨?_, hP⟩, fun i _ e => T.f_fresh i (e ▸ hm)⟩
      rw [TriData.m3_atoms]
      simp [hm]

theorem triKeep_dartless
    (hd : ∀ j, s.cls (T.t j) ≠ .eps → s.M.deg (T.t j) ≤ 2) :
    ∀ x : PDart T.m3 T.TP, triKeep s T (T.kept.atom x) := by
  intro x j hj hxj
  have h0 := kept_deg_f_zero T j (hd j hj)
  have hmem : x ∈ T.kept.dartsAt (T.f j) := (mem_dartsAt T.kept _ x).2 hxj
  have : 0 < T.kept.deg (T.f j) := Finset.card_pos.2 ⟨x, hmem⟩
  omega

/-- `F(post) = F(kept) - g`: the `g` ghost remainders of `T.kept` are isolated atoms, deleted by the ghost deletion. -/
theorem triSt_numComponents_ghost (hcl : PClosed T.kept (triKeep s T))
    (hd : ∀ j, s.cls (T.t j) ≠ .eps → s.M.deg (T.t j) ≤ 2) :
    (triSt s T Q kp hcl).M.numComponents + (Finset.univ.filter fun j => s.cls (T.t j) ≠ .eps).card =
      T.kept.numComponents := by
  have hno := triKeep_dartless T hd
  have h1 := numComponents_restrictP_add T.kept (triKeep s T) hcl
  have hE : IsEmpty (PDart T.kept (fun a => ¬ triKeep s T a)) := ⟨fun x => x.2 (hno x.1)⟩
  have h2 := dartless_numComponents (restrictP T.kept (fun a => ¬ triKeep s T a) hcl.neg)
  have h3 : (restrictP T.kept (fun a => ¬ triKeep s T a) hcl.neg).atoms =
      (Finset.univ.filter fun j => s.cls (T.t j) ≠ .eps).image T.f := by
    show (T.m3.atoms.filter T.TP).filter (fun a => ¬ triKeep s T a) = _
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, triKeep]
    constructor
    · rintro ⟨⟨hm, hP⟩, hk⟩
      push Not at hk
      obtain ⟨j, hj, hj2⟩ := hk
      exact ⟨j, hj, hj2.symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨f_mem_m3 T j, T.TP_f j⟩, by push Not; exact ⟨j, hj, rfl⟩⟩
  rw [h2, h3, Finset.card_image_of_injective _ T.f_inj] at h1
  exact h1

theorem atoms_split : s.M.atoms = s.M.atoms.filter T.TP ∪ Finset.univ.image T.t := by
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro ha
    by_cases hP : T.TP a
    · exact Or.inl ⟨ha, hP⟩
    · obtain ⟨j, rfl⟩ := (T.not_TP_iff a).1 hP; exact Or.inr ⟨j, rfl⟩
  · rintro (⟨ha, -⟩ | ⟨j, rfl⟩)
    · exact ha
    · exact T.t_mem j

theorem atoms_disj : Disjoint (s.M.atoms.filter T.TP) (Finset.univ.image T.t) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
  exact (Finset.mem_filter.1 ha).2 j rfl

theorem betaCount_pre :
    betaCount s = ∑ a ∈ s.M.atoms.filter T.TP, (if s.cls a = .beta then (1 : ℤ) else 0) +
      ∑ j : Fin 3, (if s.cls (T.t j) = .beta then (1 : ℤ) else 0) := by
  unfold betaCount
  rw [Finset.natCast_card_filter, atoms_split T, Finset.sum_union (atoms_disj T),
    Finset.sum_image (fun i _ j _ e => T.t_inj e)]
  rw [← atoms_split T]

theorem betaCount_post (hcl : PClosed T.kept (triKeep s T)) :
    betaCount (triSt s T Q kp hcl) = ∑ a ∈ s.M.atoms.filter T.TP, (if s.cls a = .beta then (1 : ℤ) else 0) +
      ∑ j : Fin 3, (if s.cls (T.t j) = .eps then (if triCls s T Q kp (T.f j) = .beta then (1 : ℤ) else 0) else 0) := by
  have hc : (triSt s T Q kp hcl).cls = triCls s T Q kp := rfl
  unfold betaCount
  rw [hc, Finset.natCast_card_filter, triSt_atoms_gen T Q kp hcl, Finset.sum_union, Finset.sum_image (fun i _ j _ e => T.f_inj e),
    Finset.sum_filter, add_comm]
  · congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ (Finset.mem_filter.1 ha).1)
    rw [triCls_other T Q kp hf]
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact T.f_fresh j (Finset.mem_filter.1 hb).1

end tri

section incr
variable (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

/-- `#β(post) - #β(pre) = 3 - #newα - g - g_β` (the `β`-atoms `t j` are removed, the non-ghost `f j` are new, the new `α`-atoms
are not `β`). -/
theorem betaCount_incr (hcl : PClosed T.kept (triKeep h.s T))
    (hd : ∀ j, h.s.cls (T.t j) ≠ .eps → h.s.M.deg (T.t j) ≤ 2) :
    betaCount (h.triPost T Q kp hcl).s - betaCount h.s =
      3 - ((triAlphaNew h T Q kp).length : ℤ) - ((Finset.univ.filter fun j => h.s.cls (T.t j) ≠ .eps).card : ℤ) -
        ((Finset.univ.filter fun j => h.s.cls (T.t j) = .beta).card : ℤ) := by
  have e1 := betaCount_post T Q kp hcl
  have e2 := betaCount_pre T
  have e3 := alphaLabels_eq_triAlphaNew h T Q kp hd
  rw [← e3]
  change betaCount (triSt h.s T Q kp hcl) - betaCount h.s = _
  rw [e1, e2, Finset.natCast_card_filter, Finset.natCast_card_filter]
  unfold TriData.alphaLabels
  have hA0 := isA0_iff T
  have hA1 := isA1_iff T
  rw [Fin.sum_univ_three]
  simp only [List.length_append, Fin.sum_univ_three, add_sub_add_left_eq_sub]
  have a0 := T.not_isA0_of_ghost
  have a1 := T.not_isA1_of_ghost1
  have f0 := triCls_f0 (s := h.s) T Q kp
  have f1 := triCls_f1 (s := h.s) T Q kp
  have f2 := triCls_f2 (s := h.s) T Q kp
  rw [f0, f1, f2]
  by_cases e0 : h.s.cls (T.t 0) = .eps <;> by_cases e1' : h.s.cls (T.t 1) = .eps <;>
    by_cases e2' : h.s.cls (T.t 2) = .eps
  all_goals simp only [hA0, hA1]
  all_goals have n0 : ¬ h.s.cls (T.t 0) = .eps → ¬ (T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1)) :=
    fun e => hA0.not.1 (a0 (hd 0 e))
  all_goals have n1 : ¬ h.s.cls (T.t 1) = .eps → ¬ T.kept.SameComponent (T.f 1) (T.f 2) :=
    fun e => hA1.not.1 (a1 (hd 1 e))
  all_goals simp [e0, e1', e2'] at n0 n1 ⊢
  all_goals split_ifs <;> simp_all

end incr

end WaveTurbulence.FinalCountG3
