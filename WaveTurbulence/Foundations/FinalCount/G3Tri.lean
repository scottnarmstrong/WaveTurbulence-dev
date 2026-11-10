/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Vine
public import WaveTurbulence.Foundations.FinalCount.TriDev1
/-! **FINALCOUNT-G3**: `Inv` for Step 2 (triangles). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

theorem Inv.cutSt_tri {s : St.{u} V D₀} {R : ℕ} (hI : Inv R s) {v v₂ : V} {x₁ x₂ : s.D}
    (hcd : s.M.IsCutData v v₂ x₁ x₂) (c2 : Cls)
    (h1 : s.cls v = .eps → c2 = .beta) (h2 : s.cls v ≠ .eps → c2 = .ghost)
    (h3 : s.cls v = .eps → 3 ≤ s.M.deg v) :
    Inv R (s.cutSt v v₂ x₁ x₂ .beta c2) := by
  by_cases hε : s.cls v = .eps
  · have := h1 hε
    subst this
    exact hI.cutSt hcd _ _ (by rw [hε]; rfl) (by simp) (by simp) (by simp) (fun h => by simp at h) (fun _ => h3 hε)
  · have := h2 hε
    subst this
    have hv := hcd.1
    have hab := hI.ab v hv hε
    have hne : x₁ ≠ x₂ := cut_x_ne hcd
    have hx1 : x₁ ∈ s.M.dartsAt v := (mem_dartsAt s.M v x₁).2 hcd.2.2.1
    have hx2 : x₂ ∈ s.M.dartsAt v := (mem_dartsAt s.M v x₂).2 hcd.2.2.2.1
    have hdeg : 2 ≤ s.M.deg v := by
      have : ({x₁, x₂} : Finset s.D) ⊆ s.M.dartsAt v := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h := Finset.card_le_card this
      rw [Finset.card_pair hne] at h; exact h
    have hng : s.cls v ≠ .ghost := fun h => by have := hab.2.1 h; omega
    have hbase : (s.cls v).base = 2 := by
      rcases hc : s.cls v with _ | _ | _ | _
      · exact absurd hc hε
      · rfl
      · rfl
      · exact absurd hc hng
    exact hI.cutSt hcd _ _ (by rw [hbase]; rfl) (by simp) (by simp) (by simp) (fun _ => by omega) (fun h => absurd rfl h)


section tri
variable {s : St.{u} V D₀} (T : TriData s.M)

theorem triCuts_cls (a : V) : (triCuts s T).cls a =
    if a = T.f 2 then (if s.cls (T.t 2) = .eps then .beta else .ghost)
    else if a = T.t 2 then .beta
    else if a = T.f 1 then (if s.cls (T.t 1) = .eps then .beta else .ghost)
    else if a = T.t 1 then .beta
    else if a = T.f 0 then (if s.cls (T.t 0) = .eps then .beta else .ghost)
    else if a = T.t 0 then .beta else s.cls a := by
  simp only [triCuts, St.cutSt, Function.update_apply]

theorem Inv.triCuts {R : ℕ} (hI : Inv R s) (h3 : ∀ j, s.cls (T.t j) = .eps → 3 ≤ s.M.deg (T.t j)) :
    Inv R (triCuts s T) := by
  have t01 : T.t 1 ≠ T.t 0 := T.t_ne (by decide)
  have t02 : T.t 2 ≠ T.t 0 := T.t_ne (by decide)
  have t12 : T.t 2 ≠ T.t 1 := T.t_ne (by decide)
  have f01 : T.f 1 ≠ T.f 0 := T.f_ne (by decide)
  have f02 : T.f 2 ≠ T.f 0 := T.f_ne (by decide)
  have f12 : T.f 2 ≠ T.f 1 := T.f_ne (by decide)
  have hs1 : Inv R (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)) :=
    hI.cutSt_tri T.cd1 _ (fun h => by simp [h]) (fun h => by simp [h]) (h3 0)
  have hc1 : (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cls (T.t 1) = s.cls (T.t 1) := by
    simp only [St.cutSt, Function.update_apply, t01, (T.f_ne_t 0 1).symm, if_false]
  have hs2 : Inv R ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)) :=
    hs1.cutSt_tri T.cd2 _ (fun h => by rw [hc1] at h; simp [h]) (fun h => by rw [hc1] at h; simp [h])
      (fun h => by
        rw [hc1] at h
        have := h3 1 h
        show 3 ≤ (s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)).deg (T.t 1)
        rw [cut_deg_other T.cd1 t01 (T.f_ne_t 0 1).symm]; exact this)
  have hc2 : ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)).cls (T.t 2) = s.cls (T.t 2) := by
    simp only [St.cutSt, Function.update_apply, t02, t12, (T.f_ne_t 0 2).symm, (T.f_ne_t 1 2).symm, if_false]
  exact hs2.cutSt_tri T.cd3 _ (fun h => by rw [hc2] at h; simp [h]) (fun h => by rw [hc2] at h; simp [h])
    (fun h => by
      rw [hc2] at h
      have := h3 2 h
      show 3 ≤ (T.m1.cut (T.t 1) (T.f 1) (T.a 1) (T.b 1)).deg (T.t 2)
      rw [cut_deg_other T.cd2 t12 (T.f_ne_t 1 2).symm]
      show 3 ≤ (s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)).deg (T.t 2)
      rw [cut_deg_other T.cd1 t02 (T.f_ne_t 0 2).symm]; exact this)

theorem Inv.withCls {R : ℕ} (hI : Inv R s) (c : V → Cls)
    (h : ∀ a ∈ s.M.atoms, (c a).base = (s.cls a).base ∧ (c a = .eps ↔ s.cls a = .eps) ∧
      (c a = .ghost ↔ s.cls a = .ghost)) : Inv R (s.withCls c) := by
  refine ⟨hI.bounds, ?_, ?_, ?_, hI.noloop⟩
  · intro a ha hc
    exact hI.eps a ha ((h a ha).2.1.1 hc)
  · intro a ha hc
    have hab := hI.ab a ha (fun e => hc ((h a ha).2.1.2 e))
    exact ⟨hab.1, fun hg => hab.2.1 ((h a ha).2.2.1 hg), fun hg => hab.2.2 (fun e => hg ((h a ha).2.2.2 e))⟩
  · show ∑ a ∈ s.M.atoms, (c a).base = _
    rw [Finset.sum_congr rfl fun a ha => (h a ha).1]; exact hI.phi

theorem tri_deg_ge_two (j : Fin 3) : 2 ≤ s.M.deg (T.t j) := by
  have hne : T.a j ≠ T.b j := fun e => by
    have h1 := T.out_a j; have h2 := T.out_b j; rw [e] at h1; rw [h1] at h2; exact Bool.false_ne_true h2
  have : ({T.a j, T.b j} : Finset s.D) ⊆ s.M.dartsAt (T.t j) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_dartsAt s.M _ _).2 (T.atom_a j)
    · exact (mem_dartsAt s.M _ _).2 (T.atom_b j)
  have h := Finset.card_le_card this
  rw [Finset.card_pair hne] at h; exact h

theorem tri_deg_f (j : Fin 3) : s.M.deg (T.t j) = T.m3.deg (T.f j) + 2 := by
  have := T.sum_t j (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
  unfold Molecule.deg; omega

variable (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem triCls_f2 : triCls s T Q kp (T.f 2) = if s.cls (T.t 2) = .eps then .beta else .ghost := by
  simp [triCls]

theorem triCls_f1 : triCls s T Q kp (T.f 1) = if s.cls (T.t 1) = .eps then
    (if T.kept.SameComponent (T.f 1) (T.f 2) then .alpha (Q 1) (kp 1) else .beta) else .ghost := by
  have h : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
  have h' : T.f 1 ≠ T.f 0 := T.f_ne (by decide)
  simp [triCls, h, h']

theorem triCls_f0 : triCls s T Q kp (T.f 0) = if s.cls (T.t 0) = .eps then
    (if T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1)
      then .alpha (Q 0) (kp 0) else .beta) else .ghost := by
  have h : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
  simp [triCls, h]

theorem triCls_other {a : V} (hf : ∀ j, a ≠ T.f j) : triCls s T Q kp a = s.cls a := by
  simp [triCls, hf 0, hf 1, hf 2]

theorem tri_cls_agree (a : V) (ha : a ∈ T.m3.atoms) (hP : T.TP a) :
    (triCls s T Q kp a).base = ((triCuts s T).cls a).base ∧
    (triCls s T Q kp a = .eps ↔ (triCuts s T).cls a = .eps) ∧
    (triCls s T Q kp a = .ghost ↔ (triCuts s T).cls a = .ghost) := by
  rw [TriData.m3_atoms] at ha
  simp only [Finset.mem_insert] at ha
  have hP' : ∀ j, a ≠ T.t j := hP
  rcases ha with h | h | h | h
  · subst h
    rw [triCls_f2, triCuts_cls]; simp
  · subst h
    have h1 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
    rw [triCls_f1, triCuts_cls]; simp only [h1, if_false, T.f_ne_t 1 2, T.f_ne_t 1 1]
    split_ifs <;> simp [Cls.base]
  · subst h
    have h1 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
    have h2 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
    rw [triCls_f0, triCuts_cls]; simp only [h1, h2, if_false, T.f_ne_t 0 2, T.f_ne_t 0 1]
    split_ifs <;> simp [Cls.base]
  · have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ h)
    rw [triCls_other T Q kp hf, triCuts_cls]
    simp [hf 0, hf 1, hf 2, hP' 0, hP' 1, hP' 2]

theorem triCuts_cls_t (j : Fin 3) : (triCuts s T).cls (T.t j) = .beta := by
  rw [triCuts_cls]
  have t01 : T.t 1 ≠ T.t 0 := T.t_ne (by decide)
  have t02 : T.t 2 ≠ T.t 0 := T.t_ne (by decide)
  have t12 : T.t 2 ≠ T.t 1 := T.t_ne (by decide)
  fin_cases j
  · simp [t01.symm, t02.symm, (T.f_ne_t 0 0).symm, (T.f_ne_t 1 0).symm, (T.f_ne_t 2 0).symm]
  · simp [t01, t12.symm, (T.f_ne_t 0 1).symm, (T.f_ne_t 1 1).symm, (T.f_ne_t 2 1).symm]
  · simp [t02, t12, (T.f_ne_t 0 2).symm, (T.f_ne_t 1 2).symm, (T.f_ne_t 2 2).symm]

theorem Inv.triSt {R : ℕ} (hI : Inv R s) (hcl : PClosed T.kept (triKeep s T))
    (h3 : ∀ j, s.cls (T.t j) = .eps → 3 ≤ s.M.deg (T.t j)) :
    Inv R (triSt s T Q kp hcl) := by
  have h1 := hI.triCuts T h3
  have h2 : Inv R ((FinalCountG3.triCuts s T).delSt T.TP T.pclosed) := by
    refine h1.delSt _ _ ?_
    intro a _ hna
    obtain ⟨j, rfl⟩ := (T.not_TP_iff a).1 hna
    rw [triCuts_cls_t]
    exact (T.m3_deg_t j).symm ▸ rfl
  have h3 : Inv R (((FinalCountG3.triCuts s T).delSt T.TP T.pclosed).withCls (triCls s T Q kp)) := by
    refine h2.withCls _ ?_
    intro a ha
    have ha' : a ∈ T.m3.atoms.filter T.TP := ha
    rw [Finset.mem_filter] at ha'
    exact tri_cls_agree T Q kp a ha'.1 ha'.2
  refine h3.delSt (triKeep s T) hcl ?_
  intro a ha hna
  have hna' : ∃ j, s.cls (T.t j) ≠ .eps ∧ a = T.f j := by
    unfold triKeep at hna
    push Not at hna
    exact hna
  obtain ⟨j, hj, rfl⟩ := hna'
  have hP : T.TP (T.f j) := fun i e => T.f_ne_t j i e
  have hdegM : s.M.deg (T.t j) = 2 := by
    have := (hI.ab (T.t j) (T.t_mem j) hj).1
    have := tri_deg_ge_two T j
    omega
  have hdeg : T.kept.deg (T.f j) = 0 := by
    have h5 := tri_deg_f T j
    have h6 : T.kept.deg (T.f j) = T.m3.deg (T.f j) := restrictP_deg T.m3 T.TP T.pclosed hP
    omega
  show (triCls s T Q kp (T.f j)).base = T.kept.deg (T.f j)
  rw [hdeg]
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · rw [triCls_f0]; simp [hj]; rfl
  · rw [triCls_f1]; simp [hj]; rfl
  · rw [triCls_f2]; simp [hj]; rfl

end tri

end WaveTurbulence.FinalCountG3
