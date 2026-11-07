/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompStep
/-! **FINALCOUNT-G3**: `CompBeta` along Step 2 (triangles). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

theorem CompBeta.cutβ_tri {s : St.{u} V D₀} {R : ℕ} (hI : Inv R s) (hC : CompBeta s) {v v₂ : V} {x₁ x₂ : s.D}
    (hcd : s.M.IsCutData v v₂ x₁ x₂) (c2 : Cls)
    (h1 : s.cls v = .eps → c2 = .beta) (h2 : s.cls v ≠ .eps → c2 = .ghost) :
    CompBeta (s.cutSt v v₂ x₁ x₂ .beta c2) := by
  by_cases hε : s.cls v = .eps
  · exact hC.cutβ hcd c2 (Or.inl (h1 hε))
  · refine hC.cutβ hcd c2 (Or.inr ⟨h2 hε, ?_⟩)
    have hab := hI.ab v hcd.1 hε
    have hne : x₁ ≠ x₂ := cut_x_ne hcd
    have : ({x₁, x₂} : Finset s.D) ⊆ s.M.dartsAt v := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_dartsAt s.M v _).2 hcd.2.2.1
      · exact (mem_dartsAt s.M v _).2 hcd.2.2.2.1
    have h := Finset.card_le_card this
    rw [Finset.card_pair hne] at h
    have : s.M.deg v ≤ 2 := hab.1
    unfold Molecule.deg at *; omega

section tri
variable {s : St.{u} V D₀} (T : TriData s.M)

theorem triCuts_inv_comp {R : ℕ} (hI : Inv R s) (hC : CompBeta s)
    (h3 : ∀ j, s.cls (T.t j) = .eps → 3 ≤ s.M.deg (T.t j)) :
    Inv R (triCuts s T) ∧ CompBeta (triCuts s T) := by
  have t01 : T.t 1 ≠ T.t 0 := T.t_ne (by decide)
  have t02 : T.t 2 ≠ T.t 0 := T.t_ne (by decide)
  have t12 : T.t 2 ≠ T.t 1 := T.t_ne (by decide)
  have hs1 : Inv R (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)) :=
    hI.cutSt_tri T.cd1 _ (fun h => by simp [h]) (fun h => by simp [h]) (h3 0)
  have hC1 : CompBeta (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)) :=
    hC.cutβ_tri hI T.cd1 _ (fun h => by simp [h]) (fun h => by simp [h])
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
  have hC2 : CompBeta ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)) :=
    hC1.cutβ_tri hs1 T.cd2 _ (fun h => by rw [hc1] at h; simp [h]) (fun h => by rw [hc1] at h; simp [h])
  have hc2 : ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)).cls (T.t 2) = s.cls (T.t 2) := by
    simp only [St.cutSt, Function.update_apply, t02, t12, (T.f_ne_t 0 2).symm, (T.f_ne_t 1 2).symm, if_false]
  exact ⟨hs2.cutSt_tri T.cd3 _ (fun h => by rw [hc2] at h; simp [h]) (fun h => by rw [hc2] at h; simp [h])
      (fun h => by
        rw [hc2] at h
        have := h3 2 h
        show 3 ≤ (T.m1.cut (T.t 1) (T.f 1) (T.a 1) (T.b 1)).deg (T.t 2)
        rw [cut_deg_other T.cd2 t12 (T.f_ne_t 1 2).symm]
        show 3 ≤ (s.M.cut (T.t 0) (T.f 0) (T.a 0) (T.b 0)).deg (T.t 2)
        rw [cut_deg_other T.cd1 t02 (T.f_ne_t 0 2).symm]; exact this),
    hC2.cutβ_tri hs2 T.cd3 _ (fun h => by rw [hc2] at h; simp [h]) (fun h => by rw [hc2] at h; simp [h])⟩

theorem tri_kept_deg_f {R : ℕ} (hI : Inv R s) (j : Fin 3) (hj : s.cls (T.t j) ≠ .eps) :
    T.kept.deg (T.f j) = 0 := by
  have hP : T.TP (T.f j) := fun i e => T.f_ne_t j i e
  have hdegM : s.M.deg (T.t j) = 2 := by
    have := (hI.ab (T.t j) (T.t_mem j) hj).1
    have := tri_deg_ge_two T j
    omega
  have h5 := tri_deg_f T j
  have h6 : T.kept.deg (T.f j) = T.m3.deg (T.f j) := restrictP_deg T.m3 T.TP T.pclosed hP
  omega

theorem tri_sc_f_iso {R : ℕ} (hI : Inv R s) (j : Fin 3) (hj : s.cls (T.t j) ≠ .eps) {x : V}
    (h : T.kept.SameComponent x (T.f j)) : x = T.f j :=
  sc_isolated T.kept (tri_kept_deg_f T hI j hj) h

variable (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem tri_compBeta {R : ℕ} (hI : Inv R s) (hC : CompBeta s) (hcl : PClosed T.kept (triKeep s T))
    (h3 : ∀ j, s.cls (T.t j) = .eps → 3 ≤ s.M.deg (T.t j)) :
    CompBeta (triSt s T Q kp hcl) := by
  obtain ⟨hIc, hCc⟩ := triCuts_inv_comp T hI hC h3
  have h2 := hCc.delSt T.TP T.pclosed
  have h3 : CompBeta (((triCuts s T).delSt T.TP T.pclosed).withCls (triCls s T Q kp)) := by
    refine h2.withCls _ ?_ ?_ ?_
    · intro a ha
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact (tri_cls_agree T Q kp a ha'.1 ha'.2).2.2
    · intro a ha
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact (tri_cls_agree T Q kp a ha'.1 ha'.2).1
    · intro b hb hbeta hne
      have hbeta : (triCuts s T).cls b = .beta := hbeta
      have hne : triCls s T Q kp b ≠ .beta := hne
      have hb' : b ∈ T.m3.atoms.filter T.TP := hb
      obtain ⟨hbm, hbP⟩ := Finset.mem_filter.1 hb'
      have hmem : ∀ j : Fin 3, T.f j ∈ T.m3.atoms.filter T.TP := fun j => by
        refine Finset.mem_filter.2 ⟨?_, fun i e => T.f_ne_t j i e⟩
        rw [TriData.m3_atoms]; fin_cases j <;> simp
      have t2e : s.cls (T.t 2) = .eps → triCls s T Q kp (T.f 2) = .beta := fun h => by
        rw [triCls_f2]; simp [h]
      rw [TriData.m3_atoms] at hbm
      simp only [Finset.mem_insert] at hbm
      rcases hbm with h | h | h | h
      · subst h
        rw [triCls_f2] at hne; rw [triCuts_cls] at hbeta
        by_cases he : s.cls (T.t 2) = .eps
        · exact absurd (by simp [he]) hne
        · simp [he] at hbeta
      · subst h
        have h12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
        rw [triCuts_cls] at hbeta
        simp only [h12, T.f_ne_t 1 2, T.f_ne_t 1 1, if_false, if_true] at hbeta
        have he1 : s.cls (T.t 1) = .eps := by
          by_contra he; simp [he] at hbeta
        rw [triCls_f1] at hne
        simp only [he1, if_true] at hne
        have hsc : T.kept.SameComponent (T.f 1) (T.f 2) := by
          by_contra hn; exact hne (by simp [hn])
        have he2 : s.cls (T.t 2) = .eps := by
          by_contra he2; exact h12 (tri_sc_f_iso T hI 2 he2 hsc)
        exact ⟨T.f 2, hmem 2, hsc, t2e he2⟩
      · subst h
        have h02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
        have h01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
        rw [triCuts_cls] at hbeta
        simp only [h02, h01, T.f_ne_t 0 2, T.f_ne_t 0 1, T.f_ne_t 0 0, if_false, if_true] at hbeta
        have he0 : s.cls (T.t 0) = .eps := by
          by_contra he; simp [he] at hbeta
        rw [triCls_f0] at hne
        simp only [he0, if_true] at hne
        have hor : T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1) := by
          by_contra hn; exact hne (by simp [hn])
        by_cases hsc2 : T.kept.SameComponent (T.f 0) (T.f 2)
        · have he2 : s.cls (T.t 2) = .eps := by
            by_contra he2; exact h02 (tri_sc_f_iso T hI 2 he2 hsc2)
          exact ⟨T.f 2, hmem 2, hsc2, t2e he2⟩
        · have hsc1 := hor.resolve_left hsc2
          have he1 : s.cls (T.t 1) = .eps := by
            by_contra he1; exact h01 (tri_sc_f_iso T hI 1 he1 hsc1)
          have hn12 : ¬ T.kept.SameComponent (T.f 1) (T.f 2) := fun h =>
            hsc2 (Relation.EqvGen.trans _ _ _ hsc1 h)
          refine ⟨T.f 1, hmem 1, hsc1, ?_⟩
          rw [triCls_f1]; simp [he1, hn12]
      · exfalso
        have hf : ∀ j, b ≠ T.f j := fun j e => T.f_fresh j (e ▸ h)
        apply hne
        rw [triCls_other T Q kp hf]
        rw [triCuts_cls] at hbeta
        have hP' : ∀ j, b ≠ T.t j := hbP
        simpa [hf 0, hf 1, hf 2, hP' 0, hP' 1, hP' 2] using hbeta
  exact h3.delSt (triKeep s T) hcl

end tri

end WaveTurbulence.FinalCountG3
