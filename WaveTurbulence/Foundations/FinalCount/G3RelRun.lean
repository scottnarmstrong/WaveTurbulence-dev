/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Rel
/-! **FINALCOUNT-G3**: `DartRel` along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀}

theorem Step1.rel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hr : DartRel M₀ s) : DartRel M₀ s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents s.M.numComponents R' kp
    have hce := Cls.ne_eps_of_isAB hab
    have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ _ _ hce hce K.cut_a.2.1
    have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ _ _ hce hce K.cut_b.2.1
    exact h2.delSt _ K.closed

theorem Step2.rel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (h : Step2 L γ η w κ s s') (hr : DartRel M₀ s) : DartRel M₀ s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 =>
    have c0 : (if s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c1 : (if s.cls (T.t 1) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c2 : (if s.cls (T.t 2) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have h1 := hr.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta _ (by simp) c0 (T.f_fresh 0)
    have h2 := h1.cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta _ (by simp) c1 T.f_fresh_m1
    have h3 := h2.cutSt (T.t 2) (T.f 2) (T.a 2) (T.b 2) .beta _ (by simp) c2 T.f_fresh_m2
    have h4 := h3.delSt T.TP T.pclosed
    have h5 := h4.withCls (triCls s T Q kp) (fun a ha => by
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact (tri_cls_agree T Q kp a ha'.1 ha'.2).2.1)
    exact h5.delSt _ hcl

theorem Step3.rel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s s' : St.{u} V D₀}
    (h : Step3 L γ η w κ s s') (hr : DartRel M₀ s) : DartRel M₀ s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim h3 =>
    have hab : (if s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by
      split_ifs <;> trivial
    exact hr.cutSt v v₂ x₁ x₂ _ _ (Cls.ne_eps_of_isAB hab) (Cls.ne_eps_of_isAB hab) hcd.2.1

theorem Step4.rel {s s' : St.{u} V D₀} (h : Step4 s s') (hr : DartRel M₀ s) : DartRel M₀ s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact hr.cutSt v v₂ x₁ x₂ _ _ (by simp) (by simp) hcd.2.1

end WaveTurbulence.FinalCountG3
