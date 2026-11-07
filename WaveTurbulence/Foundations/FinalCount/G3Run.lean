/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Tri
/-! **FINALCOUNT-G3**: the invariants `Inv`, `Clean` along a run of the algorithm. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

/-- No ghost atoms. -/
def Clean (s : St.{u} V D₀) : Prop := ∀ a ∈ s.M.atoms, s.cls a ≠ .ghost

/-- Both invariants. -/
def Good (R : ℕ) (s : St.{u} V D₀) : Prop := Inv R s ∧ Clean s

theorem alphaOrBeta_isAB (fpos fpre : ℕ) (R : ℝ) (kp : ℕ) : (alphaOrBeta fpos fpre R kp).IsAB := by
  unfold alphaOrBeta; split_ifs <;> trivial

theorem Clean.cutSt {s : St.{u} V D₀} (hC : Clean s) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls)
    (h₁ : c₁ ≠ .ghost) (h₂ : c₂ ≠ .ghost) : Clean (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  intro a ha
  show Function.update (Function.update s.cls v c₁) v₂ c₂ a ≠ _
  by_cases h1 : a = v₂
  · rw [h1, Function.update_self]; exact h₂
  · rw [Function.update_of_ne h1]
    by_cases h2 : a = v
    · rw [h2, Function.update_self]; exact h₁
    · rw [Function.update_of_ne h2]
      have ha' : a ∈ insert v₂ s.M.atoms := ha
      exact hC a ((Finset.mem_insert.1 ha').resolve_left h1)

theorem Clean.delSt {s : St.{u} V D₀} (hC : Clean s) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) :
    Clean (s.delSt P h) := by
  intro a ha
  exact hC a (Finset.mem_filter.1 ha).1

theorem Step3.good {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step3 L γ η w κ s s') (hg : Good R s) : Good R s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim h3 =>
    have hab : (if s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by
      split_ifs <;> trivial
    have hbase := Cls.base_eq_two hab
    have hne := Cls.ne_eps_of_isAB hab
    have hng := Cls.ne_ghost_of_isAB hab
    refine ⟨hg.1.cutSt hcd _ _ (by rw [hε, hbase]; rfl) hne hne hng (fun h => absurd h hng)
      (fun _ => h3), ?_⟩
    exact hg.2.cutSt v v₂ x₁ x₂ _ _ hng hng

theorem Step4.good {R : ℕ} {s s' : St.{u} V D₀} (h : Step4 s s') (hg : Good R s) : Good R s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 =>
    refine ⟨hg.1.cutSt hcd _ _ (by rw [hε]; rfl) (by simp) (by simp) (by simp) (fun h => by simp at h)
      (fun _ => h3), ?_⟩
    exact hg.2.cutSt v v₂ x₁ x₂ _ _ (by simp) (by simp)


theorem Step1.good {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hg : Good R s) : Good R s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents s.M.numComponents R' kp
    have hng := Cls.ne_ghost_of_isAB hab
    refine ⟨hg.1.vineSt K _ hab hu hl h3a h3b, ?_⟩
    exact ((hg.2.cutSt _ _ _ _ _ _ hng hng).cutSt _ _ _ _ _ _ hng hng).delSt _ _

theorem Step2.good {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step2 L γ η w κ s s') (hg : Good R s) : Good R s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 =>
    refine ⟨hg.1.triSt T Q kp hcl h3, ?_⟩
    intro a ha
    have ha' : a ∈ T.m3.atoms.filter T.TP ∧ triKeep s T a := by
      have : a ∈ (T.m3.atoms.filter T.TP).filter (triKeep s T) := ha
      exact Finset.mem_filter.1 this
    obtain ⟨ha1, hk⟩ := ha'
    obtain ⟨ham, _⟩ := Finset.mem_filter.1 ha1
    show triCls s T Q kp a ≠ .ghost
    rw [TriData.m3_atoms] at ham
    simp only [Finset.mem_insert] at ham
    rcases ham with h | h | h | h
    · subst h
      have : s.cls (T.t 2) = .eps := by by_contra hne; exact hk 2 hne rfl
      rw [triCls_f2]; simp [this]
    · subst h
      have : s.cls (T.t 1) = .eps := by by_contra hne; exact hk 1 hne rfl
      rw [triCls_f1]; simp only [this, if_true]; split_ifs <;> simp
    · subst h
      have : s.cls (T.t 0) = .eps := by by_contra hne; exact hk 0 hne rfl
      rw [triCls_f0]; simp only [this, if_true]; split_ifs <;> simp
    · have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ h)
      rw [triCls_other T Q kp hf]
      exact hg.2 a h

end WaveTurbulence.FinalCountG3
