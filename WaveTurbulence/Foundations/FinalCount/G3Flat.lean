/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Final1
public import WaveTurbulence.Foundations.FinalCount.G3Run
/-! **FINALCOUNT-G3: the flatness invariant** `Flat s` (`contrib ≤ 1` at every atom).

It carries the *erasure-free* strengthening of `Inv`: in a state without tame-atom erasures (TARGET Remark `remtame`,
case (ii)) the `ε`-atoms have degree `≥ 3` and there are exactly `2R` atoms of odd degree.  (After an erasure the
neighbours of the erased atom can have defect `≥ 2`.) -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

/-- Every atom has defect `contrib ≤ 1`. -/
def Flat (s : St.{u} V D₀) : Prop := ∀ a ∈ s.M.atoms, contrib s a ≤ 1

section
variable {s : St.{u} V D₀} {R : ℕ}

theorem Flat.cutSt (hF : Flat s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls)
    (hc : c₁.base + c₂.base = (s.cls v).base) (h2 : c₁.base = 2) : Flat (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  have hv : v ∈ s.M.atoms := hcd.1
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  intro a ha
  have ha' : a ∈ insert v₂ s.M.atoms := ha
  unfold contrib
  show ((s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a).base - ((s.M.cut v v₂ x₁ x₂).deg a : ℤ) ≤ 1
  by_cases h1 : a = v₂
  · have e1 : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = c₂ := by
      show Function.update (Function.update s.cls v c₁) v₂ c₂ a = c₂; rw [h1]; simp
    have e2 := cut_deg_v₂ hcd
    have := hF v hv
    unfold contrib at this
    rw [e1, h1]; omega
  · by_cases h3 : a = v
    · subst h3
      have e1 : (s.cutSt a v₂ x₁ x₂ c₁ c₂).cls a = c₁ := by
        show Function.update (Function.update s.cls a c₁) v₂ c₂ a = c₁
        rw [Function.update_of_ne hne.symm]; simp
      rw [e1, cut_deg_v s.M hcd]; omega
    · have e1 : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = s.cls a := by
        show Function.update (Function.update s.cls v c₁) v₂ c₂ a = _
        rw [Function.update_of_ne h1, Function.update_of_ne h3]
      rw [e1, cut_deg_other hcd h3 h1]
      exact hF a ((Finset.mem_insert.1 ha').resolve_left h1)

theorem Flat.delSt (hF : Flat s) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) : Flat (s.delSt P h) := by
  intro a ha
  have haP : a ∈ s.M.atoms ∧ P a := Finset.mem_filter.1 ha
  have := hF a haP.1
  unfold contrib at this ⊢
  show (s.cls a).base - ((restrictP s.M P h).deg a : ℤ) ≤ 1
  rw [restrictP_deg s.M P h haP.2]; exact this

theorem Flat.withCls (hF : Flat s) (c : V → Cls) (h : ∀ a ∈ s.M.atoms, (c a).base = (s.cls a).base) :
    Flat (s.withCls c) := by
  intro a ha
  have := hF a ha
  unfold contrib at this ⊢
  show (c a).base - _ ≤ 1
  rw [h a ha]; exact this

theorem Flat.init [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} (h : SubHyp R M₀) : Flat (St.init M₀) := by
  intro a ha
  have h3 := h.deg3 a ha
  unfold contrib
  show ((Cls.eps).base) - (M₀.deg a : ℤ) ≤ 1
  simp only [Cls.base]; omega


theorem Cls.base_two_of_ne {c : Cls} (h1 : c ≠ .eps) (h2 : c ≠ .ghost) : c.base = 2 := by
  cases c <;> simp_all [Cls.base]

theorem Flat.cutSt_tri (hF : Flat s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂) (c2 : Cls)
    (h1 : s.cls v = .eps → c2 = .beta) (h2 : s.cls v ≠ .eps → c2 = .ghost)
    (hb : s.cls v ≠ .eps → (s.cls v).base = 2) : Flat (s.cutSt v v₂ x₁ x₂ .beta c2) := by
  by_cases hε : s.cls v = .eps
  · have := h1 hε; subst this
    exact hF.cutSt hcd _ _ (by rw [hε]; rfl) rfl
  · have := h2 hε; subst this
    exact hF.cutSt hcd _ _ (by rw [hb hε]; rfl) rfl

theorem Flat.triCuts (hF : Flat s) (hC : Clean s) (T : TriData s.M) : Flat (triCuts s T) := by
  have t01 : T.t 1 ≠ T.t 0 := T.t_ne (by decide)
  have t02 : T.t 2 ≠ T.t 0 := T.t_ne (by decide)
  have t12 : T.t 2 ≠ T.t 1 := T.t_ne (by decide)
  have hbase : ∀ j, s.cls (T.t j) ≠ .eps → (s.cls (T.t j)).base = 2 := fun j hj =>
    Cls.base_two_of_ne hj (hC _ (T.t_mem j))
  have hs1 : Flat (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)) :=
    hF.cutSt_tri T.cd1 _ (fun h => by simp [h]) (fun h => by simp [h]) (hbase 0)
  have hc1 : (s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cls (T.t 1) = s.cls (T.t 1) := by
    simp only [St.cutSt, Function.update_apply, t01, (T.f_ne_t 0 1).symm, ite_false]
  have hs2 : Flat ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)) :=
    hs1.cutSt_tri T.cd2 _ (fun h => by rw [hc1] at h; simp [h]) (fun h => by rw [hc1] at h; simp [h])
      (fun h => by rw [hc1] at h ⊢; exact hbase 1 h)
  have hc2 : ((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta
      (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta
      (if s.cls (T.t 1) = .eps then .beta else .ghost)).cls (T.t 2) = s.cls (T.t 2) := by
    simp only [St.cutSt, Function.update_apply, t02, t12, (T.f_ne_t 0 2).symm, (T.f_ne_t 1 2).symm, ite_false]
  exact hs2.cutSt_tri T.cd3 _ (fun h => by rw [hc2] at h; simp [h]) (fun h => by rw [hc2] at h; simp [h])
    (fun h => by rw [hc2] at h ⊢; exact hbase 2 h)


theorem Flat.vineSt (hF : Flat s) (K : VineCut s.M) (c : Cls) (hc : c.IsAB)
    (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps) : Flat (vineSt s K c) := by
  have hc2 := Cls.base_eq_two hc
  have hF1 := hF.cutSt K.cut_a c c (by rw [hu, hc2]; rfl) hc2
  have hlow : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cls K.C.lower = .eps := by
    show Function.update (Function.update s.cls K.C.upper c) K.fa c K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]; exact hl
  have hF2 := hF1.cutSt K.cut_b c c (by rw [hlow, hc2]; rfl) hc2
  exact hF2.delSt _ K.closed

theorem Flat.triSt (hF : Flat s) (hC : Clean s) (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep s T)) : Flat (triSt s T Q kp hcl) := by
  have h1 := hF.triCuts hC T
  have h2 := h1.delSt T.TP T.pclosed
  have h3 := h2.withCls (triCls s T Q kp) (fun a ha => by
    have ha' : a ∈ T.m3.atoms.filter T.TP := ha
    rw [Finset.mem_filter] at ha'
    exact (tri_cls_agree T Q kp a ha'.1 ha'.2).1)
  exact h3.delSt _ hcl

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {s' : St.{u} V D₀}

theorem Step1.flat (h : Step1 L γ η w κ s s') (hF : Flat s) : Flat s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    exact hF.vineSt K _ (alphaOrBeta_isAB _ _ _ _) hu hl

theorem Step2.flat (h : Step2 L γ η w κ s s') (hF : Flat s) (hC : Clean s) : Flat s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 => exact hF.triSt hC T Q kp hcl

theorem Step3.flat (h : Step3 L γ η w κ s s') (hF : Flat s) : Flat s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim h3 =>
    have hab : (if s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by split_ifs <;> trivial
    have hb := Cls.base_eq_two hab
    exact hF.cutSt hcd _ _ (by rw [hε, hb]; rfl) hb

theorem Step4.flat (h : Step4 s s') (hF : Flat s) : Flat s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact hF.cutSt hcd _ _ (by rw [hε]; rfl) rfl


theorem Flat.eps3 (hF : Flat s) {a : V} (ha : a ∈ s.M.atoms) (he : s.cls a = .eps) : 3 ≤ s.M.deg a := by
  have := hF a ha
  unfold contrib at this
  rw [he] at this; simp only [Cls.base] at this; omega

theorem Cls.even_base (c : Cls) : Even c.base := by cases c <;> simp [Cls.base] <;> decide

theorem Flat.contrib_eq (hF : Flat s) (hg : Good R s) {a : V} (ha : a ∈ s.M.atoms) :
    contrib s a = if ¬ Even (s.M.deg a) then 1 else 0 := by
  have h0 := hg.contrib_nonneg ha
  have h1 := hF a ha
  have hpar : Even (contrib s a + (s.M.deg a : ℤ)) := by
    unfold contrib; simp only [sub_add_cancel]; exact Cls.even_base _
  by_cases he : Even (s.M.deg a)
  · have : Even (contrib s a) := by
      have h2 : Even ((s.M.deg a : ℕ) : ℤ) := (Int.even_coe_nat _).2 he
      exact (Int.even_add.1 hpar).2 h2
    rw [if_neg (by simpa using he)]
    obtain ⟨k, hk⟩ := this; omega
  · have : ¬ Even (contrib s a) := by
      intro hc
      have h2 : Even ((s.M.deg a : ℕ) : ℤ) := (Int.even_add.1 hpar).1 hc
      exact he ((Int.even_coe_nat _).1 h2)
    rw [if_pos he]
    have hodd : Odd (contrib s a) := Int.not_even_iff_odd.1 this
    obtain ⟨k, hk⟩ := hodd; omega

/-- In a flat state, the number of atoms of odd degree is exactly `2R`. -/
theorem Flat.odd_card (hF : Flat s) (hg : Good R s) :
    (s.M.atoms.filter fun a => ¬ Even (s.M.deg a)).card = 2 * R := by
  have key : ∀ a ∈ s.M.atoms, contrib s a = if ¬ Even (s.M.deg a) then 1 else 0 :=
    fun a ha => hF.contrib_eq hg ha
  have hsum := hg.sum_contrib
  rw [Finset.sum_congr rfl key] at hsum
  rw [Finset.card_filter]
  have : (((∑ a ∈ s.M.atoms, if ¬ Even (s.M.deg a) then 1 else 0 : ℕ)) : ℤ) = 2 * R := by
    rw [← hsum]; push_cast; rfl
  exact_mod_cast this

end
end WaveTurbulence.FinalCountG3
