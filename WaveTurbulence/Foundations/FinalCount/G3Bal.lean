/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Run
public import WaveTurbulence.Foundations.FinalCount.G3Init
/-! **FINALCOUNT-G3: balance of the degree-`2` atoms.**  `BalM M`: degree bounds `≤ 2` and every atom of degree `2`
has one incoming and one outgoing bond.  Preserved by cuts and restrictions, hence along a run. -/
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

/-- Degree bounds and balance of the degree-`2` atoms. -/
def BalM (M : Molecule V D) : Prop :=
  (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) ∧
    ∀ a ∈ M.atoms, M.deg a = 2 → M.outdeg a = 1 ∧ M.indeg a = 1

theorem BalM.cut {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D} (hB : BalM M) (hcd : M.IsCutData v v₂ x₁ x₂) :
    BalM (M.cut v v₂ x₁ x₂) := by
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
  · intro a ha hd
    have ha' : a ∈ insert v₂ M.atoms := ha
    by_cases h1 : a = v₂
    · subst h1; omega
    · by_cases h2 : a = v
      · subst h2; rw [cut_outdeg_v hcd, cut_indeg_v hcd]; omega
      · rw [cut_outdeg_other hcd h2 h1, cut_indeg_other hcd h2 h1]
        rw [cut_deg_other hcd h2 h1] at hd
        exact hB.2 a ((Finset.mem_insert.1 ha').resolve_left h1) hd

theorem BalM.restrict {M : Molecule V D} (hB : BalM M) (P : V → Prop) [DecidablePred P] (h : PClosed M P) :
    BalM (restrictP M P h) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : a ∈ M.atoms.filter P := ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ha'
    rw [restrictP_outdeg M P h h2, restrictP_indeg M P h h2]
    exact hB.1 a h1
  · intro a ha hd
    have ha' : a ∈ M.atoms.filter P := ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ha'
    rw [restrictP_deg M P h h2] at hd
    rw [restrictP_outdeg M P h h2, restrictP_indeg M P h h2]
    exact hB.2 a h1 hd

end bal

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

theorem BalM.cutSt {s : St.{u} V D₀} {v v₂ : V} {x₁ x₂ : s.D} (hB : BalM s.M) (hcd : s.M.IsCutData v v₂ x₁ x₂)
    (c₁ c₂ : Cls) : BalM (s.cutSt v v₂ x₁ x₂ c₁ c₂).M := hB.cut hcd

theorem Step1.bal {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') (hB : BalM s.M) : BalM s'.M := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    exact BalM.restrict ((hB.cut K.cut_a).cut K.cut_b) _ K.closed

theorem Step2.bal {s s' : St.{u} V D₀} (h : Step2 L γ η w κ s s') (hB : BalM s.M) : BalM s'.M := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 =>
    have h3 : BalM T.m3 := ((hB.cut T.cd1).cut T.cd2).cut T.cd3
    exact BalM.restrict (BalM.restrict h3 _ T.pclosed) _ hcl

theorem Step3.bal {s s' : St.{u} V D₀} (h : Step3 L γ η w κ s s') (hB : BalM s.M) : BalM s'.M := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R kp hR hkp hε hsg hsim h3 => exact hB.cut hcd

theorem Step4.bal {s s' : St.{u} V D₀} (h : Step4 s s') (hB : BalM s.M) : BalM s'.M := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact hB.cut hcd

theorem bal_rtg {step : St.{u} V D₀ → St.{u} V D₀ → Prop} (hstep : ∀ s s', step s s' → BalM s.M → BalM s'.M)
    {a b : St.{u} V D₀} (h : Relation.ReflTransGen step a b) : BalM a.M → BalM b.M := by
  induction h with
  | refl => exact id
  | tail _ hs ih => exact fun g => hstep _ _ hs (ih g)

theorem Run.bal {R : ℕ} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {sf : St.{u} V D₀}
    (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) : BalM sf.M := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : BalM (St.init M₀).M := ⟨hS.bounds, fun a ha hd => by have := hS.deg3 a ha; have hd' : M₀.deg a = 2 := hd; omega⟩
  exact bal_rtg (fun _ _ h g => Step4.bal h g) h4 (bal_rtg (fun _ _ h g => Step3.bal h g) h3
    (bal_rtg (fun _ _ h g => Step2.bal h g) h2 (bal_rtg (fun _ _ h g => Step1.bal h g) h1 g0)))

end WaveTurbulence.FinalCountG3
