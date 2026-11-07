/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmStuck
public import WaveTurbulence.Foundations.FinalCount.G3RunN
/-! **FINALCOUNT-ASSEMBLY, M7 (phase 4): existence of the `β`-cut phase.**  `epsCount` (the number of `ε` atoms) strictly
decreases along every cut `ε → β,β`; `HStep4` is such a cut; so from every state satisfying `InvE` there is a reachable state in which no
`HStep4` is enabled, and (by `Inv.ab`: a non-`ε` atom has degree `≤ 2`) that state satisfies `NoBetaCut`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} {R : ℕ}

/-- The number of `ε` atoms of a state. -/
noncomputable def epsCount (s : St.{u} V D₀) : ℕ := (s.M.atoms.filter (fun a => s.cls a = .eps)).card

theorem epsCount_cutSt_lt (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂)
    (hε : s.cls v = .eps) (c₁ c₂ : Cls) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps) :
    epsCount (s.cutSt v v₂ x₁ x₂ c₁ c₂) < epsCount s := by
  have hv : v ∈ s.M.atoms := hcd.1
  have hat : (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms = insert v₂ s.M.atoms := rfl
  have hsub : (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms.filter (fun a => (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = .eps) ⊆
      (s.M.atoms.filter (fun a => s.cls a = .eps)).erase v := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    rw [hat] at ha1
    have hcl : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls = Function.update (Function.update s.cls v c₁) v₂ c₂ := rfl
    rw [hcl] at ha2
    by_cases h1 : a = v₂
    · rw [h1, Function.update_self] at ha2; exact absurd ha2 h₂
    · by_cases h2 : a = v
      · have : Function.update (Function.update s.cls v c₁) v₂ c₂ a = c₁ := by
          rw [Function.update_of_ne h1, h2, Function.update_self]
        rw [this] at ha2; exact absurd ha2 h₁
      · rw [Function.update_of_ne h1, Function.update_of_ne h2] at ha2
        have : a ∈ s.M.atoms := by
          rcases Finset.mem_insert.1 ha1 with h | h
          · exact absurd h h1
          · exact h
        exact Finset.mem_erase.2 ⟨h2, Finset.mem_filter.2 ⟨this, ha2⟩⟩
  unfold epsCount
  refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.2 ⟨hv, hε⟩)

theorem epsCount_step4 {h h' : HSt V D₀} (hs : HStep4 L w κ h h') : epsCount h'.s < epsCount h.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    exact epsCount_cutSt_lt h.s hc hε .beta .beta (by simp) (by simp)

/-- **Phase 4 exists**: from any state satisfying `InvE` the `β`-cut phase can be run to its stop condition. -/
theorem exists_phase4 (h₃ : HSt V D₀) (hI : InvE M₀ R 0 L γ η w κ h₃) :
    ∃ hf : HSt V D₀, Relation.ReflTransGen (HStep4 L w κ) h₃ hf ∧ InvE M₀ R 0 L γ η w κ hf ∧
      NoBetaCut L w κ hf.s := by
  obtain ⟨hf, hr, hP, hstuck⟩ := exists_stuck_inv (HStep4 L w κ) (fun h => epsCount h.s)
    (InvE M₀ R 0 L γ η w κ) (fun _ _ hs => epsCount_step4 hs) (fun _ _ hs hI => hI.step4 hs) h₃ hI
  refine ⟨hf, hr, hP, ?_⟩
  intro v hv hdeg v₂ x₁ x₂ hc hnz
  by_contra hβ
  have hε : hf.s.cls v = .eps := by
    by_contra hne
    have := ((hP.good0 rfl).1.ab v hv hne).1
    omega
  exact hstuck _ (HStep4.cut hf v v₂ x₁ x₂ hc hε hβ hnz hdeg)

end WaveTurbulence.FinalCountAsm
