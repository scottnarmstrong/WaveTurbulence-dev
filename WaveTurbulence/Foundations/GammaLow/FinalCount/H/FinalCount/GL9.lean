/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL9`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 9**: facts along the LOW run: auxiliary invariants, `NoEligibleTriangle`, `EpsLe`, `eps_back`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- The state after Step 2 satisfies the invariants with some index `≤ R`. -/
theorem HRunL.inv3 {C : CollData M₀} {h₀ h₃ : HSt V D₀} {h₁ h₂ : HSt V D₀}
    (a1 : Relation.ReflTransGen (HStep1L C L γ η w κ) h₀ h₁)
    (a2 : Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂)
    (a3 : Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃) (h0 : InvL M₀ R L γ η w κ h₀) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h₃ := by
  let P : HSt V D₀ → Prop := fun h => ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → ∀ R', InvL M₀ R' L γ η w κ a →
      ∃ R'', R'' ≤ R' ∧ InvL M₀ R'' L γ η w κ b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → P a → P b := by
    intro S hS a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih =>
      obtain ⟨R', hR', hI⟩ := ih
      obtain ⟨R'', hR'', hI''⟩ := hS _ _ hs R' hI
      exact ⟨R'', hR''.trans hR', hI''⟩
  exact key (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) a3
    (key (fun a b hs R' hI => hI.stepD3'L hs) a2
    (key (fun a b hs R' hI => hI.step1LL hs) a1 ⟨R, le_rfl, h0⟩))

/-- The auxiliary invariants and the nonexistence of eligible triangles, at the end of the run. -/
theorem HRunL.final {C : CollData M₀} {h₀ hf : HSt V D₀} (hr : HRunL C L γ η w κ h₀ hf)
    (hS : SubHypL R M₀) (obl : SubproOblG C L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hinit : h₀ = HSt.init M₀) :
    RunAux M₀ C hf ∧ NoEligibleTriangle C L γ η w κ hf := by
  subst hinit
  obtain ⟨h₁, h₂, h₃, h₄, a1, -, a2, -, a3, n3, a4, hsgl, a5, -⟩ := hr
  have i0 : InvL M₀ R L γ η w κ (HSt.init M₀) := InvL.init hS h0
  obtain ⟨R₃, hR₃, i3⟩ := HRunL.inv3 a1 a2 a3 i0
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → RunAux M₀ C a → RunAux M₀ C b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → RunAux M₀ C a → RunAux M₀ C b :=
    fun hS a b hab ha => rtgH (P := fun h => RunAux M₀ C h) hS hab ha
  have p1 := key (fun a b hs hp => hs.aux hp) a1 (RunAux.init C)
  have p2 := key (fun a b hs hp => hs.aux hp) a2 p1
  have p3 := key (fun a b hs hp => hs.aux hp) a3 p2
  have p4 := key (fun a b hs hp => hs.aux hp) a4 p3
  have hN : NoEpsHinge C h₄ := fun v hv hε hvH => hsgl v hv hε (hinge_sgat obl hvH)
  refine ⟨?_, ?_⟩
  · exact (rtgH (P := fun h => RunAux M₀ C h ∧ NoEpsHinge C h)
      (fun a b hs hp => ⟨⟨hs.dp hp.1.1 hp.1.2.1.inj, hs.anc hp.1.2.1, hp.1.2.2.step4 hs hp.1.2.1 hp.2⟩,
        hp.2.step4 hs⟩) a5 ⟨p4, hN⟩).1
  · have k4 := rtgH (P := fun h => (∃ R', InvL M₀ R' L γ η w κ h) ∧ NoEligibleTriangle C L γ η w κ h)
      (fun h h' hs hP => ⟨by obtain ⟨R', hR'⟩ := hP.1; exact ⟨R', hR'.step3 hs.toHStep3⟩,
        hP.2.step3 (by obtain ⟨R', hR'⟩ := hP.1; exact hR'.good.1.noloop) hs.toHStep3⟩) a4 ⟨⟨R₃, i3⟩, n3⟩
    exact (rtgH (P := fun h => (∃ R', InvL M₀ R' L γ η w κ h) ∧ NoEligibleTriangle C L γ η w κ h)
      (fun h h' hs hP => ⟨by obtain ⟨R', hR'⟩ := hP.1; exact ⟨R', hR'.step4 hs⟩,
        hP.2.step4 (by obtain ⟨R', hR'⟩ := hP.1; exact hR'.good.1.noloop) hs⟩) a5 k4).2

end WaveTurbulence.GammaLow.FinalCount.H
