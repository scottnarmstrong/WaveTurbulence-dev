/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3UStep
public import WaveTurbulence.Foundations.FinalCount.G3AdmRel
/-! **FINALCOUNT-G3: excessprop1 (1) for the cuts of Steps 3 and 4** (DH23 Prop 9.4 = TARGET `excessprop1` (1), L1785;
cut cases L1789--L1792, L1801), glued to FINALCOUNT-G2 `alphaCut_excess` / `betaCut_excess`.

`StepDev` is the displayed inequality "`𝔇 ≤ C · excessRHS`" for a step `h → h'` and the inherited decorations
`AdmS Adm0`.  For a cut at `ε`-atom `v`: an `α`-cut creates two `α`-atoms labelled `(R, κ)` (`ΔF = ΔV_β = 0`), a `β`-cut
creates two `β`-atoms (`ΔF = 1`, `ΔV_β = 2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop}

/-- The displayed inequality of `excessprop1` for the step `h → h'` (deviation of the counts of the inherited
decoration classes against `C · excessRHS`). -/
def StepDev (L γ η δ C₁ : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (C : ℝ) (αs : List (ℝ × ℕ)) (ΔF ΔVb : ℤ) (h h' : HSt V D₀) : Prop :=
  IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
    (ENNReal.ofReal (C * excessRHS L γ η αs ΔF ΔVb))

theorem triReal_eta_le_gamma {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) : η ≤ γ := by
  have := H.hη; have := H.hη1; linarith

theorem triReal_eta_le_one_sub {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) : η ≤ (1 - γ) / 200 := by
  have := H.hη2; linarith

theorem triReal_eta_lt_one {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) : η < 1 := by
  have := H.hη; have := H.hη1; have := H.hγ1; linarith

/-- The `ι` fixed ball for the cut `(x₁, x₂)` at the state `h`. -/
theorem ball_of_cut {δ R : ℝ} {kp : ℕ} {h : HSt V D₀} (hAR : AtomRelU Adm0 L w h) {x₁ x₂ : h.s.D}
    (hι : kp = 50 → IotaUnif Adm0 L η w h (h.s.pr x₁ x₂) R) :
    kp = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : h.s.D → Mom d), ParamOK h.s.M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet h.s.M L γ δ w (AdmS Adm0 h.s) c β k0,
        ‖Molecule.gapAt L w κ' x₁ x₂ - r₀‖ ≤ L ^ (-50 * η) * R :=
  fun h50 c β k0 hp => (hι h50).ball (γ := γ) (δ := δ) hAR c β k0 hp

/-- **Step 3, `α`-cut and `β`-cut** (in the literal shape of FINALCOUNT-G2). -/
theorem cut_excess {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) {Rn : ℕ} {h : HSt V D₀} (hI : Inv Rn h.s)
    (hAR : AtomRelU Adm0 L w h) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hc : h.s.M.IsCutData v v₂ x₁ x₂)
    (hPinh : ∀ S' ∈ (h.s.M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
    (hsim : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) x₁ x₂ R)
    (hι : kp = 50 → IotaUnif Adm0 L η w h (h.s.pr x₁ x₂) R) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) :
    (h.s.M.IsAlphaCut v v₂ x₁ x₂ →
      IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
        ((h.s.M.cut v v₂ x₁ x₂).countA L γ δ C₁ w (AdmS Adm0 h.s) P)
        (ENNReal.ofReal ((26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
          excessRHS L γ η [(R, kp), (R, kp)] 0 0))) ∧
    (¬ h.s.M.IsAlphaCut v v₂ x₁ x₂ →
      IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
        ((h.s.M.cut v v₂ x₁ x₂).countA L γ δ C₁ w (AdmS Adm0 h.s) P)
        (ENNReal.ofReal ((10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4)) * excessRHS L γ η [] 1 2))) := by
  have hM : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => deg_le_four _ (hI.bounds a ha)
  have hdeg : h.s.M.deg v ≤ 4 := hM v hc.1
  obtain ⟨-, hRl, hRu⟩ := hR
  refine ⟨fun hα => ?_, fun hβ => ?_⟩
  · exact alphaCut_excess h.s.M H.hd hc hdeg hM hα L γ η δ C₁ H.hγ0 H.hγ1 H.hη (triReal_eta_le_gamma H) (triReal_eta_le_one_sub H) w
      (AdmS Adm0 h.s) P H.hL H.hδ0 H.hδ1 H.hC hP0 hPinh R hRl hRu kp hkp
      (fun κ' hκ' => by obtain ⟨k0, hk0, rfl⟩ := hκ'; exact (hsim k0 hk0).2)
      (ball_of_cut hAR hι)
  · exact betaCut_excess h.s.M hc hdeg hM hβ L γ η δ C₁ H.hη (triReal_eta_lt_one H) c hn w (AdmS Adm0 h.s) P H.hL H.hδ0
      (by linarith [H.hC]) hP0 hPinh


theorem cα_nonneg {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) :
    0 ≤ (26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4) : ℝ) := by
  have h1 : 0 < 1 - γ := by linarith [H.hγ1]
  have := H.hη
  positivity

theorem cβ_nonneg {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (c : ℕ) :
    0 ≤ (10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4) : ℝ) := by
  have h1 : 0 < η ^ 2 - η ^ 3 := by
    have := H.hη; have := triReal_eta_lt_one H
    nlinarith [mul_pos H.hη H.hη, mul_pos (mul_pos H.hη H.hη) (sub_pos.2 (triReal_eta_lt_one H))]
  positivity

/-- **excessprop1 (1) for Step 3.** -/
theorem UStep3.excess {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) {Rn : ℕ} {h h' : HSt V D₀}
    (hs : UStep3 L γ η w Adm0 h h') (hI : Inv Rn h.s) (hAR : AtomRelU Adm0 L w h) (P : Finset V → ℝ)
    (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ h'.s.M.maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) :
    ∃ (R : ℝ) (kp : ℕ), IsLabel L γ η R ∧ (kp = 0 ∨ kp = 50) ∧
      ((h'.s.M.numComponents = h.s.M.numComponents ∧ ∃ C : ℝ, 0 ≤ C ∧
          StepDev L γ η δ C₁ w Adm0 P C [(R, kp), (R, kp)] 0 0 h h') ∨
       (h'.s.M.numComponents = h.s.M.numComponents + 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
          StepDev L γ η δ C₁ w Adm0 P C [] 1 2 h h')) := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι hι' h3 =>
    have key := cut_excess H hI hAR P hP0 hc hPinh R kp hR hkp hsim hι c hn
    refine ⟨R, kp, hR, hkp, ?_⟩
    by_cases hα : h.s.M.IsAlphaCut v v₂ x₁ x₂
    · exact Or.inl ⟨numComponents_cut_of_same h.s.M hc ((isAlphaCut_iff h.s.M hc).1 hα), _, cα_nonneg H, key.1 hα⟩
    · exact Or.inr ⟨numComponents_cut_of_not_same h.s.M hc (fun hs => hα ((isAlphaCut_iff h.s.M hc).2 hs)), _,
        cβ_nonneg H c, key.2 hα⟩

/-- **excessprop1 (1) for Step 4** (a `β`-cut). -/
theorem UStep4.excess {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) {Rn : ℕ} {h h' : HSt V D₀}
    (hs : UStep4 L w Adm0 h h') (hI : Inv Rn h.s) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ h'.s.M.maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) :
    h'.s.M.numComponents = h.s.M.numComponents + 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      StepDev L γ η δ C₁ w Adm0 P C [] 1 2 h h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    have hM : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => deg_le_four _ (hI.bounds a ha)
    exact ⟨numComponents_cut_of_not_same h.s.M hc (fun hs => hβ ((isAlphaCut_iff h.s.M hc).2 hs)), _, cβ_nonneg H c,
      betaCut_excess h.s.M hc (hM v hc.1) hM hβ L γ η δ C₁ H.hη (triReal_eta_lt_one H) c hn w (AdmS Adm0 h.s) P
        H.hL H.hδ0 (by linarith [H.hC]) hP0 hPinh⟩

end WaveTurbulence.FinalCountG3
