/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompVine
/-! **FINALCOUNT-G3**: `CompBeta` along a whole run: every component of the final molecule contains a `β`-atom or
an atom of odd degree. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem Step1.compBeta {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step1 L γ η w κ s s') (hg : Good R s) (hC : CompBeta s) : CompBeta s' := by
  cases h with
  | vine K R' kp hR hkp hu hl ga gb h3a h3b =>
    by_cases hα : K.post.numComponents ≤ s.M.numComponents
    · have : alphaOrBeta K.post.numComponents s.M.numComponents R' kp = .alpha R' kp := by
        unfold alphaOrBeta; rw [if_pos hα]
      rw [this]; exact vine_compBeta_alpha K hg hC R' kp hu hl hα
    · have : alphaOrBeta K.post.numComponents s.M.numComponents R' kp = .beta := by
        unfold alphaOrBeta; rw [if_neg hα]
      rw [this]
      exact ((hC.cutβ K.cut_a .beta (Or.inl rfl)).cutβ K.cut_b .beta (Or.inl rfl)).delSt _ K.closed

theorem Step2.compBeta {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {s s' : St.{u} V D₀}
    (h : Step2 L γ η w κ s s') (hg : Good R s) (hC : CompBeta s) : CompBeta s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 => exact tri_compBeta T Q kp hg.1 hC hcl h3

theorem SubHyp.compBeta {R : ℕ} {M₀ : Molecule V D₀} (h : SubHyp R M₀) : CompBeta (St.init M₀) := by
  intro a ha _
  have hI := h.inv
  have hne : (M₀.atoms.filter fun a => ¬ Even (M₀.deg a)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (M₀.atoms.filter fun a => ¬ Even (M₀.deg a)).card = 2 * R := h.odd_card
    have := h.one_le
    omega
  obtain ⟨b, hb⟩ := hne
  obtain ⟨hbm, hbo⟩ := Finset.mem_filter.1 hb
  refine ⟨b, hbm, h.conn a ha b hbm, Or.inr ?_⟩
  unfold contrib
  show ((Cls.eps).base : ℤ) - (M₀.deg b : ℤ) ≠ 0
  simp only [Cls.base]
  intro h0
  apply hbo
  have : M₀.deg b = 4 := by omega
  rw [this]; decide

theorem good_comp_rtg {R : ℕ} {step : St.{u} V D₀ → St.{u} V D₀ → Prop}
    (hstep : ∀ s s', step s s' → Good R s → CompBeta s → Good R s' ∧ CompBeta s') {a b : St.{u} V D₀}
    (h : Relation.ReflTransGen step a b) : Good R a → CompBeta a → Good R b ∧ CompBeta b := by
  induction h with
  | refl => exact fun g c => ⟨g, c⟩
  | tail _ hs ih =>
    exact fun g c => by
      obtain ⟨g', c'⟩ := ih g c
      exact hstep _ _ hs g' c'

/-- Along a run, both `Good` and `CompBeta` hold. -/
theorem Run.goodComp {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
    {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀) :
    Good R sf ∧ CompBeta sf := by
  obtain ⟨s₁, s₂, s₃, h1, _, h2, _, h3, _, h4, _⟩ := hr
  have g0 : Good R (St.init M₀) := ⟨hS.inv, St.init_clean M₀⟩
  have r1 := good_comp_rtg (fun _ _ h g c => ⟨h.good g, h.compBeta g c⟩) h1 g0 hS.compBeta
  have r2 := good_comp_rtg (fun _ _ h g c => ⟨h.good g, h.compBeta g c⟩) h2 r1.1 r1.2
  have r3 := good_comp_rtg (fun _ _ h g c => ⟨h.good g, h.compBeta g c⟩) h3 r2.1 r2.2
  exact good_comp_rtg (fun _ _ h g c => ⟨h.good g, h.compBeta c⟩) h4 r3.1 r3.2

end WaveTurbulence.FinalCountG3
