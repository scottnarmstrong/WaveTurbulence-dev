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

end WaveTurbulence.FinalCountG3
