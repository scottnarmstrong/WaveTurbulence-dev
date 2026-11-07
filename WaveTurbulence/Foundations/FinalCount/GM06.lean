/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM05
/-! **FINALCOUNT-G3: `FinalDec` for a component** (third part: `α` gaps, `β` gaps and the `ι/κ` property N2). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

section dec3
variable (hC : Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm)
include hC

/-- The gap at two distinct darts of a non-`ε` atom is, up to sign, the gap of the recorded cut of the atom. -/
theorem gap_pm_atomgapL {a : V} (ha : a ∈ hf.s.M.atoms) (hne : hf.s.cls a ≠ .eps) {x y : hf.s.D}
    (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) (hxy : x ≠ y) :
    ∃ g, AtomGap L (0 : Mom d) κ hf a g ∧
      (Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y = -g) := by
  have ho := orient_neL hC ha hne hx hy hxy
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases hoy : hf.s.M.out y
      · exact absurd (hox.trans hoy.symm) ho
      · rfl
    exact hC.dartGap a ha hne x y hx hy hox hoy
  · have hoy : hf.s.M.out y = false := by
      cases hoy : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans hoy.symm) ho
    obtain ⟨g, hg, h⟩ := hC.dartGap a ha hne y x hy hx hoy hox
    refine ⟨g, hg, ?_⟩
    have : Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y = -Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) y x := by
      unfold Molecule.gapAt; abel
    rw [this]
    rcases h with h | h
    · right; rw [h]
    · left; rw [h, neg_neg]

theorem atomGap_uniqueL {a : V} {g g' : Mom d} (h : AtomGap L (0 : Mom d) κ hf a g)
    (h' : AtomGap L (0 : Mom d) κ hf a g') : g = g' := by
  obtain ⟨p, vis, e, rfl⟩ := h
  obtain ⟨p', vis', e', rfl⟩ := h'
  rw [e] at e'
  simp only [Option.some.injEq, Prod.mk.injEq] at e'
  rw [e'.1]

theorem dec_alphaGapL {a : V} (ha : a ∈ hf.s.M.atoms) (hα : (toCls (hf.s.cls a)).IsAlpha) {x y : hf.s.D}
    (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) (hxy : x ≠ y) :
    (toCls (hf.s.cls a)).lab / 2 ≤ ‖Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y‖ ∧
      ‖Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y‖ ≤ 2 * (toCls (hf.s.cls a)).lab := by
  obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
  obtain ⟨-, -, hl⟩ := hC.label a ha ρ kp e
  have ho := orient_neL hC ha (by rw [e]; simp) hx hy hxy
  rw [e]
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases hoy : hf.s.M.out y
      · exact absurd (hox.trans hoy.symm) ho
      · rfl
    exact hl x y hx hy hox hoy (ne_mate_of_atomL hC hx hy)
  · have hoy : hf.s.M.out y = false := by
      cases hoy : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans hoy.symm) ho
    have := hl y x hy hx hoy hox (ne_mate_of_atomL hC hy hx)
    unfold GapSim at this
    rw [gapAt_swapL] at this
    exact this

theorem dec_alphaSGL {a : V} (ha : a ∈ hf.s.M.atoms) (hα : (toCls (hf.s.cls a)).IsAlpha) {x y : hf.s.D}
    (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) (hxy : x ≠ y) :
    ‖Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y‖ ≤ L ^ (-γ + η) := by
  obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
  have ho := orient_neL hC ha (by rw [e]; simp) hx hy hxy
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases hoy : hf.s.M.out y
      · exact absurd (hox.trans hoy.symm) ho
      · rfl
    exact le_norm_of_SGL (hC.alpha_sg a ha ρ kp e x y hx hy hox hoy)
  · have hoy : hf.s.M.out y = false := by
      cases hoy : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans hoy.symm) ho
    have := le_norm_of_SGL (hC.alpha_sg a ha ρ kp e y x hy hx hoy hox)
    rwa [gapAt_swapL] at this

theorem cls_beta_of_toClsL {a : V} (ha : a ∈ hf.s.M.atoms) (hβ : (toCls (hf.s.cls a)).IsBeta) :
    hf.s.cls a = .beta := by
  rcases toCls_isBeta.1 hβ with h | h
  · exact h
  · have h1 := hC.struct.ab_deg a ha (by rw [h]; simp)
    have h2 := (hC.struct.deg_range a ha).1
    rcases hC.struct.ab_cls a ha (by rw [h]; simp) with ⟨ρ, kp, e⟩ | e
    · rw [h] at e; simp at e
    · exact e

theorem dec_betaGapL {a : V} (ha : a ∈ hf.s.M.atoms) (hβ : (toCls (hf.s.cls a)).IsBeta) {x y : hf.s.D}
    (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) (hxy : x ≠ y) :
    Molecule.gapAt L (0 : Mom d) (κ ∘ hf.s.down) x y ≠ 0 := by
  have hb := cls_beta_of_toClsL hC ha hβ
  obtain ⟨g, hg, h⟩ := gap_pm_atomgapL hC ha (by rw [hb]; simp) hx hy hxy
  obtain ⟨g', hg', hne⟩ := hC.N1 a ha hb
  have := atomGap_uniqueL hC hg hg'
  subst this
  rcases h with h | h <;> rw [h] <;> simpa using hne

end dec3

end WaveTurbulence.FinalCountG3
