/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM04
/-! **FINALCOUNT-G3: `FinalDec` for a component** (second part: the fields about labels, `ε`-atoms, `α`/`β` gaps). -/
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

/-- Two distinct darts at a `α`/`β`-atom have opposite directions. -/
theorem orient_neL (hC : Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm) {a : V} (ha : a ∈ hf.s.M.atoms)
    (hne : hf.s.cls a ≠ .eps) {x y : hf.s.D} (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) (hxy : x ≠ y) :
    hf.s.M.out x ≠ hf.s.M.out y := by
  have hle := hC.struct.ab_deg a ha hne
  have hxm : x ∈ hf.s.M.dartsAt a := (mem_dartsAt _ _ _).2 hx
  have hym : y ∈ hf.s.M.dartsAt a := (mem_dartsAt _ _ _).2 hy
  have h2 : 2 ≤ hf.s.M.deg a := by
    have := Finset.one_lt_card.2 ⟨x, hxm, y, hym, hxy⟩
    exact this
  obtain ⟨ho, hi⟩ := hC.bal.2 a ha hne (by omega)
  intro he
  cases hox : hf.s.M.out x
  · have hy' : hf.s.M.out y = false := by rw [← he, hox]
    have : 2 ≤ hf.s.M.indeg a := by
      unfold Molecule.indeg
      exact Finset.one_lt_card.2 ⟨x, Finset.mem_filter.2 ⟨hxm, hox⟩, y, Finset.mem_filter.2 ⟨hym, hy'⟩, hxy⟩
    omega
  · have hy' : hf.s.M.out y = true := by rw [← he, hox]
    have : 2 ≤ hf.s.M.outdeg a := by
      unfold Molecule.outdeg
      exact Finset.one_lt_card.2 ⟨x, Finset.mem_filter.2 ⟨hxm, hox⟩, y, Finset.mem_filter.2 ⟨hym, hy'⟩, hxy⟩
    omega

theorem ne_mate_of_atomL (hC : Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm) {a : V} {x y : hf.s.D}
    (hx : hf.s.M.atom x = a) (hy : hf.s.M.atom y = a) : y ≠ hf.s.M.mate x := by
  intro e
  exact hC.noloop x (by rw [← e, hx, hy])

theorem gapAt_swapL (L : ℝ) (w : Mom d) {D : Type*} (κ : D → (Fin d → ℤ)) (x y : D) :
    ‖Molecule.gapAt L w κ y x‖ = ‖Molecule.gapAt L w κ x y‖ := by
  unfold Molecule.gapAt; exact norm_sub_rev _ _

section dec
variable (hC : Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm) {a₀ : V}
include hC

theorem dec_labRangeL {a : V} (ha : a ∈ hf.s.M.atoms) (hα : (toCls (hf.s.cls a)).IsAlpha) :
    L⁻¹ ≤ (toCls (hf.s.cls a)).lab ∧ (toCls (hf.s.cls a)).lab ≤ L ^ (-γ + η) := by
  obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
  obtain ⟨hl, -⟩ := hC.label a ha ρ kp e
  rw [e]
  exact ⟨hl.2.1, hl.2.2⟩

theorem dec_kapValsL {a : V} (ha : a ∈ hf.s.M.atoms) (hα : (toCls (hf.s.cls a)).IsAlpha) :
    (toCls (hf.s.cls a)).kap = 0 ∨ (toCls (hf.s.cls a)).kap = 50 := by
  obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
  obtain ⟨-, hk, -⟩ := hC.label a ha ρ kp e
  rw [e]
  exact hk

theorem dec_epsLGL {a : V} (ha : a ∈ hf.s.M.atoms) (hε : hf.s.cls a = .eps) (hT : TameFree hf Tm a) (x y : PDart hf.s.M (compP hf.s.M a₀))
    (hx : (compMol hf.s.M a₀).atom x = a) (hy : (compMol hf.s.M a₀).atom y = a)
    (hxy : (compMol hf.s.M a₀).out x ≠ (compMol hf.s.M a₀).out y) :
    L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) (compDecL hf a₀ κ) x - Molecule.kvec L (0 : Mom d) (compDecL hf a₀ κ) y‖ := by
  have hx' : hf.s.M.atom x.1 = a := hx
  have hy' : hf.s.M.atom y.1 = a := hy
  have hlg : ∀ x' y' : hf.s.D, hf.s.M.atom x' = a → hf.s.M.atom y' = a → hf.s.M.out x' = false →
      hf.s.M.out y' = true → L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) (κ ∘ hf.s.down) x' -
        Molecule.kvec L (0 : Mom d) (κ ∘ hf.s.down) y'‖ := by
    intro x' y' h1 h2 o1 o2
    exact lt_norm_of_LGL (hC.eps_LG a ha hε hT x' y' h1 h2 o1 o2 (ne_mate_of_atomL hC h1 h2))
  have hxy' : hf.s.M.out x.1 ≠ hf.s.M.out y.1 := hxy
  cases hox : hf.s.M.out x.1
  · have hoy : hf.s.M.out y.1 = true := by
      cases hoy : hf.s.M.out y.1
      · exact absurd (hox.trans hoy.symm) hxy'
      · rfl
    exact hlg x.1 y.1 hx' hy' hox hoy
  · have hoy : hf.s.M.out y.1 = false := by
      cases hoy : hf.s.M.out y.1
      · rfl
      · exact absurd (hox.trans hoy.symm) hxy'
    have := hlg y.1 x.1 hy' hx' hoy hox
    rw [kvec_compL, kvec_compL, norm_sub_rev]
    exact this

end dec

end WaveTurbulence.FinalCountG3
