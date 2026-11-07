/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Small
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # G8-XROUTE (e), (f): the base bound at `X ∖ ℓ*` and `route_bound_X`

* `xMinus_afree` (e): for `X` (or the quadrilateral), `𝔄(M ∖ ℓ) ≤ K (log L)^B L^{-γ₀-η₀/3}` for every bond `ℓ` and
  every LG parameter `η' ≥ η₀`, from `afree_case_pair` (G8's `pairGainAt` for the `(3,3)`/`(3,4)` pair and Prop 10.2's
  second statement for the leftover double bond `c = d`).
* `route_bound_X` (f): copy of `G8R.ThmA.route_bound` with `IsXFinal` at the end of the route.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem YRouteX.isX_of_zero {M : Molecule V D} (h : YRouteX 0 M) : IsXFinal M := by
  cases h with
  | done _ hT => exact hT

theorem YRouteX.inv_succ {M : Molecule V D} {k : ℕ} (h : YRouteX (k + 1) M) :
    ∃ (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C),
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 ∧ YRouteX k (E.toTwoExit hcap).post := by
  cases h with
  | y2 _ _ hcap C E hc h' => exact ⟨hcap, C, E, hc, h'⟩

/-- Larger LG parameter, fewer decorations. -/
theorem afree_mono_eta (M : Molecule V D) {d : ℕ} {L γ δ η η' C1 : ℝ} (hL : 1 ≤ L) (h : η ≤ η') (P : Finset V → ℝ) :
    AFree M d L γ δ η' C1 P ≤ AFree M d L γ δ η C1 P :=
  countAFree_mono_adm M fun κ hκ =>
    ⟨fun x y hxy hdir => (Real.rpow_le_rpow_of_exponent_le hL (by linarith)).trans (hκ.1 x y hxy hdir), hκ.2⟩

theorem ennreal_le_sq_mul' {a b : ℝ≥0∞} (ha : 1 ≤ a) : a * b ≤ a ^ 2 * b :=
  calc a * b ≤ a * (a * b) := mul_le_mul' le_rfl (le_mul_of_one_le_left bot_le ha)
    _ = a ^ 2 * b := by rw [← mul_assoc, ← sq]

theorem ofReal_mul_ofReal_mul' {x y : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x * ENNReal.ofReal (x * y) = ENNReal.ofReal x ^ 2 * ENNReal.ofReal y := by
  rw [ENNReal.ofReal_mul hx, ← mul_assoc, ← sq]

/-- **Steps 3–4: a route of at most two (Y2) sequences to `X` (G8-XROUTE (f)).** -/
theorem route_bound_X {d : ℕ} {L γ δ η η0 C1 Kt : ℝ} (hηnn : 0 ≤ η) (hη0 : η0 ≤ η / 4)
    (hK : 1 ≤ 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6)
    (hs1 : Ylem2SecondAt.{u, v} d L γ δ η C1) (hn1 : Ylem2NotRemovedAt.{u, v} d L γ δ η C1)
    (hs2 : Ylem2SecondAt.{u, v} d L γ δ (η / 2) C1) (hn2 : Ylem2NotRemovedAt.{u, v} d L γ δ (η / 2) C1)
    (hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsXFinal M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      ∀ (e : D) (η' : ℝ), η0 ≤ η' → ∀ (P : Finset V → ℝ),
        (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
        AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤ ENNReal.ofReal Kt)
    (M : Molecule V D) (k : ℕ) (hk : k ≤ 2) (hroute : YRouteX k M)
    (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (h4 : ∀ a ∈ M.atoms, M.deg a = 4) (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (e : D) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal Kt := by
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK
  have hK2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 :=
    one_le_pow₀ hK1
  match k, hk, hroute with
  | 0, _, hroute =>
    exact (hbase M hroute.isX_of_zero hcap hloop h4 hconn e η (by linarith) P hP).trans (le_mul_of_one_le_left bot_le hK2)
  | 1, _, hroute =>
    obtain ⟨hcap', C, E, _, hroute'⟩ := hroute.inv_succ
    obtain ⟨hcapP, hloopP, h4P, hconnP⟩ := E.post_props hcap' hloop h4 hconn
    have hT' := hroute'.isX_of_zero
    refine (route_step hs1 hn1 M hcap' h4 hconn C E (X := Kt) (fun e₁ P' hP' => hbase _ hT' hcapP hloopP h4P hconnP e₁ _ (by linarith) P' hP') e P
      hP).trans ?_
    exact ennreal_le_sq_mul' hK1
  | 2, _, hroute =>
    obtain ⟨hcap', C, E, _, hroute'⟩ := hroute.inv_succ
    obtain ⟨hcapP, hloopP, h4P, hconnP⟩ := E.post_props hcap' hloop h4 hconn
    obtain ⟨hcap'', C', E', _, hroute''⟩ := hroute'.inv_succ
    obtain ⟨hcapQ, hloopQ, h4Q, hconnQ⟩ := E'.post_props hcap'' hloopP h4P hconnP
    have hT'' := hroute''.isX_of_zero
    have hstep2 := fun e₁ P' (hP' : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap').post e₁),
        0 ≤ P' S) => (route_step hs2 hn2 _ hcap'' h4P hconnP C' E' (X := Kt)
          (fun e₂ P'' hP'' => hbase _ hT'' hcapQ hloopQ h4Q hconnQ e₂ _ (by linarith) P'' hP'') e₁ P' hP')
    by_cases hKt : 0 ≤ Kt
    · have hstep2' := fun e₁ P' hP' => (hstep2 e₁ P' hP').trans_eq (ENNReal.ofReal_mul (by positivity)).symm
      exact (route_step hs1 hn1 M hcap' h4 hconn C E hstep2' e P hP).trans_eq
        (ofReal_mul_ofReal_mul' (by positivity))
    · push Not at hKt
      have h0 : ∀ e₁ P' hP', AFree (MoleProp.eraseBond (E.toTwoExit hcap').post e₁) d L γ δ (η / 2) C1 P' ≤
          ENNReal.ofReal 0 := fun e₁ P' hP' => by
        refine (hstep2 e₁ P' hP').trans ?_
        rw [ENNReal.ofReal_of_nonpos hKt.le, mul_zero]; exact bot_le
      refine (route_step hs1 hn1 M hcap' h4 hconn C E h0 e P hP).trans ?_
      rw [ENNReal.ofReal_zero, mul_zero]; exact bot_le


end

end WaveTurbulence.FinalCountG8
