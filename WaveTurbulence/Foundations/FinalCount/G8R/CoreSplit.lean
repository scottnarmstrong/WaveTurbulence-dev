/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseIV
public import WaveTurbulence.Foundations.FinalCount.G8R.MergeSmall
import Mathlib.Tactic

/-! # The core of Prop 10.4(2)′: the case analysis

For a core molecule `𝕄` (`IsCore`: in/out caps, no loops, 4-regular, connected, no triple bond, not `T`) and any bond
`ℓ`, the decoration split holds with `ε₁ = (|𝕄| + 1) L^{−η/4}` and `ε₂ = (|𝕄| + 1) L^{−γ₀−η/4}` (DH23 L1963–L1977).
The cases are taken in the order
* 0: only single bonds (Prop 10.3); A: a cut vertex (β-cut); B: a bridge of `𝕄 ∖ ℓ`; II: a bi-bridge;
* I: a double bond at an end of `ℓ`; III/IV: a double bond away from `ℓ` (small gap, or merge and induct).
The induction is on the number of atoms (the merge removes one). The factor `|𝕄| + 1` comes from the size factors of
the β-cut and bi-bridge inputs and from adding the two parts of case III/IV along the induction.
-/

@[expose] public section
set_option autoImplicit false
open Finset Filter
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- A constant times a power of `log L` is eventually below `L ^ θ`. -/
theorem exists_mul_log_rpow_le (c B : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, ∀ L ≥ R, c * Real.log L ^ B ≤ L ^ θ := by
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp ((isLittleO_log_rpow_rpow_atTop B hθ).bound
    (by positivity : (0 : ℝ) < 1 / (|c| + 1)))
  refine ⟨max R1 1, fun L hL => ?_⟩
  have hL1 : R1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have h := hR1 L hL1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLp.le _)] at h
  have h0 : 0 ≤ L ^ θ := Real.rpow_nonneg hLp.le _
  have hc1 : |c| / (|c| + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  calc c * Real.log L ^ B ≤ |c| * |Real.log L ^ B| := (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ |c| * (1 / (|c| + 1) * L ^ θ) := by gcongr
    _ = |c| / (|c| + 1) * L ^ θ := by ring
    _ ≤ 1 * L ^ θ := by gcongr
    _ = L ^ θ := one_mul _

/-- Two statements of the form "for large `C1`, every `δ`, and large `L`" combine. -/
theorem uniform_and {P Q : ℝ → ℝ → ℝ → Prop}
    (hP : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, P C1 δ L)
    (hQ : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, Q C1 δ L) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, P C1 δ L ∧ Q C1 δ L := by
  obtain ⟨C₁, h₁, hP⟩ := hP
  obtain ⟨C₂, h₂, hQ⟩ := hQ
  refine ⟨max C₁ C₂, h₁.trans (le_max_left _ _), fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hP C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨R₂, hR₂⟩ := hQ C1 ((le_max_right _ _).trans hC1) δ hδ
  exact ⟨max R₁ R₂, fun L hL => ⟨hR₁ L ((le_max_left _ _).trans hL), hR₂ L ((le_max_right _ _).trans hL)⟩⟩

/-- `uniform_and` with the size parameter `m` quantified after the constant (the constant is `m`-independent). -/
theorem uniform_and_m {P Q : ℕ → ℝ → ℝ → ℝ → Prop}
    (hP : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, P m C1 δ L)
    (hQ : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, Q m C1 δ L) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      P m C1 δ L ∧ Q m C1 δ L := by
  obtain ⟨C₁, h₁, hP⟩ := hP
  obtain ⟨C₂, h₂, hQ⟩ := hQ
  refine ⟨max C₁ C₂, h₁.trans (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hP m C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨R₂, hR₂⟩ := hQ m C1 ((le_max_right _ _).trans hC1) δ hδ
  exact ⟨max R₁ R₂, fun L hL => ⟨hR₁ L ((le_max_left _ _).trans hL), hR₂ L ((le_max_right _ _).trans hL)⟩⟩

/-- An `m`-free uniform statement is an `m`-uniform one. -/
theorem uniform_lift {P : ℝ → ℝ → ℝ → Prop}
    (hP : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R, P C1 δ L) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      (fun _ : ℕ => P) m C1 δ L := by
  obtain ⟨C₁, h₁, hP⟩ := hP
  exact ⟨C₁, h₁, fun _ => hP⟩

/-- **An input with its constants absorbed**: at each large `L` some constants work and `K (log L)^B ≤ L^θ`. -/
theorem input_good {X : ℝ → ℝ → ℝ → ℝ → ℝ → Prop} {θ : ℝ} (hθ : 0 < θ)
    (h : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R, X C1 δ L K B) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∃ K B : ℝ, X C1 δ L K B ∧ K * Real.log L ^ B ≤ L ^ θ := by
  obtain ⟨Cs, hCs, h⟩ := h
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨K, B, R, hR⟩ := h C1 hC1 δ hδ
  obtain ⟨R', hR'⟩ := exists_mul_log_rpow_le K B hθ
  exact ⟨max R R', fun L hL => ⟨K, B, hR L ((le_max_left _ _).trans hL), hR' L ((le_max_right _ _).trans hL)⟩⟩

/-- The same with a nonnegative constant, for inputs monotone in it. -/
theorem input_good_nonneg {X : ℝ → ℝ → ℝ → ℝ → ℝ → Prop} {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ C1 δ L K B, 1 ≤ L → X C1 δ L K B → X C1 δ L (max K 0) B)
    (h : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R, X C1 δ L K B) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∃ K B : ℝ, 0 ≤ K ∧ X C1 δ L K B ∧ K * Real.log L ^ B ≤ L ^ θ := by
  obtain ⟨Cs, hCs, h⟩ := h
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨K, B, R, hR⟩ := h C1 hC1 δ hδ
  obtain ⟨R', hR'⟩ := exists_mul_log_rpow_le (max K 0) B hθ
  refine ⟨max (max R R') 1, fun L hL => ⟨max K 0, B, le_max_right _ _, hmono C1 δ L K B ((le_max_right _ _).trans hL)
    (hR L ((le_max_left _ _).trans ((le_max_left _ _).trans hL))),
    hR' L ((le_max_right _ _).trans ((le_max_left _ _).trans hL))⟩⟩

/-- `ofReal (K x) ≤ ofReal (max K 0 · x)` for `x ≥ 0`. -/
theorem ofReal_mul_le_max {K x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (K * x) ≤ ENNReal.ofReal (max K 0 * x) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)

theorem smallGapPairAt_mono {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 1 ≤ L)
    (h : SmallGapPairAt.{u, v} d L γ δ η C1 K B) : SmallGapPairAt.{u, v} d L γ δ η C1 (max K 0) B := by
  intro V D _ _ _ M hcap hloop v₁ hv₁ v₂ hv₂ hne hbb h1 h2 hconn hconnR P hP Adm hAdm
  refine (h M hcap hloop v₁ hv₁ v₂ hv₂ hne hbb h1 h2 hconn hconnR P hP Adm hAdm).trans (mul_le_mul' ?_ le_rfl)
  rw [mul_assoc, mul_assoc]
  exact ofReal_mul_le_max (mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hL) _)
    (Real.rpow_nonneg (zero_le_one.trans hL) _))

theorem mergeAt_mono {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 1 ≤ L)
    (h : MergeAt.{u, v} d L γ δ η C1 K B) : MergeAt.{u, v} d L γ δ η C1 (max K 0) B := by
  intro V D _ _ _ M hcap hloop v₁ v₂ hv₁ hv₂ hne hbb h1 h2 hconn hgood P hP Adm hAdm
  refine (h M hcap hloop v₁ v₂ hv₁ hv₂ hne hbb h1 h2 hconn hgood P hP Adm hAdm).trans (mul_le_mul' ?_ le_rfl)
  rw [mul_assoc, mul_assoc]
  exact ofReal_mul_le_max (mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hL) _)
    (Real.rpow_nonneg (zero_le_one.trans hL) _))

/-- **Absorbing a constant**: `c ≤ L^θ` and `θ + a ≤ b` give `c · (m L^a) ≤ m L^b`. -/
theorem absorb {L θ c m a b : ℝ} (hL : 1 ≤ L) (hc : c ≤ L ^ θ) (hm : 0 ≤ m) (hab : θ + a ≤ b) :
    c * (m * L ^ a) ≤ m * L ^ b := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  calc c * (m * L ^ a) ≤ L ^ θ * (m * L ^ a) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = m * L ^ (θ + a) := by rw [Real.rpow_add hLp]; ring
    _ ≤ m * L ^ b := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hab) hm

end WaveTurbulence.MoleProp4
