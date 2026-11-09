/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.ChainSum` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.ChainSum


/-!
# CLASSCOUNT: sums over the joint layers of a Fama.Spine.chain of ingredient vines

A vine Fama.Spine.chain (VC) is a concatenation of ingredient vines with joint layers `q_0, …, q_n ∈ [0, 𝔇]`.  An ingredient
is *good* when the improved bound `layervine` applies (`M(x,y) ≤ c K^{x-y}` for `y ≤ x`, and `M(x,y) = 0` for `y > x`)
and *bad* when only its total `Σ_{x,y} M(x,y) ≤ T` is known.  This module bounds the sum over all joint layers of
the product of the ingredient sums.  The accounting is by runs: a run of `k` consecutive good ingredients costs
`2^{k+𝔇}`, not `(𝔇+1)^k` (TARGET L1519, L2243-L2249 gloss over this).  The proof is by induction on the Fama.Spine.chain with the
potential `I_k(v) = Σ_x v(x) K^x ν_k(x)`, `ν_0 = 1`, `ν_{k+1}(x) = Σ_{y ≤ x} ν_k(y)` (`k` = number of good ingredients
still to come before the next bad one).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.GammaLow.FinalCount
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

theorem nu_mono (k : ℕ) {x y : ℕ} (h : x ≤ y) : nu k x ≤ nu k y := by
  cases k with
  | zero => simp [nu]
  | succ k =>
    show ∑ z ∈ range (x + 1), nu k z ≤ ∑ z ∈ range (y + 1), nu k z
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun z _ _ => nu_nonneg k z

variable (𝔇 : ℕ) (K : ℝ)

variable {𝔇 K}

theorem bad_step (hK : 1 ≤ K) {l : Link} (hl : l.Ok 𝔇 K) (hg : l.good = false) (k : ℕ) {v : ℕ → ℝ}
    (hv : ∀ x, 0 ≤ v x) :
    Ipot 𝔇 K k (prop 𝔇 v l.M) ≤ K ^ 𝔇 * nu k 𝔇 * l.T * Ipot 𝔇 K 0 v := by
  obtain ⟨hM0, -, -, hT⟩ := hl
  have hT := hT hg
  have hK0 : 0 < K := by linarith
  have hT0 : 0 ≤ l.T :=
    le_trans (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hM0 x y) hT
  unfold Ipot prop
  simp only [Finset.sum_mul]
  -- each term `v x * M x y * K^y * ν_k y ≤ K^𝔇 ν_k(𝔇) * (v x * M x y)`
  have hterm : ∀ y ∈ range (𝔇 + 1), ∀ x ∈ range (𝔇 + 1),
      v x * l.M x y * K ^ y * nu k y ≤ K ^ 𝔇 * nu k 𝔇 * (v x * l.M x y) := by
    intro y hy x hx
    have hy' : y ≤ 𝔇 := by have := Finset.mem_range.mp hy; omega
    have h1 : K ^ y ≤ K ^ 𝔇 := pow_le_pow_right₀ hK hy'
    have h2 : nu k y ≤ nu k 𝔇 := nu_mono k hy'
    have h0 : 0 ≤ v x * l.M x y := mul_nonneg (hv x) (hM0 x y)
    calc v x * l.M x y * K ^ y * nu k y = (v x * l.M x y) * (K ^ y * nu k y) := by ring
      _ ≤ (v x * l.M x y) * (K ^ 𝔇 * nu k 𝔇) := by
          gcongr
          · exact nu_nonneg k y
      _ = _ := by ring
  have hrow : ∀ x ∈ range (𝔇 + 1), ∑ y ∈ range (𝔇 + 1), l.M x y ≤ l.T := fun x hx =>
    calc ∑ y ∈ range (𝔇 + 1), l.M x y
        ≤ ∑ x' ∈ range (𝔇 + 1), ∑ y ∈ range (𝔇 + 1), l.M x' y :=
          Finset.single_le_sum (f := fun x' => ∑ y ∈ range (𝔇 + 1), l.M x' y)
            (fun x' _ => Finset.sum_nonneg fun y _ => hM0 x' y) hx
      _ ≤ l.T := hT
  calc ∑ y ∈ range (𝔇 + 1), ∑ x ∈ range (𝔇 + 1), v x * l.M x y * K ^ y * nu k y
      ≤ ∑ y ∈ range (𝔇 + 1), ∑ x ∈ range (𝔇 + 1), K ^ 𝔇 * nu k 𝔇 * (v x * l.M x y) :=
        Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x hx => hterm y hy x hx
    _ = K ^ 𝔇 * nu k 𝔇 * ∑ x ∈ range (𝔇 + 1), v x * ∑ y ∈ range (𝔇 + 1), l.M x y := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
    _ ≤ K ^ 𝔇 * nu k 𝔇 * ∑ x ∈ range (𝔇 + 1), v x * l.T := by
        have hc : 0 ≤ K ^ 𝔇 * nu k 𝔇 := mul_nonneg (by positivity) (nu_nonneg k 𝔇)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx => ?_) hc
        exact mul_le_mul_of_nonneg_left (hrow x hx) (hv x)
    _ ≤ K ^ 𝔇 * nu k 𝔇 * l.T * ∑ x ∈ range (𝔇 + 1), v x * K ^ x * nu 0 x := by
        have hc : 0 ≤ K ^ 𝔇 * nu k 𝔇 := mul_nonneg (by positivity) (nu_nonneg k 𝔇)
        calc K ^ 𝔇 * nu k 𝔇 * ∑ x ∈ range (𝔇 + 1), v x * l.T
            = K ^ 𝔇 * nu k 𝔇 * l.T * ∑ x ∈ range (𝔇 + 1), v x := by
              rw [← Finset.sum_mul]; ring
          _ ≤ K ^ 𝔇 * nu k 𝔇 * l.T * ∑ x ∈ range (𝔇 + 1), v x * K ^ x * nu 0 x := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx => ?_) (mul_nonneg hc hT0)
              have : (1 : ℝ) ≤ K ^ x := one_le_pow₀ hK
              simp only [nu]
              nlinarith [hv x]

theorem phi_nonneg (hK : 1 ≤ K) : ∀ L : List Link, (∀ l ∈ L, l.Ok 𝔇 K) → 0 ≤ phi 𝔇 K L
  | [], _ => by simp [phi]
  | l :: L, h => by
    have hl := h l (List.mem_cons_self ..)
    have hL := phi_nonneg hK L fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold phi
    split_ifs with hg
    · exact mul_nonneg (hl.2.1 hg).1 hL
    · have hg' : l.good = false := by simpa using hg
      have hK0 : 0 < K := by linarith
      have h1 : 0 ≤ K ^ 𝔇 * nu (lead L) 𝔇 := mul_nonneg (by positivity) (nu_nonneg _ _)
      exact mul_nonneg (mul_nonneg h1 (link_T_nonneg hl hg')) hL

/-- **The Fama.Spine.chain bound.** -/
theorem chain_bound (hK : 1 ≤ K) : ∀ (L : List Link), (∀ l ∈ L, l.Ok 𝔇 K) → ∀ v : ℕ → ℝ, (∀ x, 0 ≤ v x) →
    ∑ y ∈ range (𝔇 + 1), chainV 𝔇 L v y ≤ phi 𝔇 K L * Ipot 𝔇 K (lead L) v
  | [], _, v, hv => by
    simp only [chainV, phi, lead, one_mul, Ipot, nu]
    refine Finset.sum_le_sum fun x _ => ?_
    have : (1 : ℝ) ≤ K ^ x := one_le_pow₀ hK
    nlinarith [hv x]
  | l :: L, h, v, hv => by
    have hl := h l (List.mem_cons_self ..)
    have hL : ∀ l' ∈ L, l'.Ok 𝔇 K := fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have ih := chain_bound hK L hL (prop 𝔇 v l.M) (prop_nonneg hl hv)
    have hphi := phi_nonneg (𝔇 := 𝔇) hK L hL
    simp only [chainV]
    refine ih.trans ?_
    have e1 : phi 𝔇 K (l :: L) = if l.good = true then l.c * phi 𝔇 K L
        else K ^ 𝔇 * nu (lead L) 𝔇 * l.T * phi 𝔇 K L := rfl
    have e2 : lead (l :: L) = if l.good = true then lead L + 1 else 0 := rfl
    rw [e1, e2]
    by_cases hg : l.good = true
    · rw [if_pos hg, if_pos hg]
      have := good_step hK hl hg (lead L) hv
      calc phi 𝔇 K L * Ipot 𝔇 K (lead L) (prop 𝔇 v l.M) ≤ phi 𝔇 K L * (l.c * Ipot 𝔇 K (lead L + 1) v) :=
            mul_le_mul_of_nonneg_left this hphi
        _ = l.c * phi 𝔇 K L * Ipot 𝔇 K (lead L + 1) v := by ring
    · have hg' : l.good = false := by simpa using hg
      rw [if_neg hg, if_neg hg]
      have := bad_step hK hl hg' (lead L) hv
      calc phi 𝔇 K L * Ipot 𝔇 K (lead L) (prop 𝔇 v l.M)
          ≤ phi 𝔇 K L * (K ^ 𝔇 * nu (lead L) 𝔇 * l.T * Ipot 𝔇 K 0 v) :=
            mul_le_mul_of_nonneg_left this hphi
        _ = K ^ 𝔇 * nu (lead L) 𝔇 * l.T * phi 𝔇 K L * Ipot 𝔇 K 0 v := by ring

theorem Ipot_one_le (hK : 1 ≤ K) (k : ℕ) :
    Ipot 𝔇 K k (fun _ => 1) ≤ (𝔇 + 1 : ℕ) * (K ^ 𝔇 * 2 ^ (𝔇 + k)) := by
  have hK0 : 0 < K := by linarith
  unfold Ipot
  have hterm : ∀ x ∈ range (𝔇 + 1), (1 : ℝ) * K ^ x * nu k x ≤ K ^ 𝔇 * 2 ^ (𝔇 + k) := by
    intro x hx
    have hx' : x ≤ 𝔇 := by have := Finset.mem_range.mp hx; omega
    have h1 : K ^ x ≤ K ^ 𝔇 := pow_le_pow_right₀ hK hx'
    have h2 : nu k x ≤ 2 ^ (𝔇 + k) :=
      (nu_le k x).trans (pow_le_pow_right₀ (by norm_num) (by omega))
    rw [one_mul]
    exact mul_le_mul h1 h2 (nu_nonneg k x) (by positivity)
  have := Finset.sum_le_sum hterm
  simpa using this

/-- **The Fama.Spine.chain bound for the sum over all joint layers.** -/
theorem chain_bound_one (hK : 1 ≤ K) (L : List Link) (h : ∀ l ∈ L, l.Ok 𝔇 K) :
    ∑ y ∈ range (𝔇 + 1), chainV 𝔇 L (fun _ => 1) y ≤
      phi 𝔇 K L * ((𝔇 + 1 : ℕ) * (K ^ 𝔇 * 2 ^ (𝔇 + lead L))) := by
  refine (chain_bound hK L h _ fun _ => zero_le_one).trans ?_
  exact mul_le_mul_of_nonneg_left (Ipot_one_le hK _) (phi_nonneg hK L h)

end WaveTurbulence.GammaLow.Famc.ClassCount
