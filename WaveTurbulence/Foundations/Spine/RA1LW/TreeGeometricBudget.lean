/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeafFrequencyBudget
public import WaveTurbulence.Foundations.RegAsymp.OrderLoss
public import WaveTurbulence.Foundations.Spine.RA1LW.LeadingGeometricBudget

/-! # Uniform geometric absorption of the actual tree spatial coefficients -/

public section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links

/-- The actual tree row loss is geometric in its original link count. -/
theorem treeSpectralFrequencyLoss_le_geometric (X : RegChain) (ζ : ℤˣ) :
    treeSpectralFrequencyLoss X ζ ≤ (9:ℝ)^(X.treeLinks ζ).length := by
  have hs := chain_linksAt_length X ζ ((0:Fin 1),[])
  change (X.treeLinks ζ).length*2=X.size at hs
  have hsr : (X.size:ℝ)=2*((X.treeLinks ζ).length:ℝ) := by exact_mod_cast hs.symm.trans (Nat.mul_comm _ _)
  unfold treeSpectralFrequencyLoss
  rw [hsr]
  have hh := leaf_polynomial_le_geometric (X.treeLinks ζ).length 2
  norm_num only [show (3:ℝ)^2=9 by norm_num] at hh
  calc
    _ ≤ (2*((X.treeLinks ζ).length:ℝ)+1)^2 := by nlinarith
    _ ≤ _ := hh

/-- Fixed derivative and localization constants absorb geometrically, with constants
chosen before every tree and every logarithmic order exponent. -/
theorem tree_spatial_budget_le_geometric {a b c p e q r s x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (he : 0 ≤ e) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (n : ℕ) (hx : x ≤ (9:ℝ)^n) :
    a*(b*(c^n*p^(2*n+1)))*(e*(q^n*r^n*s^(2*n))*x) ≤
      (a*b*p*e)*(c*p^2*q*r*s^2*9)^n := by
  calc
    _ ≤ a*(b*(c^n*p^(2*n+1)))*(e*(q^n*r^n*s^(2*n))*(9:ℝ)^n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by positivity)) (by positivity)
    _ = _ := by simp only [mul_pow,pow_add,pow_one,pow_mul]; ring

/-- The corresponding extended-real expression is the literal finite real budget. -/
theorem tree_ofReal_spatial_budget {a b c p e q r s x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (he : 0 ≤ e) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (_hx : 0 ≤ x) (n : ℕ) :
    (ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (c^n)*ENNReal.ofReal p^(2*n+1))))*
      ENNReal.ofReal (e*(q^n*r^n*s^(2*n))*x) =
      ENNReal.ofReal (a*(b*(c^n*p^(2*n+1)))*(e*(q^n*r^n*s^(2*n))*x)) := by
  simp (disch := positivity) only [ENNReal.ofReal_mul,ENNReal.ofReal_pow]

end WaveTurbulence.RA1Leafwise
