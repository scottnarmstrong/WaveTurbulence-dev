/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Cancel.RegType2
public import WaveTurbulence.Foundations.ClassJR.MCTShift

/-! # The regularized chain limit after rebasing at the lone-leaf time

The pair kernels retain their original physical times, shifted by s. Clamping
outside the used time square preserves the landed kernel-family invariant.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set Filter Cancel ClassJR
open scoped Topology

/-- The landed two-chain regularization theorem also gives the single chain with
constant continuation. No second root clock is introduced in this result. -/
theorem tree_chain_const_regularized {V : Type} [DecidableEq V]
    {ζ : V → ℤ} (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) (Z : Finset V)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = ζ (σ j))
    {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} {SF : ℕ → Finset V}
    (hF : ∀ j, NiceCoef (SF j) (F j)) {BF : ℝ}
    (hBF : ∀ j α, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ‖F j α t s‖ ≤ BF)
    {L : ℕ → ℝ → ℝ → ℂ} (c : LegalCode)
    (hR : ∀ j < c.size, RegLim2 (fun η t s => RI η ζ Z (SF j) (F j) t s) (L j))
    (hd : ChainDisjF σ SF c 0) :
    RegCoef ζ Z (chainVarsF σ SF c 0)
      (fun α t _ => chainT σ ε c 0 F α t (fun _ => 1))
      (fun t _ => chainL (kD (fun j => decide (σ j ∈ Z)) (fun j τ _ => L j τ τ)) c 0 t (fun _ => 1)) := by
  have hOne := regCoef_one ζ Z
  have h := regCoef_type2 (Jm := fun _ _ _ => 1) hζ hε hε hF (fun _ => hOne.nice)
    (BF := max BF 1) (by positivity)
    (fun j α t ht s hs => (hBF j α t ht s hs).trans (le_max_left _ _))
    (fun _ _ _ _ _ _ => by simpa only [norm_one] using le_max_right BF 1)
    c LegalCode.nil hR (fun j hj => by simp [LegalCode.size] at hj)
    hOne hd (by trivial) (by simp [chainVarsF]) (by simp [chainVarsF])
  have hnil (D : ℕ → ℝ → ℂ) (q : ℕ) (u : ℝ) (g : ℝ → ℂ) :
      chainL D LegalCode.nil q u g = g u := rfl
  simpa only [chainVarsF, Finset.empty_union, Finset.union_empty, chainT_nil, hnil] using h

end WaveTurbulence.RegAsymp
