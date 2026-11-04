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

/-- Rebasing pair times preserves their actual regularized-limit invariant. -/
theorem tree_shiftedKernelFamily {R : ℕ → ℝ → ℝ → ℝ → ℂ} {R₀ : ℕ → ℝ → ℝ → ℂ}
    (hR : KFam R R₀) (s : ℝ) :
    KFam (fun j ε u v => R j ε (clamp01 (u+s)) (clamp01 (v+s)))
      (fun j u v => R₀ j (clamp01 (u+s)) (clamp01 (v+s))) := by
  obtain ⟨M,hM⟩ := hR.bound
  obtain ⟨L,hL⟩ := hR.lip
  refine ⟨⟨M,?_⟩,⟨max L 0,?_⟩,?_⟩
  · filter_upwards [hM] with ε hε
    exact fun j u v => hε j _ _
  · filter_upwards [hL] with ε hε
    intro j u v u' v'
    have hu : |clamp01 (u+s)-clamp01 (u'+s)| ≤ |u-u'| := by
      simpa only [add_sub_add_right_eq_sub] using abs_clamp01_sub_le (u+s) (u'+s)
    have hv : |clamp01 (v+s)-clamp01 (v'+s)| ≤ |v-v'| := by
      simpa only [add_sub_add_right_eq_sub] using abs_clamp01_sub_le (v+s) (v'+s)
    calc
      _ ≤ L*(|clamp01 (u+s)-clamp01 (u'+s)|+|clamp01 (v+s)-clamp01 (v'+s)|) := hε j _ _ _ _
      _ ≤ max L 0*(|clamp01 (u+s)-clamp01 (u'+s)|+|clamp01 (v+s)-clamp01 (v'+s)|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ max L 0*(|u-u'|+|v-v'|) :=
        mul_le_mul_of_nonneg_left (add_le_add hu hv) (le_max_right _ _)
  · intro j u _ v _
    exact hR.lim j _ (clamp01_mem _) _ (clamp01_mem _)

/-- The exact shifted chain has the landed adjacent-pair limit for every forward source
endpoint. This includes empty chains and non-adjacent pair codes. -/
theorem tree_rebased_chain_limit {R : ℕ → ℝ → ℝ → ℝ → ℂ} {R₀ : ℕ → ℝ → ℝ → ℂ}
    (hR : KFam R R₀) (bb : ℕ → Bool) (c : LegalCode) (q : ℕ) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    Tendsto (fun ε => chainK
      (kP bb (fun j ε u v => R j ε (clamp01 (u+s)) (clamp01 (v+s))) ε)
      c q (t-s) (fun _ => 1)) (𝓝[>] (0:ℝ))
      (𝓝 (chainL (kD bb (fun j u v => R₀ j (clamp01 (u+s)) (clamp01 (v+s)))) c q (t-s) (fun _ => 1))) := by
  exact tendsto_chainK (tree_shiftedKernelFamily hR s) c q
    (Eventually.of_forall (fun _ => continuous_const))
    (G := 1) (Eventually.of_forall (fun _ _ _ => by simp)) (t-s)
    ⟨sub_nonneg.mpr hst.le,by linarith⟩
    (fun _ _ => tendsto_const_nhds) (fun _ => tendsto_const_nhds)

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
