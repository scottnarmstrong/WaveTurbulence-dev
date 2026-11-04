/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeRebasedChain

/-! # Shifted pair coefficients retain the original Gaussian regularized limits -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set Filter Cancel ClassJR
open scoped Topology

/-- Source pair coefficients evaluated at the rebased physical times. -/
theorem tree_shiftedNiceCoef {V : Type} {S : Finset V}
    {F : (V → ℝ) → ℝ → ℝ → ℂ} (hF : NiceCoef S F) (s : ℝ) :
    NiceCoef S (fun α u v => F α (clamp01 (u+s)) (clamp01 (v+s))) := by
  refine ⟨fun u v => hF.dep _ _,?_,?_⟩
  · exact hF.cont.comp (f := fun p : (V → ℝ) × ℝ × ℝ =>
      (p.1,clamp01 (p.2.1+s),clamp01 (p.2.2+s)))
      (continuous_fst.prodMk
        ((continuous_clamp01.comp (continuous_snd.fst.add_const s)).prodMk
          (continuous_clamp01.comp (continuous_snd.snd.add_const s))))
  · obtain ⟨B,hB⟩ := hF.bdd
    exact ⟨B,fun α u _ v _ => hB α _ (clamp01_mem _) _ (clamp01_mem _)⟩

/-- Clamping and shifting a pair's physical times preserves its actual RegCoef invariant. -/
theorem tree_shiftedRegCoef {V : Type} [DecidableEq V] {ζ : V → ℤ} {Z S : Finset V}
    {F : (V → ℝ) → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ}
    (hF : RegCoef ζ Z S F J) (s : ℝ) :
    RegCoef ζ Z S (fun α u v => F α (clamp01 (u+s)) (clamp01 (v+s)))
      (fun u v => J (clamp01 (u+s)) (clamp01 (v+s))) := by
  refine ⟨tree_shiftedNiceCoef hF.nice s,?_⟩
  obtain ⟨M,hM⟩ := hF.lim.bound
  obtain ⟨L,hL⟩ := hF.lim.lip
  refine ⟨⟨M,?_⟩,⟨max L 0,?_⟩,?_⟩
  · filter_upwards [hM] with ε hε
    exact fun u _ v _ => hε _ (clamp01_mem _) _ (clamp01_mem _)
  · filter_upwards [hL] with ε hε
    intro u _ v _ u' _ v' _
    have hu : |clamp01 (u+s)-clamp01 (u'+s)| ≤ |u-u'| := by
      simpa only [add_sub_add_right_eq_sub] using abs_clamp01_sub_le (u+s) (u'+s)
    have hv : |clamp01 (v+s)-clamp01 (v'+s)| ≤ |v-v'| := by
      simpa only [add_sub_add_right_eq_sub] using abs_clamp01_sub_le (v+s) (v'+s)
    calc
      _ ≤ L*(|clamp01 (u+s)-clamp01 (u'+s)|+|clamp01 (v+s)-clamp01 (v'+s)|) :=
        hε _ (clamp01_mem _) _ (clamp01_mem _) _ (clamp01_mem _) _ (clamp01_mem _)
      _ ≤ max L 0*(|clamp01 (u+s)-clamp01 (u'+s)|+|clamp01 (v+s)-clamp01 (v'+s)|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ max L 0*(|u-u'|+|v-v'|) :=
        mul_le_mul_of_nonneg_left (add_le_add hu hv) (le_max_right _ _)
  · intro u _ v _
    exact hF.lim.lim _ (clamp01_mem _) _ (clamp01_mem _)

end WaveTurbulence.RegAsymp
