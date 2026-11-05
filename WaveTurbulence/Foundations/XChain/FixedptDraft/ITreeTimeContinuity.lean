/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! (Copied verbatim from wt-cumul's INDUCT `TreeTimeContinuity.lean`, sha256 `6778400bbd3784055b0734177bafbf2b00c4477eefa56cda8f7073c0afde53e7`; namespace `Induct` ↦ `Fixedpt` and the
imports of copied INDUCT modules renamed.)

 Time continuity of the actual tree terms, derived from their Duhamel identity. -/
public section
namespace WaveTurbulence.Fixedpt
open MeasureTheory Finset Set
open SysAPI

/-- A tree term is continuous on the forward time interval. -/
theorem continuousOn_treeTerm {d : ℕ} (L γ δ : ℝ) (p : ℕ) (T : ℝ)
    (S : TTree) {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (n : Fin d → ℤ) :
    ContinuousOn (fun t => treeTerm L γ δ p S c t n) (Icc (p : ℝ) T) := by
  cases S with
  | leaf => simpa only [treeTerm_leaf] using continuousOn_const
  | node l m r =>
    have hi := intervalIntegrable_treeTriple L γ δ p l m r hc
    have hcont := intervalIntegral.continuous_primitive
      (fun a b => (hi a n).symm.trans (hi b n)) (p : ℝ)
    apply hcont.continuousOn.congr
    intro t ht
    exact treeTerm_node l m r L γ δ p hc ht.1 n

/-- Each order is a finite sum of continuous tree terms. -/
theorem continuousOn_treeTermN {d : ℕ} (L γ δ : ℝ) (p N : ℕ) (T : ℝ)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (n : Fin d → ℤ) :
    ContinuousOn (fun t => treeTermN L γ δ p N c t n) (Icc (p : ℝ) T) := by
  simp only [treeTermN_eq_sum]
  exact continuousOn_finsetSum _ fun S _ => continuousOn_treeTerm L γ δ p T S hc n

/-- The truncated Duhamel sum is continuous coordinatewise. -/
theorem continuousOn_aTr {d : ℕ} (L γ δ : ℝ) (p N : ℕ) (T : ℝ)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (n : Fin d → ℤ) :
    ContinuousOn (fun t => aTr L γ δ p N c t n) (Icc (p : ℝ) T) := by
  unfold aTr
  exact continuousOn_finsetSum _ fun k _ => continuousOn_treeTermN L γ δ p k T hc n

end WaveTurbulence.Fixedpt
