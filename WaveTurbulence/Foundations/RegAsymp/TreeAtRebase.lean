/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeShiftedCoefficients
public import WaveTurbulence.Foundations.ClassJR.MCTExp

/-! # Exact rebasing of the literal tree chain with its lone-leaf time constraint -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set ClassJR

private theorem chainT_congr_Icc {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ) (T : ℝ) :
    ∀ (c : LegalCode) (q : ℕ) {F F' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (_ : ∀ j t s, t ∈ Icc (0:ℝ) T → s ∈ Icc (0:ℝ) T → F j α t s = F' j α t s)
    {g g' : ℝ → ℂ} (_ : ∀ s ∈ Icc (0:ℝ) T, g s = g' s) (t : ℝ) (_ : t ∈ Icc (0:ℝ) T),
    chainT σ ε c q F α t g = chainT σ ε c q F' α t g'
  | .nil, _, _, _, _, _, _, _, hg, t, ht => hg t ht
  | .node i r, q, F, F', α, hF, g, g', hg, t, ht => by
    rw [chainT_node, chainT_node]
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le ht.1] at hta
    have hta' : ta ∈ Icc (0:ℝ) T := ⟨hta.1,hta.2.trans ht.2⟩
    congr 1
    refine chainT_congr_Icc σ ε T i (q+1) α hF (fun t' ht' => ?_) ta hta'
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le ht'.1] at htb
    have htb' : tb ∈ Icc (0:ℝ) T := ⟨htb.1,htb.2.trans ht'.2⟩
    rw [hF q ta tb hta' htb', chainT_congr_Icc σ ε T r (q+i.size+1) α hF hg tb htb']

/-- Literal tree rebasing. Every pair is evaluated at its original shifted physical times;
clamping only chooses an extension outside the interval actually used by the chain. -/
theorem tree_chainT_rebase_clamp {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ)
    (c : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    chainT σ ε c q F α t (fun u => if s < u then 1 else 0) =
      chainT σ ε c q (fun j β u v => F j β (clamp01 (u+s)) (clamp01 (v+s)))
        α (t-s) (fun _ => 1) := by
  rw [chainT_rebase c q F α hs (fun u hu => by simp [not_lt.mpr hu]) hst.le]
  apply (chainT_congr_pos c q _ α (g' := fun _ => 1) (fun u hu => by simp [hu]) (by linarith : 0 < t-s)).trans
  apply chainT_congr_Icc σ ε (t-s) c q α _ (fun _ _ => rfl) (t-s) ⟨by linarith,le_rfl⟩
  intro j u v hu hv
  rw [clamp01_eq (show u+s ∈ Icc (0:ℝ) 1 from ⟨by linarith [hu.1],by linarith [hu.2]⟩),
    clamp01_eq (show v+s ∈ Icc (0:ℝ) 1 from ⟨by linarith [hv.1],by linarith [hv.2]⟩)]

end WaveTurbulence.RegAsymp
