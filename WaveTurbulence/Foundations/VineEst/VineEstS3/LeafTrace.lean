/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # Leaf lower children: the trace argument on the `sumint` output box

`XNorm00Restr_leaf`: if the kernel `Kfun` equals `Ifun` evaluated at the effective output times `leafT` (the time of a
leaf lower child replaced by the lower end `qOut c` of its unit interval) on the output box, and `Ifun` is continuous in time
on the closed cube of output times, then `‖Kfun‖_{𝔛^{θ,0,0}(outBox)} ≤ traceConst(θ)² ‖Ifun‖_{𝔛^{θ,0,0}(outBox)}`
(Tietze extension of `Ifun` from the cube, then `XNorm00Restr_trace` once per leaf child).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.DegenVine MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- The closed cube `∏ [q_i, q_i + 1]` of output times. -/
def cubeSet (q : Fin 3 → ℕ) : Set (Fin 3 → ℝ) := {t | ∀ i, (q i : ℝ) ≤ t i ∧ t i ≤ q i + 1}

theorem isClosed_cubeSet (q : Fin 3 → ℕ) : IsClosed (cubeSet q) := by
  have : cubeSet q = ⋂ i, {t : Fin 3 → ℝ | (q i : ℝ) ≤ t i} ∩ {t | t i ≤ q i + 1} := by
    ext t; simp [cubeSet]
  rw [this]
  exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_apply i) continuous_const)

theorem exists_continuous_extension {V : Type*} (q : Fin 3 → ℕ) (K : Set V) (H : (Fin 3 → ℝ) → V → ℂ)
    (hH : ∀ v ∈ K, ContinuousOn (fun t => H t v) (cubeSet q)) :
    ∃ H' : (Fin 3 → ℝ) → V → ℂ, (∀ v ∈ K, Continuous fun t => H' t v) ∧
      ∀ t ∈ cubeSet q, ∀ v, v ∈ K → H' t v = H t v := by
  classical
  have h1 : ∀ v, ∃ g : (Fin 3 → ℝ) → ℂ, Continuous g ∧ (v ∈ K → ∀ t ∈ cubeSet q, g t = H t v) := by
    intro v
    by_cases hv : v ∈ K
    · obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (isClosed_cubeSet q)
        (⟨fun t => H t.1 v, continuousOn_iff_continuous_domRestrict.1 (hH v hv)⟩ : C(cubeSet q, ℂ))
      exact ⟨g, g.continuous, fun _ t ht => congrArg (fun f : C(cubeSet q, ℂ) => f ⟨t, ht⟩) hg⟩
    · exact ⟨fun _ => 0, continuous_const, fun h => absurd h hv⟩
  choose g hg1 hg2 using h1
  exact ⟨fun t v => g v t, fun v _ => hg1 v, fun t ht v hv => hg2 v hv t ht⟩



/-- The effective output times: a leaf lower child's (dummy) time is replaced by the lower end of its unit interval. -/
def leafT (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (if b2 then Function.update (if b1 then Function.update t 1 (q 1 : ℝ) else t) 2 (q 2 : ℝ)
    else (if b1 then Function.update t 1 (q 1 : ℝ) else t))

theorem continuousOn_update_comp {V : Type*} {K : Set V} (q : Fin 3 → ℕ) (H : (Fin 3 → ℝ) → V → ℂ) (j : Fin 3)
    (hH : ∀ v ∈ K, ContinuousOn (fun t => H t v) (cubeSet q)) (v : V) (hv : v ∈ K) :
    ContinuousOn (fun t => H (Function.update t j (q j : ℝ)) v) (cubeSet q) := by
  refine (hH v hv).comp (continuous_id.update j continuous_const).continuousOn fun t ht i => ?_
  by_cases hi : i = j
  · subst hi; simp
  · simpa [Function.update_of_ne hi] using ht i

theorem leafT_zero (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] (t : Fin 3 → ℝ) :
    leafT q b1 b2 t 0 = t 0 := by
  unfold leafT; split_ifs <;> simp

theorem leafT_one (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] (t : Fin 3 → ℝ) :
    leafT q b1 b2 t 1 = if b1 then (q 1 : ℝ) else t 1 := by
  unfold leafT; split_ifs <;> simp

theorem leafT_two (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] (t : Fin 3 → ℝ) :
    leafT q b1 b2 t 2 = if b2 then (q 2 : ℝ) else t 2 := by
  unfold leafT; split_ifs <;> simp

end WaveTurbulence.VineEstS3
