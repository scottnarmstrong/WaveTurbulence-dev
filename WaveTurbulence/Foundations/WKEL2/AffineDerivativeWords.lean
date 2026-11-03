/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedJets
public import WaveTurbulence.Foundations.Analysis.WeightedSobolev

/-!
# Coordinate mixed partials as actual Schwartz directional words

An affine coordinate parametrization allows induction in the coordinate
dimension while every directional derivative stays in the original Schwartz space.
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance affineMomAddGroup : AddCommGroup (Mom d) :=
  (inferInstance : NormedAddCommGroup (Mom d)).toAddCommGroup
local instance affineMomModule : Module ℝ (Mom d) :=
  (inferInstance : NormedSpace ℝ (Mom d)).toModule

/-- An affine coordinate map with prescribed column vectors. -/
@[expose] def affineCoordinatePoint {n : ℕ} (k : Mom d) (V : Fin n → Mom d)
    (x : Fin n → ℝ) : Mom d := k + ∑ i, x i • V i

theorem affineCoordinatePoint_cons {n : ℕ} (k : Mom d) (V : Fin (n + 1) → Mom d)
    (t : ℝ) (x : Fin n → ℝ) :
    affineCoordinatePoint k V (Fin.cons t x) =
      affineCoordinatePoint (k + t • V 0) (Fin.tail V) x := by
  simp only [affineCoordinatePoint, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail_def, add_assoc]

theorem affineCoordinatePoint_head_tail {n : ℕ} (k : Mom d) (V : Fin (n + 1) → Mom d)
    (x : Fin (n + 1) → ℝ) :
    affineCoordinatePoint k V x =
      affineCoordinatePoint (k + x 0 • V 0) (Fin.tail V) (Fin.tail x) := by
  simpa only [Fin.cons_self_tail] using affineCoordinatePoint_cons k V (x 0) (Fin.tail x)

/-- Differentiate the head affine coordinate within the actual Schwartz class. -/
theorem deriv_affineCoordinatePoint_cons {n : ℕ} (f : 𝓢(Mom d, ℝ)) (k : Mom d)
    (V : Fin (n + 1) → Mom d) (t : ℝ) (x : Fin n → ℝ) :
    deriv (fun s => f (affineCoordinatePoint k V (Fin.cons s x))) t =
      (∂_{V 0} f) (affineCoordinatePoint (k + t • V 0) (Fin.tail V) x) := by
  have hi : HasDerivAt (fun s => affineCoordinatePoint k V (Fin.cons s x)) (V 0) t := by
    simp_rw [affineCoordinatePoint_cons, affineCoordinatePoint]
    simpa only [one_smul, id_eq] using
      ((((hasDerivAt_id t).smul_const (V 0)).const_add k).add_const
        (∑ i, x i • Fin.tail V i))
  have H := f.differentiableAt.hasFDerivAt.comp_hasDerivAt t hi
  simpa only [Function.comp_def, affineCoordinatePoint_cons,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using H.deriv

/-- An ordered list of directional derivatives as a continuous Schwartz operator. -/
@[expose] def derivativeWordCLM : List (Mom d) → 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ)
  | [] => ContinuousLinearMap.id ℝ _
  | v :: w => (LineDeriv.lineDerivOpCLM ℝ 𝓢(Mom d, ℝ) v).comp (derivativeWordCLM w)

theorem derivativeWordCLM_append (v w : List (Mom d)) (f : 𝓢(Mom d, ℝ)) :
    derivativeWordCLM (v ++ w) f = derivativeWordCLM v (derivativeWordCLM w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      simp only [List.cons_append, derivativeWordCLM, ContinuousLinearMap.comp_apply, ih]

/-- The directional word selected by a square-free coordinate derivative. -/
@[expose] def selectedDirections : {n : ℕ} → (Fin n → Bool) → (Fin n → Mom d) → List (Mom d)
  | 0, _, _ => []
  | _ + 1, b, V => selectedDirections (Fin.tail b) (Fin.tail V) ++ if b 0 then [V 0] else []

/-- Square-free mixed partials of affine Schwartz pullbacks are genuine directional words. -/
theorem mixedPartial_affine_schwartz : ∀ {n : ℕ} (b : Fin n → Bool) (V : Fin n → Mom d)
    (f : 𝓢(Mom d, ℝ)) (k : Mom d) (x : Fin n → ℝ),
    Analysis.mixedPartial n b (fun y => f (affineCoordinatePoint k V y)) x =
      derivativeWordCLM (selectedDirections b V) f (affineCoordinatePoint k V x)
  | 0, b, V, f, k, x => by simp only [Analysis.mixedPartial, selectedDirections, derivativeWordCLM,
      ContinuousLinearMap.id_apply]
  | n + 1, b, V, f, k, x => by
      rw [Analysis.mixedPartial]
      cases hb : b 0 with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          simp_rw [affineCoordinatePoint_cons]
          rw [mixedPartial_affine_schwartz]
          simp only [selectedDirections, hb, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [affineCoordinatePoint_head_tail]
      | true =>
          simp only [↓reduceIte]
          simp_rw [deriv_affineCoordinatePoint_cons]
          rw [mixedPartial_affine_schwartz]
          simp only [selectedDirections, hb, ↓reduceIte, derivativeWordCLM_append,
            derivativeWordCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
            LineDeriv.lineDerivOpCLM_apply]
          rw [affineCoordinatePoint_head_tail]

end WaveTurbulence.WKEL2
