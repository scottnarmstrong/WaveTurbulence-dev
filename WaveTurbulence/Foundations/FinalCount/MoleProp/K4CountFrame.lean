/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountPlanar
public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
import Mathlib.Tactic

/-! # Aligning an actual planar strip with rotated floor cells

The frame is constructed from its actual nonzero strip coefficient. Both
coordinate bounds and its shell identity follow from orthogonality.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- Orthogonality preserves the actual squared radius about any real center. -/
theorem k4_rotated_radius_sq (c s : ℝ) (hf : c^2+s^2=1)
    (b : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    (k4RotU c s b n)^2+(k4RotV c s b n)^2 =
      ‖latticePoint 1 n-(WithLp.toLp 2 b : Mom 2)‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,latticePoint,PiLp.sub_apply,div_one]
  change _ = ((n 0 : ℝ)-b 0)^2+((n 1 : ℝ)-b 1)^2
  calc
    _ = (c^2+s^2)*(((n 0 : ℝ)-b 0)^2+((n 1 : ℝ)-b 1)^2) := by
      unfold k4RotU k4RotV
      ring
    _ = _ := by rw [hf,one_mul]

/-- A genuine planar sphere-and-strip count in the coefficient's actual
orthogonal frame. The original lattice is never replaced by a rotated grid. -/
theorem k4_planar_physical_shell_strip_le (S : Finset (Fin 2 → ℤ))
    (r b : Mom 2) {A M T W : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (hW : 0 ≤ W) (hr : A ≤ ‖r‖) (α K : ℝ)
    (hball : ∀ n ∈ S, ‖latticePoint 1 n-b‖ ≤ M)
    (hstrip : ∀ n ∈ S, |inner ℝ r (latticePoint 1 n-b)-α| ≤ T)
    (hshell : ∀ n ∈ S, |‖latticePoint 1 n-b‖^2-K| ≤ W) :
    (S.card : ℝ) ≤ (2*(T/A)+2)*(2*Real.sqrt (2*(W+4*M+1))+2)*9 := by
  have hrp : 0 < ‖r‖ := hA.trans_le hr
  let c := r 0/‖r‖
  let s := r 1/‖r‖
  have hr2 : (r 0)^2+(r 1)^2 = ‖r‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  have hf : c^2+s^2=1 := by
    dsimp only [c,s]
    field_simp [hrp.ne']
    exact hr2
  have hsq (n : Fin 2 → ℤ) :
      (k4RotU c s (fun i => b i) n)^2+(k4RotV c s (fun i => b i) n)^2 = ‖latticePoint 1 n-b‖^2 :=
    k4_rotated_radius_sq c s hf (fun i => b i) n
  have hcoord : ∀ n ∈ S, |k4RotU c s (fun i => b i) n| ≤ M ∧
      |k4RotV c s (fun i => b i) n| ≤ M := by
    intro n hn
    have he := hsq n
    have hU := sq_nonneg (k4RotU c s (fun i => b i) n)
    have hV := sq_nonneg (k4RotV c s (fun i => b i) n)
    have hn0 := norm_nonneg (latticePoint 1 n-b)
    have hb := hball n hn
    constructor
    · have ha := abs_nonneg (k4RotU c s (fun i => b i) n)
      have ha2 := sq_abs (k4RotU c s (fun i => b i) n)
      nlinarith only [he,hU,hV,hn0,hb,hM,ha,ha2]
    · have ha := abs_nonneg (k4RotV c s (fun i => b i) n)
      have ha2 := sq_abs (k4RotV c s (fun i => b i) n)
      nlinarith only [he,hU,hV,hn0,hb,hM,ha,ha2]
  have hst : ∀ n ∈ S, |k4RotU c s (fun i => b i) n-α/‖r‖| ≤ T/A := by
    intro n hn
    have he : k4RotU c s (fun i => b i) n-α/‖r‖ =
        (inner ℝ r (latticePoint 1 n-b)-α)/‖r‖ := by
      simp only [k4RotU,c,s,PiLp.inner_apply,Real.inner_apply,Fin.sum_univ_two,PiLp.sub_apply,latticePoint,div_one]
      ring
    rw [he,abs_div,abs_of_pos hrp]
    exact (div_le_div_of_nonneg_right (hstrip n hn) hrp.le).trans
      (div_le_div_of_nonneg_left hT hA hr)
  have hs : ∀ n ∈ S, |(k4RotU c s (fun i => b i) n)^2+(k4RotV c s (fun i => b i) n)^2-K| ≤ W := by
    intro n hn
    rw [hsq n]
    exact hshell n hn
  exact k4_planar_shell_strip_card_le S c s hf (fun i => b i) (div_nonneg hT hA.le) hM hW
    (α/‖r‖) K hcoord hst hs

end WaveTurbulence.MoleProp
