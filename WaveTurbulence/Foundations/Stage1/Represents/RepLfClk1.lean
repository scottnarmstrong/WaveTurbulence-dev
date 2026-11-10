/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode2
public import WaveTurbulence.Foundations.Stage1.Represents.RepH5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, F-LEAFCLK: hinge data with the clock of a leaf lower child decoupled

The clock of a leaf lower child of a unit is the root time of its tree, which lies above the hinge clock and so outside
`outBox`.  The unit kernel does not depend on it (`hind`, from `unitKernelM_clocks` / `clRecenteredLocalKernelModC_congr`).
`HingeFam.leafWrap` zeroes the frequency of the leaf coordinates and absorbs `e^{πi m·t_d}` (a dummy time `td`) into the
amplitude; `exists_hinge_data_units_leaf` is `exists_hinge_data_units` with G1 asked only at the clock tuple whose leaf
coordinates are replaced by `td`, and the superposition identity delivered at the actual clocks.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract
open scoped ENNReal

theorem fsPhase_leaf_split {r : ℕ} (leaf : Fin r → Prop) [DecidablePred leaf] (m : Fin r → ℤ) (t td : Fin r → ℝ) :
    fsPhase m (fun i => if leaf i then td i else t i) =
      fsPhase (fun i => if leaf i then 0 else m i) t * fsPhase (fun i => if leaf i then m i else 0) td := by
  rw [fsPhase_eq_prod, fsPhase_eq_prod, fsPhase_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : leaf i <;> simp [h]

/-- Zero the frequencies of the leaf coordinates; absorb their phase at the dummy time `td` into the amplitude. -/
noncomputable def HingeFam.leafWrap {J : Type} {d : ℕ} (H : HingeFam J d) (leaf : J → Fin 3 → Prop)
    [∀ j i, Decidable (leaf j i)] (td : J → Fin 3 → ℝ) : HingeFam J d where
  Λ := H.Λ
  cnt := H.cnt
  w := H.w
  m j c l := fun i => if leaf j i then 0 else H.m j c l i
  a j c l E := H.a j c l E * fsPhase (fun i => if leaf j i then H.m j c l i else 0) (td j)
  w_nn := H.w_nn
  w_sum := H.w_sum
  a_one j c l E := by
    rw [norm_mul, fsPhase_norm, mul_one]
    exact H.a_one j c l E

theorem HingeFam.leafWrap_hasSum {J : Type} {d : ℕ} (H : HingeFam J d) (leaf : J → Fin 3 → Prop)
    [∀ j i, Decidable (leaf j i)] (td : J → Fin 3 → ℝ) (j : J) (c : Fin 4 → Fin d → ℤ) (E : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) {F : ℂ}
    (h : HasSum (fun l => (H.w j c l : ℂ) * H.a j c l E *
      fsPhase (H.m j c l) (fun i => if leaf j i then td j i else t i)) F) :
    HasSum (fun l => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) F := by
  have e : (fun l : H.Λ j c => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) =
      fun l : H.Λ j c => (H.w j c l : ℂ) * H.a j c l E *
        fsPhase (H.m j c l) (fun i => if leaf j i then td j i else t i) := by
    funext l
    show (H.w j c l : ℂ) * (H.a j c l E * fsPhase (fun i => if leaf j i then H.m j c l i else 0) (td j)) *
        fsPhase (fun i => if leaf j i then 0 else H.m j c l i) t = _
    rw [fsPhase_leaf_split (leaf j) (H.m j c l) t (td j)]
    ring
  show HasSum (fun l : H.Λ j c => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) F
  rw [e]
  exact h

end WaveTurbulence.Represents
