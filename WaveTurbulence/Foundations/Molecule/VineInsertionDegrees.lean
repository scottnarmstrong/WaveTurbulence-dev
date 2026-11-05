/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIncidence
import Mathlib.Tactic

/-! # Degrees under arbitrary rung insertion (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

private theorem double_rungs_degree (us vs : List ℕ) (h : us.length=vs.length) (v : ℕ) :
    edgeDegree ((us.zip vs).flatMap fun p => [p,p]) v = 2*(us.count v+vs.count v) := by
  induction us generalizing vs with
  | nil => have hv : vs=[] := List.length_eq_zero_iff.mp h.symm; subst vs; rfl
  | cons u us ih =>
    cases vs with
    | nil => simp only [List.length_cons,List.length_nil] at h; omega
    | cons w vs =>
      have ht : us.length=vs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h
      simp only [List.zip_cons_cons,List.flatMap_cons,edgeDegree_append,ih vs ht]
      simp only [edgeDegree,List.map_cons,List.map_nil,List.count_cons,List.count_nil]
      omega

/-- Replacing the two slot bonds leaves every old incidence unchanged and
adds four incidences at each freshly inserted atom. This formula counts
fresh names with multiplicity and therefore needs no freshness hypothesis. -/
theorem insertRungs_degree (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k v : ℕ)
    (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1) :
    templateDegree (insertRungs T s k) v = templateDegree T v +
      4*(((List.range k).map (T.n+·)).count v+
        ((List.range k).map (T.n+k+·)).count v) := by
  by_cases hk : k=0
  · simp [hk,insertRungs_zero]
  · have hd1 := edgeDegree_erase h1 v
    have hd2 := edgeDegree_erase h2 v
    let us := (List.range k).map (T.n+·)
    let vs := (List.range k).map (T.n+k+·)
    have hl : us.length=vs.length := by simp only [us,vs,List.length_map]
    change edgeDegree (insertRungs T s k).bonds v = edgeDegree T.bonds v + _
    simp only [insertRungs,hk,ite_false,edgeDegree_append,railBonds_degree]
    have hdouble := double_rungs_degree us vs hl v
    dsimp only [us,vs] at hdouble
    rw [hdouble]
    omega

end WaveTurbulence.Vine
