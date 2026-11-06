/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamActualEnergy
public import WaveTurbulenceVineParam.VineParamDirectedTransport
public import WaveTurbulence.Foundations.Molecule.VineGapConservation
import Mathlib.Tactic

/-! # Conservation and joint gaps through actual directed bond coordinates -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E]

/-- The integer directed incidence convention is the exact actual signed
internal dart sum, including the incidences of loops. -/
theorem directedFlow_actual (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) (k : D → E)
    (hk : ∀ d,k (M.mate d)=k d) :
    directedFlow (actualEnds M S e) v (fun j => k (e j).1)=internalSignedSum M S v k := by
  rw [directedFlow,internalSignedSum_eq_enumeration M S v e k hk]
  apply sum_congr rfl
  intro j _hj
  dsimp only [energySign,actualEnds]
  by_cases ha : M.atom (e j).1=v <;>
    by_cases hb : M.atom (M.mate (e j).1)=v <;>
      simp only [ha,hb,ite_true,ite_false] <;> norm_num

section Real
variable [Module ℝ E]

/-- Real source flow and its sign-only version agree exactly. -/
theorem internalSignedSum_eq_groupFlow (M : Molecule V D) (S : Finset V) (v : V) (k : D → E) :
    internalSignedSum M S v k=groupFlow M S k v := by
  apply sum_congr rfl
  intro d _hd
  simp only [Molecule.dartSign]
  split_ifs <;> simp only [one_smul,neg_smul]

/-- A source joint gap is exactly the directed graph's root divergence. -/
theorem directedFlow_eq_gap (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) (k : D → E)
    (hk : ∀ d,k (M.mate d)=k d) (hd : M.degIn S v=2)
    {r : E} (hr : IsGroupGap M S k v r) :
    directedFlow (actualEnds M S e) v (fun j => k (e j).1)=r := by
  classical
  rw [directedFlow_actual M S e v k hk,internalSignedSum_eq_groupFlow]
  exact (groupGap_eq_flow M hd hr).symm

end Real
end WaveTurbulence.Vine.Param
