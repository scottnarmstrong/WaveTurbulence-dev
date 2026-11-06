/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceDecoder
public import WaveTurbulenceVineParam.VineParamNormalizedSplicePhases
import Mathlib.Tactic

/-! # Resonance transport in the full reanchored source chart -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- The physical gap sign is determined by the two joint memberships. -/
@[expose] def gapSign (a b : V) : ℤ :=
  (if a ∈ G.cap then 1 else 0)-(if b ∈ G.cap then 1 else 0)

/-- Every source cap has a ternary physical gap sign. -/
theorem gapSign_unit (a b : V) : G.gapSign a b ∈ ({-1,0,1} : Finset ℤ) := by
  by_cases ha : a ∈ G.cap <;> by_cases hb : b ∈ G.cap <;> simp [gapSign,ha,hb]

/-- The complete source inverse obeys the exact joint/interior energy law. -/
theorem globalSourceChart_energy {d : ℕ} (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : Mom d) (k : DirectedRootFiber G.ends a b r) (xy : Mom d×Mom d) (v : V) :
    directedEnergy G.newEnds (.inl (G.σ v)) ((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1=
      directedEnergy G.ends v k.1+2*inner ℝ (directedFlow G.ends v k.1)
        (if v ∈ G.cap then G.pattern.correction (spliceGap G.cap a b r) xy else 0) := by
  rw [G.globalSourceChart_decode]
  unfold newEnds
  rw [splice_energy_transport G.ends G.i G.j G.distinct G.σ G.p G.q G.c G.d v G.pattern
    G.cap G.outer_p G.outer_q G.inner_c G.inner_d G.fixed_p G.fixed_q G.port_c G.port_d
    G.first G.second G.uncut k.1 (spliceGap G.cap a b r) (k.1 G.j) xy
    (G.source_cut_gap a b hab r k) rfl]
  exact directedEnergy_sub_of_balanced G.ends v k.1 _ (G.balanced v)

/-- Every inserted s slot in the reanchored chart has exactly the contract
negative bilinear phase, independent of all old coordinates. -/
theorem anchoredInsertionChart_s_phase {d : ℕ} {ι : Type*} [DecidableEq ι]
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : Mom d)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → Mom d)) (ref : ι) (anchorInside : Bool)
    (x : ι ⊕ Fin 2 → Mom d) :
    directedEnergy G.newEnds (.inr 1)
      ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1=
        -2*inner ℝ (x (.inr 0)) (x (.inr 1)) := by
  rw [G.anchoredInsertionChart_decode_labels,G.globalSourceChart_decode]
  exact normalizedSplice_s_phase G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern _
    (G.gapSign a b) r _ _ _

/-- Every inserted t slot in the reanchored chart has exactly the contract
positive bilinear phase and its fixed ternary physical-gap correction. -/
theorem anchoredInsertionChart_t_phase {d : ℕ} {ι : Type*} [DecidableEq ι]
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : Mom d)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → Mom d)) (ref : ι) (anchorInside : Bool)
    (x : ι ⊕ Fin 2 → Mom d) :
    directedEnergy G.newEnds (.inr 0)
      ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1=
        2*inner ℝ (x (.inr 0)) (x (.inr 1))+2*inner ℝ r
          ((G.pattern.contractCorrection (G.gapSign a b) 0 : ℝ) • x (.inr 0)+
            (G.pattern.contractCorrection (G.gapSign a b) 1 : ℝ) • x (.inr 1)+
            (G.pattern.contractCorrection (G.gapSign a b) 2 : ℝ) • r) := by
  rw [G.anchoredInsertionChart_decode_labels,G.globalSourceChart_decode]
  exact normalizedSplice_t_phase G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern _
    (G.gapSign a b) r _ _ _

end WaveTurbulence.Vine.Param.RungSpliceGeometry
