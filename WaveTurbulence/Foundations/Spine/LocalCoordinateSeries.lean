/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LocalSmoothSeries
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
/-! Coordinate derivatives commute with the locally normally convergent source decoration sums. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem local_partialMom_tsum {I : Type*} {d : ℕ} {U : Set (Mom d)}
    {f : I → Mom d → ℂ} {v : ℕ → I → ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : ∀ i, ContDiff ℝ (1 : ℕ) (f i))
    (hv : ∀ r : ℕ, r ≤ 1 → Summable (v r))
    (hbound : ∀ (r : ℕ) (i : I) (x : Mom d), x ∈ U → r ≤ 1 →
      ‖iteratedFDeriv ℝ r (f i) x‖ ≤ v r i)
    (j : Fin d) (x : Mom d) (hx : x ∈ U) :
    partialMom j (fun y => ∑' i, f i y) x = ∑' i, partialMom j (f i) x := by
  have hD := local_iteratedFDeriv_tsum (N := (1 : ℕ∞)) hU hconn hf
    (fun r hr => hv r (by exact_mod_cast hr))
    (fun r i y hy hr => hbound r i y hy (by exact_mod_cast hr)) (by rfl) hx
  have hs : Summable fun i => iteratedFDeriv ℝ 1 (f i) x :=
    Summable.of_norm_bounded (hv 1 le_rfl) (fun i => hbound 1 i x hx le_rfl)
  have he (g : Mom d → ℂ) : partialMom j g x =
      iteratedFDeriv ℝ 1 g x (fun _ => EuclideanSpace.single j (1 : ℝ)) := by
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [he, hD]
  have hm := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Mom d) ℂ
    (fun _ => EuclideanSpace.single j (1 : ℝ))).map_tsum hs
  calc
    _ = ∑' i, iteratedFDeriv ℝ 1 (f i) x (fun _ => EuclideanSpace.single j (1 : ℝ)) := hm
    _ = _ := tsum_congr (fun i => (he (f i)).symm)

end WaveTurbulence.LGSpine
