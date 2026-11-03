/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzL2Core
public import WaveTurbulence.Foundations.WKEL2.SchwartzCollisionLinear
public import WaveTurbulence.Foundations.WKEL2.CollisionBound
public import WaveTurbulence.Foundations.WKEL2.BoundedTrilinear

/-!
# The collision trilinear map on the normed Schwartz core

The norm is the exact frozen weighted L² norm, not a Schwartz seminorm.
Theorem 7 therefore supplies the bound needed for Banach completion.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Transport the actual Schwartz collision map to its weighted L² image. -/
@[expose] def collisionCoreLinear (hd : 2 ≤ d) (s : ℝ) :
    WeightedSchwartzCore d s →ₗ[ℝ] WeightedSchwartzCore d s →ₗ[ℝ]
      WeightedSchwartzCore d s →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Mom d)) where
  toFun f :=
    { toFun := fun g => (weightedToL2CLM s).toLinearMap.comp
        ((schwartzCollisionLinear hd (weightedSchwartzCoreDecode s f)
          (weightedSchwartzCoreDecode s g)).comp (weightedSchwartzCoreDecode s))
      map_add' := fun g g' => by
        apply LinearMap.ext
        intro h
        simp only [ LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' := fun c g => by
        apply LinearMap.ext
        intro h
        simp only [ LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  map_add' f f' := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro h
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro h
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The core map is bounded in the exact weighted norm by Theorem 7. -/
theorem exists_collisionCore_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : WeightedSchwartzCore d s,
      ‖collisionCoreLinear (by omega) s f g h‖ ≤ C * ‖f‖ * ‖g‖ * ‖h‖ := by
  obtain ⟨C, hC, hb⟩ := exists_collisionOp_bound hd s hs
  refine ⟨C, hC, fun f g h => ?_⟩
  let f' := weightedSchwartzCoreDecode s f
  let g' := weightedSchwartzCoreDecode s g
  let h' := weightedSchwartzCoreDecode s h
  have H := (hb f' g' h' f'.continuous.measurable g'.continuous.measurable
    h'.continuous.measurable (memLp_weighted_schwartz s f')
    (memLp_weighted_schwartz s g') (memLp_weighted_schwartz s h')).2
  change ‖weightedToL2CLM s (WKE.collisionOpSchwartz _ f' g' h')‖ ≤ _
  rw [norm_weightedToL2CLM]
  simpa only [WKE.coe_collisionOpSchwartz, f', g', h', weightedL2Norm_coreDecode] using H

end WaveTurbulence.WKEL2
