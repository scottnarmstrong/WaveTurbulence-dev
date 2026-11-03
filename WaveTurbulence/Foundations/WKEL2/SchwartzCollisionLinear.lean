/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SchwartzValued
public import WaveTurbulence.Foundations.WKE.SeriesTools

/-!
# The algebraic Schwartz collision trilinear map

Each linearity law is the corresponding law of the actual frozen collision
integral, whose absolute integrability on Schwartz inputs was proved in WKE.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The Schwartz collision operator bundled in all three linear slots. -/
@[expose] def schwartzCollisionLinear (hd : 2 ≤ d) :
    𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) where
  toFun f :=
    { toFun := fun g =>
        { toFun := WKE.collisionOpSchwartz hd f g
          map_add' := fun h h' => by
            ext k
            simpa only [WKE.coe_collisionOpSchwartz, add_apply] using
              WKE.collisionOp_add_right hd f g h h' k
          map_smul' := fun c h => by
            ext k
            simpa only [WKE.coe_collisionOpSchwartz, smul_apply, smul_eq_mul,
              RingHom.id_apply] using WKE.collisionOp_smul_right c h f g k }
      map_add' := fun g g' => by
        ext h k
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, WKE.coe_collisionOpSchwartz, add_apply] using
          WKE.collisionOp_add_mid hd f g g' h k
      map_smul' := fun c g => by
        ext h k
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, WKE.coe_collisionOpSchwartz, smul_apply,
          smul_eq_mul, RingHom.id_apply] using WKE.collisionOp_smul_mid c g f h k }
  map_add' f f' := by
    ext g h k
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, WKE.coe_collisionOpSchwartz, add_apply] using
      WKE.collisionOp_add_left hd f f' g h k
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro h
    apply SchwartzMap.ext
    intro k
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, WKE.coe_collisionOpSchwartz, smul_apply,
      smul_eq_mul, RingHom.id_apply] using WKE.collisionOp_smul_left c f g h k

/-- The bundled map is exactly the established Schwartz-valued collision operator. -/
theorem schwartzCollisionLinear_apply (hd : 2 ≤ d) (f g h : 𝓢(Mom d, ℝ)) :
    schwartzCollisionLinear hd f g h = WKE.collisionOpSchwartz hd f g h := rfl

end WaveTurbulence.WKEL2
