/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzTermAlgebra

/-!
# The algebraic Schwartz collision term trilinear maps

Each linearity law is the corresponding law of the actual frozen collision
integral, whose absolute integrability on Schwartz inputs was proved in WKE.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Each Schwartz collision term bundled in all three linear slots. -/
@[expose] def schwartzTermLinear (hd : 2 ≤ d) (j : Fin 4) :
    𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) →ₗ[ℝ] 𝓢(Mom d, ℝ) where
  toFun f :=
    { toFun := fun g =>
        { toFun := WKE.collisionTermSchwartz hd j f g
          map_add' := fun h h' => by
            ext k
            simpa only [WKE.coe_collisionTermSchwartz, add_apply] using
              collisionTerm_add_right hd j f g h h' k
          map_smul' := fun c h => by
            ext k
            simpa only [WKE.coe_collisionTermSchwartz, smul_apply, smul_eq_mul,
              RingHom.id_apply] using collisionTerm_smul_right j c f g h k }
      map_add' := fun g g' => by
        ext h k
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, WKE.coe_collisionTermSchwartz, add_apply] using
          collisionTerm_add_mid hd j f g g' h k
      map_smul' := fun c g => by
        ext h k
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, WKE.coe_collisionTermSchwartz, smul_apply,
          smul_eq_mul, RingHom.id_apply] using collisionTerm_smul_mid j c f g h k }
  map_add' f f' := by
    ext g h k
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, WKE.coe_collisionTermSchwartz, add_apply] using
      collisionTerm_add_left hd j f f' g h k
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro h
    apply SchwartzMap.ext
    intro k
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, WKE.coe_collisionTermSchwartz, smul_apply,
      smul_eq_mul, RingHom.id_apply] using collisionTerm_smul_left j c f g h k

/-- The bundled map is exactly the established Schwartz-valued collision operator. -/
theorem schwartzTermLinear_apply (hd : 2 ≤ d) (j : Fin 4) (f g h : 𝓢(Mom d, ℝ)) :
    schwartzTermLinear hd j f g h = WKE.collisionTermSchwartz hd j f g h := rfl

end WaveTurbulence.WKEL2
