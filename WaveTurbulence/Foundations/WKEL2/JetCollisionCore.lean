/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevModel
public import WaveTurbulence.Foundations.WKEL2.SchwartzTermLinear
public import WaveTurbulence.Foundations.WKEL2.JetWordBound
public import WaveTurbulence.Foundations.WKEL2.BoundedTrilinear

/-!
# Collision terms on finite weighted Schwartz jet cores

The norm is the supremum of actual frozen weighted L² jet norms.
Theorem 7 therefore supplies the bound needed for Banach completion.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Transport each actual Schwartz collision term to the weighted jet core. -/
@[expose] def jetCollisionCoreLinear (hd : 2 ≤ d) (s : ℝ) (m : ℕ) (j : Fin 4) :
    WeightedJetCore d s m →ₗ[ℝ] WeightedJetCore d s m →ₗ[ℝ]
      WeightedJetCore d s m →ₗ[ℝ] WeightedSobolevSpace d s m where
  toFun f :=
    { toFun := fun g => (schwartzToWeightedSobolevCLM s m).toLinearMap.comp
        ((schwartzTermLinear hd j (weightedJetCoreDecode s m f)
          (weightedJetCoreDecode s m g)).comp (weightedJetCoreDecode s m))
      map_add' := fun g g' => by
        apply LinearMap.ext
        intro h
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' := fun c g => by
        apply LinearMap.ext
        intro h
        simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
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

/-- Every literal collision term is bounded in each completed weighted jet model. -/
theorem exists_jetCollisionCore_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 4) (f g h : WeightedJetCore d s m),
      ‖jetCollisionCoreLinear (d := d) (by omega) s m j f g h‖ ≤ C * ‖f‖ * ‖g‖ * ‖h‖ := by
  let C := (exists_weightedJet_bound hd s hs m).choose
  have hC : 0 ≤ C := (exists_weightedJet_bound hd s hs m).choose_spec.1
  have hb := (exists_weightedJet_bound hd s hs m).choose_spec.2
  refine ⟨C, hC, fun j f g h => ?_⟩
  let f' := weightedJetCoreDecode s m f
  let g' := weightedJetCoreDecode s m g
  let h' := weightedJetCoreDecode s m h
  have H := hb j ![f', g', h']
  change ‖schwartzToWeightedSobolevCLM s m (WKE.collisionTermSchwartz (by omega) j f' g' h')‖ ≤ _
  rw [norm_schwartzToWeightedSobolevCLM]
  simpa [C, WKE.ktriple, f', g', h', norm_weightedJetCLM_coreDecode] using H

end WaveTurbulence.WKEL2
