/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetCollisionCore
public import WaveTurbulence.Foundations.WKEL2.DenseTrilinearExtension

/-!
# Collision operators on every complete finite weighted jet space
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance jetCoreNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedJetCore d s m) := inferInstance
local instance jetCoreSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedJetCore d s m) := inferInstance
local instance jetSobolevNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance jetSobolevSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

local instance jetCoreNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetCoreSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetCoreNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedJetCore d s m →L[ℝ] WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetCoreSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedJetCore d s m →L[ℝ] WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance

local instance jetBanachNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetBanachSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetBanachNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance jetBanachSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Bundle the proved bound on the actual Schwartz jet core. -/
@[expose] def jetCollisionCoreCLM (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (j : Fin 4) :
    WeightedJetCore d s m →L[ℝ] WeightedJetCore d s m →L[ℝ]
      WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s m :=
  boundedTrilinear (V := WeightedJetCore d s m) (F := WeightedSobolevSpace d s m)
    (jetCollisionCoreLinear (d := d) (by omega) s m j)
    (exists_jetCollisionCore_bound hd s hs m).choose
    (exists_jetCollisionCore_bound hd s hs m).choose_spec.1
    ((exists_jetCollisionCore_bound hd s hs m).choose_spec.2 j)

/-- Continuous extension of each collision term to the completed finite weighted jet space. -/
@[expose] def jetTermBanach (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (j : Fin 4) :
    WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m :=
  denseTrilinearExtension (V := WeightedJetCore d s m) (E := WeightedSobolevSpace d s m)
    (F := WeightedSobolevSpace d s m) (weightedJetCoreInclusion s m)
    (denseRange_weightedJetCoreInclusion s m) (jetCollisionCoreCLM hd s hs m j)

/-- The completed term is exactly the original Schwartz term on Schwartz data. -/
theorem jetTermBanach_schwartz (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (j : Fin 4) (f g h : 𝓢(Mom d, ℝ)) :
    jetTermBanach hd s hs m j (schwartzToWeightedSobolevCLM s m f)
      (schwartzToWeightedSobolevCLM s m g) (schwartzToWeightedSobolevCLM s m h) =
      schwartzToWeightedSobolevCLM s m (WKE.collisionTermSchwartz (by omega) j f g h) := by
  have H := denseTrilinearExtension_apply (V := WeightedJetCore d s m)
    (E := WeightedSobolevSpace d s m) (F := WeightedSobolevSpace d s m)
    (weightedJetCoreInclusion s m) (denseRange_weightedJetCoreInclusion s m)
    (jetCollisionCoreCLM hd s hs m j) (weightedJetCoreEquiv s m f)
    (weightedJetCoreEquiv s m g) (weightedJetCoreEquiv s m h)
  simp only [← schwartzToWeightedSobolevCLM_eq_inclusion] at H
  change jetTermBanach hd s hs m j _ _ _ = _ at H
  refine H.trans ?_
  simp only [jetCollisionCoreCLM, boundedTrilinear_apply, jetCollisionCoreLinear,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, weightedJetCoreDecode,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, schwartzTermLinear_apply]
  rfl

/-- The full signed collision field in the completed weighted derivative space. -/
@[expose] def jetCollisionBanach (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) :
    WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m :=
  jetTermBanach hd s hs m 0 - jetTermBanach hd s hs m 1 +
    jetTermBanach hd s hs m 2 - jetTermBanach hd s hs m 3

/-- Exact agreement of the full completed field with the frozen Schwartz collision. -/
theorem jetCollisionBanach_schwartz (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (f g h : 𝓢(Mom d, ℝ)) :
    jetCollisionBanach hd s hs m (schwartzToWeightedSobolevCLM s m f)
      (schwartzToWeightedSobolevCLM s m g) (schwartzToWeightedSobolevCLM s m h) =
      schwartzToWeightedSobolevCLM s m (WKE.collisionOpSchwartz (by omega) f g h) := by
  simp only [jetCollisionBanach, sub_apply, add_apply, jetTermBanach_schwartz,
    WKE.collisionOpSchwartz, map_sub, map_add]

end WaveTurbulence.WKEL2
