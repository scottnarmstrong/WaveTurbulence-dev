/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevLetter
public import WaveTurbulence.Foundations.WKEL2.JetRestriction
public import WaveTurbulence.Foundations.WKEL2.JetIdentity

/-!
# Leibniz and moment identities for completed weighted-jet inputs

These are TARGET (schappend6) and (schappend7), extended by the proved
Schwartz density and trilinear continuity. All operators are actual bounded
extensions of the corresponding coordinate derivative or multiplier.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

private theorem continuous_mapped_trilinear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →L[ℝ] F →L[ℝ] F →L[ℝ] F) (A B C : E →L[ℝ] F) :
    Continuous (fun p : E × E × E => T (A p.1) (B p.2.1) (C p.2.2)) := by
  fun_prop

variable {d : ℕ}

local instance closedIdentityNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance closedIdentitySpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance closedIdentityNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance closedIdentitySpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance closedIdentityNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance closedIdentitySpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- The actual three-slot Schwartz coordinate identity. -/
theorem jetLetterCLM_collisionTerm (hd : 2 ≤ d) (a : JetLetter d) (j : Fin 4)
    (f g h : 𝓢(Mom d, ℝ)) :
    jetLetterCLM a (WKE.collisionTermSchwartz hd j f g h) =
      jetCoefficient a j 0 • WKE.collisionTermSchwartz hd j (jetLetterCLM a f) g h +
      jetCoefficient a j 1 • WKE.collisionTermSchwartz hd j f (jetLetterCLM a g) h +
      jetCoefficient a j 2 • WKE.collisionTermSchwartz hd j f g (jetLetterCLM a h) := by
  simpa [WKE.ktriple, Fin.sum_univ_three, Function.update] using
    jetLetterCLM_ktriple hd a j ![f, g, h]

/-- Exact Leibniz and weight identities hold for every completed finite-jet input. -/
theorem weightedSobolevLetterCLM_collisionTerm (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m M : ℕ) (hm : m + 1 ≤ M) (a : JetLetter d) (j : Fin 4)
    (u v w : WeightedSobolevSpace d s M) :
    weightedSobolevLetterCLM s m M hm a (jetTermBanach hd s hs M j u v w) =
      jetCoefficient a j 0 • jetTermBanach hd s hs m j
        (weightedSobolevLetterCLM s m M hm a u) (weightedSobolevForgetCLM s M m (by omega) v)
        (weightedSobolevForgetCLM s M m (by omega) w) +
      jetCoefficient a j 1 • jetTermBanach hd s hs m j
        (weightedSobolevForgetCLM s M m (by omega) u) (weightedSobolevLetterCLM s m M hm a v)
        (weightedSobolevForgetCLM s M m (by omega) w) +
      jetCoefficient a j 2 • jetTermBanach hd s hs m j
        (weightedSobolevForgetCLM s M m (by omega) u)
        (weightedSobolevForgetCLM s M m (by omega) v) (weightedSobolevLetterCLM s m M hm a w) := by
  apply dense_triple_ext (denseRange_schwartzToWeightedSobolevCLM (d := d) s M)
      (x := u) (y := v) (z := w)
  · fun_prop
  · let L := weightedSobolevLetterCLM s m M hm a
    let R := weightedSobolevForgetCLM (d := d) s M m (show m ≤ M by omega)
    have H (A B C : WeightedSobolevSpace d s M →L[ℝ] WeightedSobolevSpace d s m) :=
      continuous_mapped_trilinear (jetTermBanach hd s hs m j) A B C
    exact (((H L R R).const_smul (jetCoefficient a j 0)).add
      ((H R L R).const_smul (jetCoefficient a j 1))).add
      ((H R R L).const_smul (jetCoefficient a j 2))
  · intro f g h
    have H := congrArg (schwartzToWeightedSobolevCLM s m)
      (jetLetterCLM_collisionTerm (by omega) a j f g h)
    simpa only [jetTermBanach_schwartz, weightedSobolevLetterCLM_schwartz,
      weightedSobolevForgetCLM_schwartz, map_add, map_smul] using H

end WaveTurbulence.WKEL2
