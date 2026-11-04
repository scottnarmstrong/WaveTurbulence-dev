/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LowerJets
public import WaveTurbulence.Foundations.WKEL2.JetTameBound

/-!
# Tame estimates on the completed weighted Sobolev spaces

Schwartz density extends the actual top-order estimate to completed inputs.
The coefficient of the highest coordinate depends only on the base L² norm,
and the forcing term only on strictly lower coordinates.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance tameNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance tameSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance tameNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance tameSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance tameNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance tameSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Index a specified coordinate word within a sufficiently large jet. -/
@[expose] def wordJetIndex {n m : ℕ} (hnm : n ≤ m) (w : Fin n → JetLetter d) : JetIndex d m :=
  ⟨⟨n, by omega⟩, w⟩

/-- Exact frozen norm of a specified Schwartz word coordinate. -/
theorem norm_wordCoordinate_schwartz (s : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (w : Fin n → JetLetter d) (f : 𝓢(Mom d, ℝ)) :
    ‖weightedSobolevCoordinateCLM s m (wordJetIndex hnm w)
      (schwartzToWeightedSobolevCLM s m f)‖ = weightedL2Norm s (jetWordCLM (List.ofFn w) f) := by
  rw [weightedSobolevCoordinateCLM_schwartz, norm_weightedToL2CLM]
  rfl

/-- The actual tame term estimate extends to all completed finite-jet inputs. -/
theorem exists_jetTerm_tame_completed (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℕ) (hnm : n + 1 ≤ m) (w : Fin (n + 1) → JetLetter d)
      (j : Fin 4) (u : WeightedSobolevSpace d s m),
      ‖weightedSobolevCoordinateCLM s m (wordJetIndex hnm w) (jetTermBanach hd s hs m j u u u)‖ ≤
        3 * C * ‖weightedSobolevToL2CLM s m u‖ ^ 2 *
          ‖weightedSobolevCoordinateCLM s m (wordJetIndex hnm w) u‖ +
        3 ^ (n + 1) * C *
          ‖weightedSobolevLowerJetCLM s m n ((Nat.le_succ n).trans hnm) u‖ ^ 3 := by
  let C := (exists_jetWord_tame_bound hd s hs).choose
  have hC : 0 ≤ C := (exists_jetWord_tame_bound hd s hs).choose_spec.1
  have hb := (exists_jetWord_tame_bound hd s hs).choose_spec.2
  refine ⟨C, hC, fun m n hnm w j u => ?_⟩
  refine (denseRange_schwartzToWeightedSobolevCLM (d := d) s m).induction ?_
    (isClosed_le (by fun_prop) (by fun_prop)) u
  rintro _ ⟨f, rfl⟩
  simpa only [jetTermBanach_schwartz, norm_wordCoordinate_schwartz,
    weightedSobolevToL2CLM_schwartz, norm_weightedToL2CLM,
    weightedSobolevLowerJetCLM_schwartz, WKE.ktriple, C] using hb n w j f

/-- Full signed tame estimate: the coefficient 12C of the highest coordinate is order-independent. -/
theorem exists_jetCollision_tame_completed (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℕ) (hnm : n + 1 ≤ m) (w : Fin (n + 1) → JetLetter d)
      (u : WeightedSobolevSpace d s m),
      ‖weightedSobolevCoordinateCLM s m (wordJetIndex hnm w) (jetCollisionBanach hd s hs m u u u)‖ ≤
        12 * C * ‖weightedSobolevToL2CLM s m u‖ ^ 2 *
          ‖weightedSobolevCoordinateCLM s m (wordJetIndex hnm w) u‖ +
        4 * 3 ^ (n + 1) * C *
          ‖weightedSobolevLowerJetCLM s m n ((Nat.le_succ n).trans hnm) u‖ ^ 3 := by
  let C := (exists_jetTerm_tame_completed hd s hs).choose
  have hC : 0 ≤ C := (exists_jetTerm_tame_completed hd s hs).choose_spec.1
  have hb := (exists_jetTerm_tame_completed hd s hs).choose_spec.2
  refine ⟨C, hC, fun m n hnm w u => ?_⟩
  let P := weightedSobolevCoordinateCLM s m (wordJetIndex hnm w)
  let D := 3 * C * ‖weightedSobolevToL2CLM s m u‖ ^ 2 * ‖P u‖ +
    3 ^ (n + 1) * C * ‖weightedSobolevLowerJetCLM s m n ((Nat.le_succ n).trans hnm) u‖ ^ 3
  have H : ∀ j : Fin 4, ‖P (jetTermBanach hd s hs m j u u u)‖ ≤ D :=
    fun j => hb m n hnm w j u
  simp only [jetCollisionBanach, sub_apply, add_apply, map_sub, map_add]
  calc
    _ ≤ (‖P (jetTermBanach hd s hs m 0 u u u) - P (jetTermBanach hd s hs m 1 u u u) +
        P (jetTermBanach hd s hs m 2 u u u)‖ + ‖P (jetTermBanach hd s hs m 3 u u u)‖) :=
      norm_sub_le _ _
    _ ≤ ((‖P (jetTermBanach hd s hs m 0 u u u) - P (jetTermBanach hd s hs m 1 u u u)‖ +
        ‖P (jetTermBanach hd s hs m 2 u u u)‖) + ‖P (jetTermBanach hd s hs m 3 u u u)‖) :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (((‖P (jetTermBanach hd s hs m 0 u u u)‖ + ‖P (jetTermBanach hd s hs m 1 u u u)‖) +
        ‖P (jetTermBanach hd s hs m 2 u u u)‖) + ‖P (jetTermBanach hd s hs m 3 u u u)‖) :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ ((D + D) + D) + D := add_le_add (add_le_add (add_le_add (H 0) (H 1)) (H 2)) (H 3)
    _ = _ := by dsimp only [D, P]; ring

end WaveTurbulence.WKEL2
