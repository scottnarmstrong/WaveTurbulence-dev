/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts2
public import WaveTurbulence.Foundations.Vine.A.VineIngredientCarrier
public import WaveTurbulence.Foundations.Vine.A.VineBatchTreeIndex
public import WaveTurbulence.Foundations.Vine.A.VineProducer
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
import Mathlib.Tactic

/-!
# SKEL-FACTS 3: the three skeleton facts of S2's producer, in the forms `RepPr6` / `construction_facts` consume

For `pr : PrimeData LG` (skeleton `pr.skeleton`, decoded by `pr.data`) of a layered garden `LG` of width `2 * R`:

* `PrimeData.skeleton_irreducible`: `LG.garden.Irreducible → pr.skeleton.Irreducible`;
* `PrimeData.skeleton_balanced`: `IsBalancedSig LG.garden.sig → IsBalancedSig pr.skeleton.sig`;
* `PrimeData.skeleton_order_pos`: `1 ≤ pr.skeleton.order`, given `1 ≤ R`, irreducibility, the alternating signature
  at width `2` and non-regularity at width `2` (the `Stage1Carries` clause);
* `PrimeData.skelFacts_of_carries`: all three from `Stage1Carries P p N LG` and `1 ≤ R`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton

variable {R : ℕ}

theorem skeleton_irreducible {LG : LayeredGarden (2 * R)} (pr : PrimeData LG) (hG : LG.garden.Irreducible) :
    pr.skeleton.Irreducible :=
  pr.data.irreducible_of_decodes pr.prime.1 pr.decodes hG

theorem skeleton_sig_eq {LG : LayeredGarden (2 * R)} (pr : PrimeData LG) :
    pr.skeleton.sig = LG.garden.sig :=
  pr.data.sig_eq pr.prime.1 pr.decodes

theorem skeleton_balanced {LG : LayeredGarden (2 * R)} (pr : PrimeData LG)
    (hbal : IsBalancedSig LG.garden.sig) : IsBalancedSig pr.skeleton.sig := by
  rw [skeleton_sig_eq pr]; exact hbal

theorem skeleton_order_pos (hR : 1 ≤ R) {LG : LayeredGarden (2 * R)} (pr : PrimeData LG)
    (hG : LG.garden.Irreducible) (hsig : ∀ _ : 2 * R = 2, ∀ j, LG.garden.sig j = (-1) ^ (j : ℕ))
    (hnc : ∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden)) : 1 ≤ pr.skeleton.order :=
  pr.data.order_pos_of_decodes hR pr.prime pr.decodes hG hsig hnc

/-- B1b (R156): all three facts from the truncation-free carrier `Stage1CarriesW`. -/
theorem skelFacts_of_carriesW (P : WTParams) (p N : ℕ) (hR : 1 ≤ R) {LG : LayeredGarden (2 * R)}
    (hc : Stage1Mk.Stage1CarriesW P p N LG) (pr : PrimeData LG) :
    pr.skeleton.Irreducible ∧ IsBalancedSig pr.skeleton.sig ∧ 1 ≤ pr.skeleton.order := by
  obtain ⟨hcan, _, hbal, hnc⟩ := hc
  obtain ⟨_, hirr, _⟩ := hcan
  have hsig : ∀ _ : 2 * R = 2, ∀ j, LG.garden.sig j = (-1) ^ (j : ℕ) := by
    intro h2
    rcases hirr with ⟨h4, _⟩ | ⟨_, hs⟩
    · omega
    · exact hs
  have hG : LG.garden.Irreducible := by
    rcases hirr with ⟨_, hi⟩ | ⟨h2, _⟩
    · exact hi
    · have hR1 : R = 1 := by omega
      subst hR1
      exact WaveTurbulence.Comb.couple_irreducible LG.garden
  exact ⟨skeleton_irreducible pr hG, skeleton_balanced pr hbal, skeleton_order_pos hR pr hG hsig hnc⟩

/-- All three facts from the `Stage1Carries` hypothesis of the gate (canonical, balanced, non-regular couple). -/
theorem skelFacts_of_carries (P : WTParams) (p N : ℕ) (hR : 1 ≤ R) {LG : LayeredGarden (2 * R)}
    (hc : Stage1Carries P p N LG) (pr : PrimeData LG) :
    pr.skeleton.Irreducible ∧ IsBalancedSig pr.skeleton.sig ∧ 1 ≤ pr.skeleton.order :=
  skelFacts_of_carriesW P p N hR (Stage1Mk.stage1CarriesW_of_stage1Carries hc) pr

end WaveTurbulence.Represents
