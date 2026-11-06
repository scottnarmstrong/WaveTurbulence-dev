/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleGate

/-!
# Prop 6.1: non-dominant codes have vanishing explicit leading terms

* `chainSlice_not_dominant`: a non-dominant chain has a non-dominant slice, in the layer of one of its pairs;
* `coherentCouple_eq_zero`: for a coherent couple code that is not dominant, `LeafApp.coherentCouple = 0` on
  `[q,q+1] × [q',q'+1]` (`q' ≤ q`); every factor of TARGET (prooflayer1-1) is a single-layer leading term, and one
  of them is of a non-dominant code.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

theorem chainSlice_not_dominant {w : ℕ} (LG : LayeredGarden w) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), X.dominant = false →
      ∃ z ∈ chainNodesSet X ζ a, (SourceApp.chainSlice LG a (layerAt LG z) X).dominant = false
  | .nil, _, _, h => by simp [RegChain.dominant] at h
  | .pair m Qr Qg inner rest, ζ, a, h => by
    by_cases hhead : (inner.isNil && Qr.dominant && Qg.dominant) = true
    · have hrest : rest.dominant = false := by
        simp only [RegChain.dominant, Bool.and_eq_false_iff] at h
        simp only [Bool.and_eq_true] at hhead
        rcases h with ((h | h) | h) | h
        · simp_all
        · simp_all
        · simp_all
        · exact h
      obtain ⟨z, hz, hd⟩ := chainSlice_not_dominant LG rest (slotSign (slotSign ζ m.c) m.lone)
        (nextAddr a m inner) hrest
      refine ⟨z, ?_, ?_⟩
      · unfold chainNodesSet pairEndpoints at hz ⊢
        simp only [RegChain.linksAt, RegChain.pairsAt, List.map_cons, List.map_append, List.toFinset_cons,
          List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
        unfold nextAddr at hz
        tauto
      · rw [chainSlice_pair]
        split_ifs
        · simp only [RegChain.dominant, hd, Bool.and_false]
        · exact hd
    · refine ⟨a, root_mem_chainNodesSet _ _ _ _ _ _ _, ?_⟩
      rw [chainSlice_pair, ite_eq_left rfl]
      simp only [RegChain.dominant]
      simp only [Bool.not_eq_true] at hhead
      simp [hhead]

theorem LeafApp.tree_not_dominant (δ r : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ)
    (h : X.dominant = false) (t s : ℝ) (k : Mom d) : LeafApp.tree δ r H X ζ t s k = 0 := by
  unfold LeafApp.tree
  rw [ite_eq_right (by simp [h])]

theorem LeafApp.couple_not_dominant (δ r : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl)
    (h : Q.dominant = false) (t s : ℝ) (k : Mom d) : LeafApp.couple δ r H Q t s k = 0 := by
  unfold LeafApp.couple
  rw [ite_eq_right (by simp [h])]

/-- **Non-dominant coherent couples have vanishing explicit leading terms** (`q' ≤ q`). -/
theorem coherentCouple_eq_zero (δ : ℝ) {p q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) {Q : RegCpl}
    {LG : LayeredGarden 2} (hcoh : IsCoherentCoupleAt p q q' Q LG) (hdom : Q.dominant = false)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : LeafApp.coherentCouple δ LG H Q q q' t s k = 0 := by
  by_cases heq : q = q'
  · simp only [LeafApp.coherentCouple, heq, ↓reduceIte]
    exact LeafApp.couple_not_dominant _ _ _ _ hdom _ _ _
  have hlt : q' < q := lt_of_le_of_ne hqq (Ne.symm heq)
  cases Q with
  | triv => simp [RegCpl.dominant] at hdom
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [LeafApp.coherentCouple, heq, hlt, ↓reduceIte]
    exact LeafApp.couple_not_dominant _ _ _ _ hdom _ _ _
  | type2 Xp Xm Qlp =>
    have F := cohFacts_of_coherent hqq hqp hcoh
    rw [coherentCouple_type2_eq δ LG H Xp Xm Qlp hlt]
    have hbotz : (SourceApp.closeCouple (SourceApp.chainSlice LG (0, []) q' Xp) Xm Qlp).dominant = false →
        lowBot δ LG H Xm Qlp q' [] Xp s k = 0 := fun h => by
      unfold lowBot
      exact LeafApp.couple_not_dominant _ _ _ _ h _ _ _
    by_cases hXp : Xp.dominant = true
    · have hml : (Xm.dominant && Qlp.dominant) = false := by
        simp only [RegCpl.dominant, hXp, Bool.true_and] at hdom
        exact hdom
      rw [hbotz ?_, mul_zero]
      unfold SourceApp.closeCouple
      split_ifs with hn
      · simp only [Bool.and_eq_true] at hn
        have hXm : Xm = .nil := by cases Xm <;> simp_all [RegChain.isNil]
        subst hXm
        simpa [RegChain.dominant] using hml
      · simp only [RegCpl.dominant, Bool.and_assoc, hml, Bool.and_false]
    · simp only [Bool.not_eq_true] at hXp
      obtain ⟨z, hz, hzd⟩ := chainSlice_not_dominant LG Xp 1 (0, []) hXp
      have hlow := F.low z hz
      have hup : layerAt LG z ≤ q := by
        refine le_trans ?_ (root_le_type2 hqq hcoh)
        exact layerAt_le_of_under LG F.emb.node (F.emb.mem_nodes hz) (chain_endpoints_region Xp 1 _ z hz).1
      rcases eq_or_lt_of_le hlow with hr | hr
      · -- the bottom slice
        rw [hbotz ?_, mul_zero]
        rw [← hr] at hzd
        have hne : (SourceApp.chainSlice LG (0, []) q' Xp).isNil = false := by
          cases hc : SourceApp.chainSlice LG (0, []) q' Xp with
          | nil => rw [hc] at hzd; simp [RegChain.dominant] at hzd
          | pair _ _ _ _ _ => rfl
        unfold SourceApp.closeCouple
        rw [hne]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, RegCpl.dominant, hzd, Bool.false_and]
      rcases eq_or_lt_of_le hup with hr' | hr'
      · -- the top slice
        rw [LeafApp.tree_not_dominant _ _ _ _ _ (hr' ▸ hzd), mul_zero, zero_mul]
      · -- a middle slice
        rw [Finset.prod_eq_zero (i := layerAt LG z) (Finset.mem_Ioo.mpr ⟨hr, hr'⟩) (by
          unfold sliceFactor
          exact LeafApp.tree_not_dominant _ _ _ _ _ hzd _ _ _), zero_mul, zero_mul]

end WaveTurbulence.PL234
