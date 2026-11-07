/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Lay

/-!
# Every labelled code has a coherent carrier with parent layers `q ≥ q'`

For a type-2 code `type2 Xp Xm Qlp` and labels `ls` of the top-level pairs of `Xp` (non-increasing, in `[q', q]`),
the decoded couple carries the layering `lcLayer`: `chainLay Xp ls q'` on the `+` tree and `q'` on the `-` tree. It
is a layering (`lc_isLayering`). Its frame (`P4Frame`) carries the `layerreg1` pattern, so it is canonical. Hence:

* **`coherent_lc`**: `IsCoherentCoupleAt p q q' (type2 Xp Xm Qlp) (lcLG …)`;
* **`coherent_low`**: a code that is not of type 2, constantly in layer `q'`, is coherent at `(p, q, q')`;
* **`coherentTree_lt`**: a labelled chain `X` is coherent at `(p, q, q')` with the layering `ltLG X μ`. The ambient
  garden is the frame of `closeCpl X`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The layer of a decoded address of a labelled type-2 couple. -/
def lcLayer (Xp : RegChain) (ls : List ℕ) (q' : ℕ) (z : Fin 2 × Path) : ℕ :=
  if z.1 = 0 then chainLay Xp ls q' ((0 : Fin 2), []) z else q'

theorem lcLayer_low {Xp : RegChain} {ls : List ℕ} {q' : ℕ} {z : Fin 2 × Path}
    (h : Under (addrExt ((0 : Fin 2), []) Xp.lonePath) z ∨ Under ((1 : Fin 2), []) z) : lcLayer Xp ls q' z = q' := by
  unfold lcLayer
  rcases h with h | h
  · have h0 : z.1 = 0 := by rw [← h.1]; rfl
    rw [ite_eq_left h0]
    exact chainLay_lone Xp ls _ z h
  · have h0 : ¬ z.1 = 0 := by rw [← h.1]; decide
    rw [ite_eq_right h0]

theorem lcLayer_chain {Xp : RegChain} {ls : List ℕ} {q' : ℕ} {z : Fin 2 × Path}
    (h : Under ((0 : Fin 2), []) z) : lcLayer Xp ls q' z = chainLay Xp ls q' ((0 : Fin 2), []) z := by
  unfold lcLayer
  have h0 : z.1 = 0 := h.1.symm
  rw [ite_eq_left h0]

section Couple

variable (Xp Xm : RegChain) (Qlp : RegCpl) (ls : List ℕ)

theorem lc_pairs {q' : ℕ} (x : (Fin 2 × Path) × (Fin 2 × Path))
    (hx : x ∈ (RegCpl.type2 Xp Xm Qlp).pairsAt ((0 : Fin 2), []) ((1 : Fin 2), [])) :
    lcLayer Xp ls q' x.1 = lcLayer Xp ls q' x.2 := by
  simp only [RegCpl.pairsAt, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · have h1 := (chainNodes_region Xp 1 _ x.1 (Finset.mem_union_right _ (mem_pairEndpoints_fst hx))).1
    have h2 := (chainNodes_region Xp 1 _ x.2 (Finset.mem_union_right _ (mem_pairEndpoints_snd hx))).1
    rw [lcLayer_chain h1, lcLayer_chain h2]
    exact lay_pairs_eq Xp 1 ls _ x hx
  · have h1 := (chainNodes_region Xm (-1) _ x.1 (Finset.mem_union_right _ (mem_pairEndpoints_fst hx))).1
    have h2 := (chainNodes_region Xm (-1) _ x.2 (Finset.mem_union_right _ (mem_pairEndpoints_snd hx))).1
    rw [lcLayer_low (Or.inr h1), lcLayer_low (Or.inr h2)]
  · have r1 := cplNodes_region (Finset.mem_union_right _ (mem_pairEndpoints_fst hx))
    have r2 := cplNodes_region (Finset.mem_union_right _ (mem_pairEndpoints_snd hx))
    rw [lcLayer_low (r1.imp id fun h => under_trans (under_ext _ _) h),
      lcLayer_low (r2.imp id fun h => under_trans (under_ext _ _) h)]

theorem lc_links {q' : ℕ} (x : (Fin 2 × Path) × (Fin 2 × Path))
    (hx : x ∈ (RegCpl.type2 Xp Xm Qlp).linksAt ((0 : Fin 2), []) ((1 : Fin 2), [])) :
    lcLayer Xp ls q' x.1 = lcLayer Xp ls q' x.2 := by
  simp only [RegCpl.linksAt, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · have h1 := (chainNodes_region Xp 1 _ x.1 (Finset.mem_union_left _ (mem_pairEndpoints_fst hx))).1
    have h2 := (chainNodes_region Xp 1 _ x.2 (Finset.mem_union_left _ (mem_pairEndpoints_snd hx))).1
    rw [lcLayer_chain h1, lcLayer_chain h2]
    exact lay_links_eq Xp 1 ls _ x hx
  · have h1 := (chainNodes_region Xm (-1) _ x.1 (Finset.mem_union_left _ (mem_pairEndpoints_fst hx))).1
    have h2 := (chainNodes_region Xm (-1) _ x.2 (Finset.mem_union_left _ (mem_pairEndpoints_snd hx))).1
    rw [lcLayer_low (Or.inr h1), lcLayer_low (Or.inr h2)]
  · have r1 := cplNodes_region (Finset.mem_union_left _ (mem_pairEndpoints_fst hx))
    have r2 := cplNodes_region (Finset.mem_union_left _ (mem_pairEndpoints_snd hx))
    rw [lcLayer_low (r1.imp id fun h => under_trans (under_ext _ _) h),
      lcLayer_low (r2.imp id fun h => under_trans (under_ext _ _) h)]

theorem lc_isLayering {q q' : ℕ} (hL : LabOK q' Xp ls q) (hqq : q' ≤ q) :
    IsLayering (decodedCouple (.type2 Xp Xm Qlp)) (fun z => lcLayer Xp ls q' z.1) := by
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · show lcLayer Xp ls q' (b.1.1, b.1.2 ++ [i]) ≤ lcLayer Xp ls q' b.1
    unfold lcLayer
    by_cases h : b.1.1 = 0
    · rw [ite_eq_left h, ite_eq_left h]
      exact chainLay_mono Xp ls q _ _ _ hL hqq ⟨rfl, List.prefix_append _ _⟩
    · rw [ite_eq_right h, ite_eq_right h]
  · have hp := (decodedCouple_decodes (RegCpl.type2 Xp Xm Qlp)).2.2.2 ℓ
    show lcLayer Xp ls q' ℓ.1 = lcLayer Xp ls q' (decodedCouple (.type2 Xp Xm Qlp) |>.pair ℓ).1
    simp only [symmPairs, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨y, hy, he⟩
    · exact lc_pairs Xp Xm Qlp ls _ hp
    · have e1 : y.2 = ℓ.1 := congrArg Prod.fst he
      have e2 : y.1 = (decodedCouple (.type2 Xp Xm Qlp) |>.pair ℓ).1 := congrArg Prod.snd he
      rw [← e1, ← e2]
      exact (lc_pairs Xp Xm Qlp ls _ hy).symm

open Classical in
/-- **The labelled layering of the decoded couple** (junk constant layering for invalid labels). -/
noncomputable def lcLG (q q' : ℕ) : LayeredGarden 2 :=
  if h : LabOK q' Xp ls q ∧ q' ≤ q then
    ⟨decodedCouple (.type2 Xp Xm Qlp), fun z => lcLayer Xp ls q' z.1, lc_isLayering Xp Xm Qlp ls h.1 h.2⟩
  else constLayered (decodedCouple (.type2 Xp Xm Qlp)) q'

variable {Xp Xm Qlp ls}

theorem lcLG_garden {q q' : ℕ} : (lcLG Xp Xm Qlp ls q q').garden = decodedCouple (.type2 Xp Xm Qlp) := by
  unfold lcLG
  split_ifs <;> rfl

theorem lcLG_eq {q q' : ℕ} (h : LabOK q' Xp ls q ∧ q' ≤ q) : lcLG Xp Xm Qlp ls q q' =
    ⟨decodedCouple (.type2 Xp Xm Qlp), fun z => lcLayer Xp ls q' z.1, lc_isLayering Xp Xm Qlp ls h.1 h.2⟩ := by
  unfold lcLG
  split_ifs
  rfl

theorem layerAt_lcLG {q q' : ℕ} (h : LabOK q' Xp ls q ∧ q' ≤ q) {z : Fin 2 × Path}
    (hz : z.2 ∈ ((decodedCouple (.type2 Xp Xm Qlp)).tree z.1).nodes) :
    layerAt (lcLG Xp Xm Qlp ls q q') z = lcLayer Xp ls q' z := by
  rw [lcLG_eq h]
  exact layerAt_node _ ⟨z, hz⟩

theorem lc_node {z : Fin 2 × Path} (hz : z ∈ cplNodes (.type2 Xp Xm Qlp) ((0 : Fin 2), []) ((1 : Fin 2), [])) :
    z.2 ∈ ((decodedCouple (.type2 Xp Xm Qlp)).tree z.1).nodes :=
  (Embeds.of_decodes (decodedCouple_decodes _)).mem_nodes hz

end Couple

end WaveTurbulence.PL234
