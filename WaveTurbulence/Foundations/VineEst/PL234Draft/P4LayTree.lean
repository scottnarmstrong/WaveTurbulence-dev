/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4LayFrame

/-!
# Labelled trees are coherent

For a chain `X` with labels `μ` (non-increasing, in `[q', q]`), the decoded tree `decodedTree X 1` carries the
layering `ltLayer` (`chainLay X μ q'` read on paths). It is a layering. With the frame of the couple
`closeCpl X = type2 X nil triv` as ambient garden:

* **`coherentTree_lt`**: `IsCoherentTreeAt p q q' X (ltLG X μ q q')`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The tree addresses in the `+` tree of a couple. -/
def treeIota (z : Fin 1 × Path) : Fin 2 × Path := ((0 : Fin 2), z.2)

theorem treeIota_hom (z : Fin 1 × Path) (p : Path) : treeIota (addrExt z p) = addrExt (treeIota z) p := rfl

/-- The layer of a decoded tree address of a labelled chain. -/
def ltLayer (X : RegChain) (μ : List ℕ) (q' : ℕ) (z : Fin 1 × Path) : ℕ :=
  chainLay X μ q' ((0 : Fin 2), []) (treeIota z)

theorem lt_isLayering {X : RegChain} {μ : List ℕ} {q q' : ℕ} (hL : LabOK q' X μ q) (hqq : q' ≤ q) :
    IsLayering (decodedTree X 1) (fun z => ltLayer X μ q' z.1) := by
  have hd := decodedTree_decodes X 1
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · show chainLay X μ q' _ ((0 : Fin 2), b.1.2 ++ [i]) ≤ chainLay X μ q' _ ((0 : Fin 2), b.1.2)
    exact chainLay_mono X μ q _ _ _ hL hqq ⟨rfl, List.prefix_append _ _⟩
  · by_cases hl : ℓ.1.2 = X.lonePath
    · have hm : (decodedTree X 1).mark ℓ ≠ none := by rw [hd.2.1 ℓ, ite_eq_left hl]; simp
      rw [((decodedTree X 1).pair_eq_iff ℓ).2 hm]
    · have hp := hd.2.2 ℓ hl
      have hmap := chain_pairsAt_map X treeIota treeIota_hom 1 ((0 : Fin 1), [])
      have key : ∀ x ∈ X.pairsAt 1 ((0 : Fin 1), []),
          chainLay X μ q' ((0 : Fin 2), []) (treeIota x.1) = chainLay X μ q' ((0 : Fin 2), []) (treeIota x.2) :=
        fun x hx => lay_pairs_eq X 1 μ ((0 : Fin 2), []) (treeIota x.1, treeIota x.2)
          (by rw [show ((0 : Fin 2), ([] : Path)) = treeIota ((0 : Fin 1), []) from rfl, hmap]
              exact List.mem_map.2 ⟨x, hx, rfl⟩)
      show ltLayer X μ q' ℓ.1 = ltLayer X μ q' ((decodedTree X 1).pair ℓ).1
      simp only [symmPairs, List.mem_append, List.mem_map] at hp
      rcases hp with hp | ⟨y, hy, he⟩
      · exact key _ hp
      · have e1 : y.2 = ℓ.1 := congrArg Prod.fst he
        have e2 : y.1 = ((decodedTree X 1).pair ℓ).1 := congrArg Prod.snd he
        unfold ltLayer
        rw [← e1, ← e2]
        exact (key y hy).symm

open Classical in
/-- **The labelled layering of the decoded tree** (junk constant layering for invalid labels). -/
noncomputable def ltLG (X : RegChain) (μ : List ℕ) (q q' : ℕ) : LayeredGarden 1 :=
  if h : LabOK q' X μ q ∧ q' ≤ q then ⟨decodedTree X 1, fun z => ltLayer X μ q' z.1, lt_isLayering h.1 h.2⟩
  else constLayered (decodedTree X 1) q'

theorem ltLG_garden {X : RegChain} {μ : List ℕ} {q q' : ℕ} : (ltLG X μ q q').garden = decodedTree X 1 := by
  unfold ltLG
  split_ifs <;> rfl

theorem ltLG_eq {X : RegChain} {μ : List ℕ} {q q' : ℕ} (h : LabOK q' X μ q ∧ q' ≤ q) :
    ltLG X μ q q' = ⟨decodedTree X 1, fun z => ltLayer X μ q' z.1, lt_isLayering h.1 h.2⟩ := by
  unfold ltLG
  split_ifs
  rfl

theorem closeCpl_tree0 (X : RegChain) :
    (decodedCouple (closeCpl X)).tree 0 = X.plug 1 .leaf := (decodedCouple_decodes (closeCpl X)).2.1

/-- **A labelled tree is coherent at `(p, q, q')`.** -/
theorem coherentTree_lt {X : RegChain} {μ : List ℕ} {p q q' : ℕ} (hwf : X.wf = true)
    (h : LabOK q' X μ q ∧ q' ≤ q) (hqp : q ≤ p) : IsCoherentTreeAt p q q' X (ltLG X μ q q') := by
  rw [ltLG_eq h]
  have hE := (frame_embeds (closeCpl X)).type2
  have hP := lcFrame_pattern (Xp := X) RegChain.nil RegCpl.triv h hqp
  have hcoh : CohOn (lcFrame (Xp := X) RegChain.nil RegCpl.triv h hqp) (X.linksAt 1 fA) := fun l hl =>
    hP.1 l (List.mem_append_left _ (List.mem_append_left _ hl))
  have hnode : ∀ path : Path, path ∈ (X.plug 1 .leaf).nodes →
      layerAt (lcFrame (Xp := X) RegChain.nil RegCpl.triv h hqp) (addrExt fA path) =
        chainLay X μ q' ((0 : Fin 2), []) ((0 : Fin 2), path) := fun path hp => by
    rw [show addrExt fA path = frameIota ((0 : Fin 2), path) from rfl, lcFrame_iota,
      layerAt_lcLG h (by show path ∈ ((decodedCouple (closeCpl X)).tree 0).nodes; rw [closeCpl_tree0]; exact hp),
      lcLayer_chain (z := ((0 : Fin 2), path)) ⟨rfl, List.nil_prefix⟩]
  refine ⟨hwf, decodedTree_decodes X 1, 2, lcFrame (Xp := X) RegChain.nil RegCpl.triv h hqp, fA, .leaf,
    frame_canon _ _ _ _ _ hP, hE.1, nodeSign_fA, hcoh, lcFrame_parA _ _ h hqp, ?_, ?_⟩
  · rw [hnode _ (lonePath_mem_plug X 1 _)]
    exact chainLay_lone X μ _ _ ⟨rfl, by simp [addrExt]⟩
  · rintro ⟨⟨j, path⟩, hz⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hz' : path ∈ (X.plug 1 .leaf).nodes := by
      have h2 : path ∈ ((decodedTree X 1).tree 0).nodes := hz
      rwa [(decodedTree_decodes X 1).1] at h2
    exact (hnode path hz').symm

end WaveTurbulence.PL234
