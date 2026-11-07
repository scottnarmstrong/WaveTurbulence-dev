/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4LayTree

/-!
# A coherent carrier is the labelled carrier of its spine layers

`spineLabels LG a X` lists the layers of the top-level spine positions of `X`. For a coherent carrier:

* the spine labels are valid (`labOK_spine`), and every chain node has the labelled layer (`layer_eq_lay`). The
  inner chains are handled by pl23's `chainNodes_layer_of_ends`;
* **`coherent_lc_unique`**, **`coherent_low_unique`**, **`coherentTree_lt_unique`**: the coherent carrier is the
  labelled one (`lcLG`, constant `q'`, `ltLG`);
* `spine_readback`: the labelled carrier reads back its labels.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

/-- The layers of the top-level spine positions of a chain. -/
def spineLabels (LG : LayeredGarden w) : (Fin w × Path) → RegChain → List ℕ
  | _, .nil => []
  | a, .pair m _ _ inner rest => layerAt LG a :: spineLabels LG (nextAddr a m inner) rest

theorem labOK_spine {LG : LayeredGarden w} {q' : ℕ} : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : ℕ),
    SpineMono LG a X → (X ≠ .nil → layerAt LG a ≤ u) → (∀ z ∈ chainNodesSet X ζ a, q' ≤ layerAt LG z) →
    LabOK q' X (spineLabels LG a X) u
  | .nil, _, _, _, _, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, a, u, ⟨h1, h2⟩, hu, hlow => by
    refine ⟨hlow a (Links.root_mem_chainNodesSet _ _ _ _ _ _ _), hu (by simp), ?_⟩
    refine labOK_spine rest _ _ _ h2 (fun hne => ?_) fun z hz => hlow z (mem_chainNodesSet_rest hz)
    cases rest with
    | nil => exact absurd rfl hne
    | pair m' Qr' Qg' inner' rest' => exact h1 _ _ _ _ _ rfl

/-- **Every chain node of a coherent chain has the labelled layer of its spine labels.** -/
theorem layer_eq_lay {LG : LayeredGarden w} {d : ℕ} : ∀ {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree},
    ChainEmb LG.garden X ζ a h → ChainPairLayers LG X ζ a →
    ∀ z ∈ chainNodesSet X ζ a, layerAt LG z = chainLay X (spineLabels LG a X) d a z
  | .nil, _, _, _, _, _, z, hz => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, z, hz => by
    obtain ⟨hb, hr, hg, hi, hs⟩ := hL
    obtain ⟨-, -, hCi, hCr⟩ := hC.parts
    have nA := hC.node
    have nI := hCi.node
    have nB := nodeOfChainEmb hCi
    have eB : addrExt (addrExt a [m.c]) inner.lonePath = addrExt a ([m.c] ++ inner.lonePath) :=
      addrExt_append _ _ _
    rw [eB] at nB
    have lI : layerAt LG (addrExt a [m.c]) = layerAt LG a :=
      layer_sandwich nA nI nB (under_ext a _) (by rw [← eB]; exact under_ext _ _) rfl hb
    rcases ownPart_of_mem hz with ho | hrz
    · show _ = chainLay (.pair m Qr Qg inner rest) (layerAt LG a :: _) d a z
      rw [chainLay_own ho]
      rcases ho with rfl | rfl | ho | ho | ho
      · rfl
      · exact hb
      · exact hr z ho
      · exact hg z ho
      · exact chainNodes_layer_of_ends hCi hi lI (by rw [eB]; exact hb) z ho
    · show _ = chainLay (.pair m Qr Qg inner rest) (layerAt LG a :: _) d a z
      rw [chainLay_rest hrz]
      exact layer_eq_lay hCr hs z hrz

theorem spine_readback {LG : LayeredGarden w} {d : ℕ} : ∀ (X : RegChain) (ζ : ℤˣ) (ls : List ℕ)
    (a : Fin w × Path) (u : ℕ), LabOK d X ls u →
    (∀ z ∈ chainNodesSet X ζ a, layerAt LG z = chainLay X ls d a z) → spineLabels LG a X = ls
  | .nil, _, ls, _, _, hL, _ => hL.symm
  | .pair .., _, [], _, _, hL, _ => hL.elim
  | .pair m Qr Qg inner rest, ζ, l :: ls, a, u, ⟨_, _, h3⟩, h => by
    show layerAt LG a :: spineLabels LG _ rest = l :: ls
    rw [h a (Links.root_mem_chainNodesSet _ _ _ _ _ _ _), chainLay_own (ζ := ζ) (Or.inl rfl)]
    exact congrArg (l :: ·) (spine_readback rest _ ls (nextAddr a m inner) l h3 fun z hz =>
      (h z (mem_chainNodesSet_rest hz)).trans (chainLay_rest hz))

theorem layerAt_eq_of_garden {L₁ L₂ : LayeredGarden w} (hg : L₁.garden = L₂.garden) {z : Fin w × Path}
    (hz : ¬ z.2 ∈ (L₁.garden.tree z.1).nodes) : layerAt L₁ z = layerAt L₂ z := by
  have hz' : ¬ z.2 ∈ (L₂.garden.tree z.1).nodes := by rw [← hg]; exact hz
  unfold layerAt
  rw [dite_eq_right_of_eq_false (eq_false hz), dite_eq_right_of_eq_false (eq_false hz')]

/-- **A coherent type-2 couple is the labelled couple of its spine layers.** -/
theorem coherent_lc_unique {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2} {p q q' : ℕ} (hqq : q' ≤ q)
    (hqp : q ≤ p) (hc : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) :
    LabOK q' Xp (spineLabels LG ((0 : Fin 2), []) Xp) q ∧
      LG = lcLG Xp Xm Qlp (spineLabels LG ((0 : Fin 2), []) Xp) q q' := by
  have F := cohFacts_of_coherent hqq hqp hc
  have hL : LabOK q' Xp (spineLabels LG ((0 : Fin 2), []) Xp) q :=
    labOK_spine Xp 1 _ q F.sm (fun _ => root_le_type2 hqq hc) F.low
  have hg : LG.garden = (lcLG Xp Xm Qlp (spineLabels LG ((0 : Fin 2), []) Xp) q q').garden :=
    decodes_unique hc.2.1 (lc_decodes Xm Qlp)
  refine ⟨hL, layeredGarden_ext hg fun z => ?_⟩
  by_cases hz : z.2 ∈ (LG.garden.tree z.1).nodes
  · have hz' := cplNodes_covers_node hc.2.1 ⟨z, hz⟩
    rcases mem_cplNodes_type2.1 hz' with h1 | h1 | h1
    · rw [layer_eq_lay (d := q') F.emb F.pl z h1, lc_chain Xm Qlp ⟨hL, hqq⟩ z h1]
    · rw [F.minus z h1, lc_minus Xm Qlp ⟨hL, hqq⟩ z h1]
    · rw [F.lp z h1, lc_lp Xm Qlp ⟨hL, hqq⟩ z h1]
  · exact layerAt_eq_of_garden hg hz

/-- **A coherent couple not of type 2 is constantly in layer `q'`.** -/
theorem coherent_low_unique {Q : RegCpl} {LG : LayeredGarden 2} {p q q' : ℕ} (hqq : q' ≤ q)
    (hc : IsCoherentCoupleAt p q q' Q LG) (ht : Q.isType2 = false) : LG = constLayered (decodedCouple Q) q' := by
  have hg : LG.garden = (constLayered (decodedCouple Q) q').garden :=
    decodes_unique hc.2.1 (decodedCouple_decodes Q)
  refine layeredGarden_ext hg fun z => ?_
  by_cases hz : z.2 ∈ (LG.garden.tree z.1).nodes
  · have hg' : LG.garden = decodedCouple Q := hg
    have hz' : z.2 ∈ ((decodedCouple Q).tree z.1).nodes := by rw [← hg']; exact hz
    exact (layerAt_node LG (⟨z, hz⟩ : GNode LG.garden.tree)).trans
      ((layers_type1 hqq hc ht ⟨z, hz⟩).trans (layerAt_constLayered _ q' hz').symm)
  · exact layerAt_eq_of_garden hg hz

/-- Labelled layers are transported by address maps preserving `Under` both ways. -/
theorem chainLay_map {v : ℕ} (f : (Fin w × Path) → (Fin v × Path)) (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p)
    (hU : ∀ x y, Under (f x) (f y) ↔ Under x y) {d : ℕ} :
    ∀ (X : RegChain) (ls : List ℕ) (a z : Fin w × Path), chainLay X ls d (f a) (f z) = chainLay X ls d a z
  | .nil, _, _, _ => rfl
  | .pair .., [], _, _ => rfl
  | .pair m Qr Qg inner rest, l :: ls, a, z => by
    rw [chainLay_pair, chainLay_pair, show nextAddr (f a) m inner = f (nextAddr a m inner) from (hf _ _).symm]
    by_cases hu : Under (nextAddr a m inner) z
    · rw [ite_eq_left ((hU _ _).2 hu), ite_eq_left hu, chainLay_map f hf hU rest ls]
    · rw [ite_eq_right (fun h' => hu ((hU _ _).1 h')), ite_eq_right hu]

theorem treeIota_under (x y : Fin 1 × Path) : Under (treeIota x) (treeIota y) ↔ Under x y := by
  simp only [Under, treeIota, true_and, Subsingleton.elim x.1 y.1]

theorem layerAt_ltLG {X : RegChain} {μ : List ℕ} {q q' : ℕ} (h : LabOK q' X μ q ∧ q' ≤ q) {z : Fin 1 × Path}
    (hz : z.2 ∈ ((decodedTree X 1).tree z.1).nodes) : layerAt (ltLG X μ q q') z = ltLayer X μ q' z := by
  rw [ltLG_eq h]
  exact layerAt_node _ ⟨z, hz⟩

/-- **A coherent tree of sign `+` is the labelled tree of its spine layers.** -/
theorem coherentTree_lt_unique {X : RegChain} {LX : LayeredGarden 1} {p q q' : ℕ} (hqq : q' ≤ q)
    (hc : IsCoherentTreeAt p q q' X LX) (hs : LX.garden.sig 0 = 1) :
    LabOK q' X (spineLabels LX ((0 : Fin 1), []) X) q ∧ LX = ltLG X (spineLabels LX ((0 : Fin 1), []) X) q q' := by
  have F := treeCohFacts_of_coherent hc
  have hL : LabOK q' X (spineLabels LX ((0 : Fin 1), []) X) q :=
    labOK_spine X _ _ q F.sm (fun hne => F.high _ (by
      cases X with
      | nil => exact absurd rfl hne
      | pair m Qr Qg inner rest => exact Links.root_mem_chainNodesSet _ _ _ _ _ _ _)) F.low
  have hg : LX.garden = (ltLG X (spineLabels LX ((0 : Fin 1), []) X) q q').garden := by
    rw [ltLG_garden]
    exact decodesTree_unique F.dec (decodedTree_decodes X 1) (hs.trans rfl)
  refine ⟨hL, layeredGarden_ext hg fun z => ?_⟩
  by_cases hz : z.2 ∈ (LX.garden.tree z.1).nodes
  · have hz' : z.2 ∈ ((decodedTree X 1).tree z.1).nodes := by
      rw [← show LX.garden = decodedTree X 1 from hg.trans ltLG_garden]; exact hz
    rw [layerAt_ltLG ⟨hL, hqq⟩ hz']
    show layerAt LX z = chainLay X _ q' ((0 : Fin 2), []) (treeIota z)
    have hz1 : z = ((0 : Fin 1), z.2) := Prod.ext (Subsingleton.elim _ _) rfl
    rcases addrExt_mem_chainNodes F.dec ((0 : Fin 1), []) ⟨z, hz⟩ with h1 | h1
    · have h1' : z ∈ chainNodesSet X (LX.garden.sig 0) ((0 : Fin 1), []) := by
        rw [hz1]; simpa [addrExt] using h1
      rw [layer_eq_lay (d := q') (ChainEmb.of_decodesTree F.dec) F.pl z h1',
        show ((0 : Fin 2), ([] : Path)) = treeIota ((0 : Fin 1), []) from rfl,
        chainLay_map treeIota treeIota_hom treeIota_under]
    · have hz2 : z = ((0 : Fin 1), X.lonePath) := by rw [hz1]; exact Prod.ext rfl h1
      rw [hz2, F.lone]
      exact (chainLay_lone X _ _ _ ⟨rfl, by simp [addrExt]⟩).symm
  · exact layerAt_eq_of_garden hg hz

end WaveTurbulence.PL234
