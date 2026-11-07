/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4FrameCanon
public import WaveTurbulence.Foundations.RegStruct.DecodedTree

/-!
# Every well-formed code has a coherent carrier with equal parent layers

LAYERREG gives the layering of a coherent embedded couple (`layerreg1` (1), `layerPattern_of_canon`) and the
characterization of canonicity (`layerreg1_part2`). It has no statement that every code occurs coherently; this
file proves it for equal parent layers `q = q' ≤ p`, using the frame of `P4Frame`:

* `constLayered G q`: the constant layering;
* `chainPairLayers_of_const`, `layerPattern_of_const`: a layering that is constant on the nodes of an embedded code
  carries the `layerreg1` pattern;
* `cframe_canon`: the frame of the constant decoded couple carries the pattern, hence is canonical;
* **`coherentCouple_exists`**: `IsCoherentCoupleAt p q q Q (constLayered (decodedCouple Q) q)` for `Q.wf`, `q ≤ p`;
* **`coherentTree_exists`**: `IsCoherentTreeAt p q q X (constLayered (decodedTree X 1) q)` for `X.wf`, `q ≤ p`.
  The ambient garden is the frame of the couple `closeCpl X = type2 X nil triv`.

Together with `P4Decode` (uniqueness), each well-formed code has exactly one coherent carrier at `(p, q, q)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The constant layering of a garden. -/
def constLayered {w : ℕ} (G : Garden w) (q : ℕ) : LayeredGarden w :=
  ⟨G, fun _ => q, fun _ _ => le_rfl, fun _ => rfl⟩

theorem layerAt_constLayered {w : ℕ} (G : Garden w) (q : ℕ) {z : Fin w × Path}
    (hz : z.2 ∈ (G.tree z.1).nodes) : layerAt (constLayered G q) z = q :=
  layerAt_node (constLayered G q) ⟨z, hz⟩

section Const

variable {w : ℕ} {LG : LayeredGarden w} {c : ℕ}

theorem cohOn_of_const {L : List ((Fin w × Path) × (Fin w × Path))}
    (h : ∀ z ∈ pairEndpoints L, layerAt LG z = c) : CohOn LG L := fun l hl =>
  (h l.1 ((mem_pairEndpoints_iff L _).2 ⟨l, hl, Or.inl rfl⟩)).trans
    (h l.2 ((mem_pairEndpoints_iff L _).2 ⟨l, hl, Or.inr rfl⟩)).symm

/-- A layering constant on the nodes of a chain carries `ChainPairLayers`. -/
theorem chainPairLayers_of_const : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    (∀ z ∈ chainNodesSet X ζ a, layerAt LG z = c) → ChainPairLayers LG X ζ a
  | .nil, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, h => by
    have ha := h a (Links.root_mem_chainNodesSet _ _ _ _ _ _ _)
    exact ⟨(h _ (mem_chainNodesSet_innerLone _ _ _ _ _ _ _)).trans ha.symm,
      fun z hz => (h z (mem_chainNodesSet_red hz)).trans ha.symm,
      fun z hz => (h z (mem_chainNodesSet_green hz)).trans ha.symm,
      chainPairLayers_of_const inner _ _ fun z hz => h z (mem_chainNodesSet_inner hz),
      chainPairLayers_of_const rest _ _ fun z hz => h z (mem_chainNodesSet_rest hz)⟩

/-- **A layering constant on the nodes of an embedded couple, with both parent layers equal to that constant,
carries the `layerreg1` pattern.** -/
theorem layerPattern_of_const {p : ℕ} {Q : RegCpl} {a b : Fin w × Path}
    (h : ∀ z ∈ cplNodes Q a b, layerAt LG z = c) (ha : parAt LG p a = c) (hb : parAt LG p b = c) :
    LayerPattern LG p Q a b := by
  have hm : c = min (parAt LG p a) (parAt LG p b) := by rw [ha, hb, min_self]
  have hcoh : CohOn LG (Q.linksAt a b) := cohOn_of_const fun z hz => h z (Finset.mem_union_left _ hz)
  cases Q with
  | triv => exact ⟨hcoh, fun z hz => (h z hz).trans hm⟩
  | type1 c' Q₁ Q₂ Q₃ => exact ⟨hcoh, fun z hz => (h z hz).trans hm⟩
  | type2 Xp Xm Qlp =>
    have h1 : ∀ z ∈ chainNodesSet Xp 1 a, layerAt LG z = c :=
      fun z hz => h z (mem_cplNodes_type2.2 (Or.inl hz))
    have h2 : ∀ z ∈ chainNodesSet Xm (-1) b, layerAt LG z = c :=
      fun z hz => h z (mem_cplNodes_type2.2 (Or.inr (Or.inl hz)))
    refine ⟨hcoh, fun z hz => (h z (mem_cplNodes_type2.2 (Or.inr (Or.inr hz)))).trans hm,
      chainPairLayers_of_const Xp 1 a h1, chainPairLayers_of_const Xm (-1) b h2,
      fun z hz => ?_, fun z hz => ?_⟩
    · rw [h1 z hz, ← hm, ha]
      exact ⟨le_rfl, le_rfl⟩
    · rw [h2 z hz, ← hm, hb]
      exact ⟨le_rfl, le_rfl⟩

end Const

section Frame

variable (Q : RegCpl) {p q : ℕ} (hqp : q ≤ p)

theorem const_root_le (j : Fin 2) : layerAt (constLayered (decodedCouple Q) q) (j, []) ≤ q :=
  (layerAt_constLayered _ q (TTree.nil_mem_nodes _)).le

/-- **The frame of the constant decoded couple** (parent layers `q = q'`). -/
noncomputable abbrev cframe : LayeredGarden 2 :=
  frameLayered (LQ := constLayered (decodedCouple Q) q) (decodedCouple_decodes Q) le_rfl hqp
    (const_root_le Q 0) (const_root_le Q 1)

theorem cframe_iota (z : Fin 2 × Path) :
    layerAt (cframe Q hqp) (frameIota z) = layerAt (constLayered (decodedCouple Q) q) z :=
  layerAt_frame_iota _ _ _ _ _ z

theorem cframe_layer (z : Fin 2 × Path) (hz : z ∈ cplNodes Q fA fB) : layerAt (cframe Q hqp) z = q := by
  rw [← frameIota_zero, ← frameIota_one, cplNodes_map Q frameIota frameIota_hom] at hz
  obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
  rw [cframe_iota]
  exact layerAt_constLayered _ q ((Embeds.of_decodes (decodedCouple_decodes Q)).mem_nodes hz')

theorem cframe_pattern : LayerPattern (cframe Q hqp) p Q fA fB :=
  layerPattern_of_const (cframe_layer Q hqp) (frame_parAt_fA _ _ _ _ _) (frame_parAt_fB _ _ _ _ _)

theorem cframe_canon : IsCanonGC (p + 1) (cframe Q hqp) := frame_canon _ _ _ _ _ (cframe_pattern Q hqp)

include hqp in
/-- **Existence of the coherent couple carrier at `(p, q, q)`.** -/
theorem coherentCouple_exists (hwf : Q.wf = true) :
    IsCoherentCoupleAt p q q Q (constLayered (decodedCouple Q) q) := by
  refine ⟨hwf, decodedCouple_decodes Q, 2, cframe Q hqp, fA, fB, cframe_canon Q hqp, frame_embeds Q,
    nodeSign_fA, nodeSign_fB, (cframe_pattern Q hqp).1, frame_parAt_fA _ _ _ _ _, frame_parAt_fB _ _ _ _ _, ?_⟩
  rintro ⟨⟨j, path⟩, hz⟩
  have e : addrExt (if j = 0 then fA else fB) path = frameIota (j, path) := by
    fin_cases j <;> rfl
  show q = layerAt (cframe Q hqp) (addrExt (if j = 0 then fA else fB) path)
  rw [e, cframe_iota]
  exact (layerAt_constLayered _ q hz).symm

end Frame

/-- The couple closing a chain: the chain on the `+` side, the trivial chain on the `-` side. -/
def closeCpl (X : RegChain) : RegCpl := .type2 X .nil .triv

/-- **Existence of the coherent tree carrier at `(p, q, q)`** (root sign `+`). -/
theorem coherentTree_exists (X : RegChain) {p q : ℕ} (hqp : q ≤ p) (hwf : X.wf = true) :
    IsCoherentTreeAt p q q X (constLayered (decodedTree X 1) q) := by
  have hE := (frame_embeds (closeCpl X)).type2
  have hcoh : CohOn (cframe (closeCpl X) hqp) (X.linksAt 1 fA) := fun l hl =>
    (cframe_pattern (closeCpl X) hqp).1 l (List.mem_append_left _ (List.mem_append_left _ hl))
  have h0 : ((decodedCouple (closeCpl X)).tree 0) = X.plug 1 .leaf :=
    (decodedCouple_decodes (closeCpl X)).2.1
  refine ⟨hwf, decodedTree_decodes X 1, 2, cframe (closeCpl X) hqp, fA, .leaf, cframe_canon _ hqp, hE.1,
    nodeSign_fA, hcoh, frame_parAt_fA _ _ _ _ _, ?_, ?_⟩
  · show layerAt (cframe (closeCpl X) hqp) (frameIota ((0 : Fin 2), X.lonePath)) = q
    rw [cframe_iota]
    apply layerAt_constLayered
    show X.lonePath ∈ ((decodedCouple (closeCpl X)).tree 0).nodes
    rw [h0]
    exact lonePath_mem_plug X 1 _
  · rintro ⟨⟨j, path⟩, hz⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show q = layerAt (cframe (closeCpl X) hqp) (frameIota ((0 : Fin 2), path))
    rw [cframe_iota]
    refine (layerAt_constLayered _ q ?_).symm
    show path ∈ ((decodedCouple (closeCpl X)).tree 0).nodes
    have h2 : path ∈ ((decodedTree X 1).tree 0).nodes := hz
    rw [(decodedTree_decodes X 1).1] at h2
    rw [h0]
    exact h2

end WaveTurbulence.PL234
