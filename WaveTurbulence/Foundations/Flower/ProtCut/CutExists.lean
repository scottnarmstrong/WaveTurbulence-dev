/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutBook

/-! # D2c PROT-CUT: the pieces of the terminal cut exist

`CutTermData.exists_of_wf`: a well-formed code `X = appendChain Xp (pair m Qr Qg inner nil)` decoding a layered
paired tree `LG` has its four pieces as layered gardens with the layers of `LG` (`CutTermData`). The gardens come from
main's decoding existence (`Reg.wf_chain_exists_regular_decodesTree`, `Reg.wf_code_exists_regular_decodes`), the
layers are pulled back along the placements (`isLayering_pullback`); paired leaves keep their layers because the
pieces' leaf pairs are leaf pairs of `X` (`chain_pairsAt_map`, `couple_pairsAt_map`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- A layering pulled back along an address map that sends branching nodes to branching nodes. -/
theorem isLayering_pullback {w' : ℕ} (LG : LayeredGarden 1) (G' : Garden w')
    (φ : Fin w' × Path → Fin 1 × Path) (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hb : ∀ x : GBranch G'.tree, (φ x.1).2 ∈ (LG.garden.tree (φ x.1).1).branching)
    (hpair : ∀ ℓ : GLeaf G'.tree, layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1)) :
    IsLayering G' (fun z => layerAt LG (φ z.1)) := by
  refine ⟨fun b i => ?_, hpair⟩
  let B : GBranch LG.garden.tree := ⟨φ b.1, hb b⟩
  have h := LG.isLayering.1 B i
  have e1 : layerAt LG (φ (b.child i).1) = LG.layer (B.child i) := by
    rw [← layerAt_node]
    exact congrArg (layerAt LG) (hφ b.1 [i])
  have e2 : layerAt LG (φ b.toNode.1) = LG.layer B.toNode := layerAt_node LG B.toNode
  show layerAt LG (φ (b.child i).1) ≤ layerAt LG (φ b.toNode.1)
  rw [e1, e2]
  exact h

/-- Leaf pairs of a decoded paired-tree piece keep their layers. -/
theorem pair_layer_tree (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden) {G' : Garden 1}
    {C : RegChain} (hC : C.DecodesTree G') (φ : Fin 1 × Path → Fin 1 × Path)
    (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hsub : ∀ p ∈ C.pairsAt (G'.sig 0) (φ ((0 : Fin 1), [])), p ∈ X.pairsAt (LG.garden.sig 0) ((0 : Fin 1), []))
    (ℓ : GLeaf G'.tree) : layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1) := by
  by_cases hl : ℓ.1.2 = C.lonePath
  · have hm : G'.mark ℓ ≠ none := by rw [hC.2.1 ℓ]; simp [hl]
    rw [(G'.pair_eq_iff ℓ).2 hm]
  · have hm := hC.2.2 ℓ hl
    rw [mem_symmPairs] at hm
    have key : ∀ u v : Fin 1 × Path, (u, v) ∈ C.pairsAt (G'.sig 0) ((0 : Fin 1), []) →
        layerAt LG (φ u) = layerAt LG (φ v) := by
      intro u v huv
      refine layer_eq_of_decoded_treePair hX (p := (φ u, φ v)) (hsub _ ?_)
      rw [chain_pairsAt_map C φ hφ]
      exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
    rcases hm with hm | hm
    · exact key _ _ hm
    · exact (key _ _ hm).symm

/-- Leaf pairs of a decoded couple piece keep their layers. -/
theorem pair_layer_couple (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden) {G' : Garden 2}
    {Q : RegCpl} (hQ : Q.Decodes G') (φ : Fin 2 × Path → Fin 1 × Path)
    (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hsub : ∀ p ∈ Q.pairsAt (φ ((0 : Fin 2), [])) (φ ((1 : Fin 2), [])),
      p ∈ X.pairsAt (LG.garden.sig 0) ((0 : Fin 1), []))
    (ℓ : GLeaf G'.tree) : layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1) := by
  have hm := hQ.2.2.2 ℓ
  rw [mem_symmPairs] at hm
  have key : ∀ u v : Fin 2 × Path, (u, v) ∈ Q.raw.2 → layerAt LG (φ u) = layerAt LG (φ v) := by
    intro u v huv
    refine layer_eq_of_decoded_treePair hX (p := (φ u, φ v)) (hsub _ ?_)
    rw [couple_pairsAt_map Q φ hφ]
    exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
  rcases hm with hm | hm
  · exact key _ _ hm
  · exact (key _ _ hm).symm

theorem glue_ofSum_inr_path {LG : LayeredGarden 1} {Gp GZ : Garden 1} {Xp : RegChain}
    (gd : GlueData LG.garden Gp GZ Xp) (y : GBranch GZ.tree) :
    (gd.ofSum (.inr y)).1 = ((0 : Fin 1), Xp.lonePath ++ y.1.2) := by
  obtain ⟨⟨j, p⟩, _⟩ := y
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show botAddr Xp.lonePath ((0 : Fin 1), p) = _
  simp [botAddr]

/-- **The pieces of the terminal cut exist.** -/
theorem CutTermData.exists_of_wf (LG : LayeredGarden 1) (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner : RegChain) (hX : (appendChain Xp (cpair m Qr Qg inner)).DecodesTree LG.garden)
    (hwf : (appendChain Xp (cpair m Qr Qg inner)).wf = true) :
    ∃ (LGp LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2),
      CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg := by
  set ζ := LG.garden.sig 0
  rw [appendChain_wf, Bool.and_eq_true] at hwf
  obtain ⟨hwp, hwZ⟩ := hwf
  have hwZ' := hwZ
  simp only [cpair, RegChain.wf, Bool.and_eq_true] at hwZ'
  obtain ⟨⟨⟨hwr, hwg⟩, hwi⟩, -⟩ := hwZ'
  obtain ⟨Gp, hsp, hdp, -⟩ := Reg.wf_chain_exists_regular_decodesTree Xp hwp ζ
  obtain ⟨GZ, hsZ, hdZ, -⟩ := Reg.wf_chain_exists_regular_decodesTree _ hwZ ζ
  obtain ⟨Gi, hsi, hdi, -⟩ := Reg.wf_chain_exists_regular_decodesTree inner hwi (slotSign ζ m.c)
  obtain ⟨Gr, hdr, -⟩ := Reg.wf_code_exists_regular_decodes Qr hwr
  obtain ⟨Gg, hdg, -⟩ := Reg.wf_code_exists_regular_decodes Qg hwg
  have gd : GlueData LG.garden Gp GZ Xp := glueData_tree hX hdp hsp hdZ hsZ
  have hp : PairData m Qr Qg inner GZ Gi Gr Gg := ⟨hdZ, hdi, by rw [hsi, hsZ], hdr, hdg⟩
  -- the placements
  let φp : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), x.2)
  let φi : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ m.c :: x.2)
  let φr : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ (rBase m inner ζ x.1 ++ x.2))
  let φg : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ (gBase m inner ζ x.1 ++ x.2))
  have hφp : ∀ x q, φp (addrExt x q) = addrExt (φp x) q := by intro x q; simp [φp, addrExt]
  have hφi : ∀ x q, φi (addrExt x q) = addrExt (φi x) q := by intro x q; simp [φi, addrExt]
  have hφr : ∀ x q, φr (addrExt x q) = addrExt (φr x) q := by intro x q; simp [φr, addrExt]
  have hφg : ∀ x q, φg (addrExt x q) = addrExt (φg x) q := by intro x q; simp [φg, addrExt]
  -- the pairs of X
  have hXpairs : (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) =
      Xp.pairsAt ζ ((0 : Fin 1), []) ++ (cpair m Qr Qg inner).pairsAt ζ ((0 : Fin 1), Xp.lonePath) := by
    rw [appendChain_pairsAt]; simp [addrExt]
  have hZpairs : ∀ p ∈ (cpair m Qr Qg inner).pairsAt ζ ((0 : Fin 1), Xp.lonePath),
      p ∈ (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    rw [hXpairs]; exact List.mem_append_right _ hp'
  -- branch placements
  have bP : ∀ x : GBranch Gp.tree, (φp x.1).2 ∈ (LG.garden.tree (φp x.1).1).branching :=
    fun x => (gd.ofSum (.inl x)).2
  have bI : ∀ x : GBranch Gi.tree, (φi x.1).2 ∈ (LG.garden.tree (φi x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inr (hp.βi x))).2
    rw [glue_ofSum_inr_path gd] at h
    exact h
  have bR : ∀ x : GBranch Gr.tree, (φr x.1).2 ∈ (LG.garden.tree (φr x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inr (hp.βr x))).2
    rw [glue_ofSum_inr_path gd] at h
    simpa [PairData.βr, hsZ, φr] using h
  have bG : ∀ x : GBranch Gg.tree, (φg x.1).2 ∈ (LG.garden.tree (φg x.1).1).branching := by
    intro x
    have h := (gd.ofSum (.inr (hp.βg x))).2
    rw [glue_ofSum_inr_path gd] at h
    simpa [PairData.βg, hsZ, φg] using h
  -- pair inclusions
  have sP : ∀ p ∈ Xp.pairsAt (Gp.sig 0) (φp ((0 : Fin 1), [])),
      p ∈ (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    rw [hXpairs]
    rw [hsp] at hp'
    exact List.mem_append_left _ (by simpa [φp] using hp')
  have sI : ∀ p ∈ inner.pairsAt (Gi.sig 0) (φi ((0 : Fin 1), [])),
      p ∈ (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; right
    rw [hsi] at hp'
    simpa [φi, addrExt] using hp'
  have sR : ∀ p ∈ Qr.pairsAt (φr ((0 : Fin 2), [])) (φr ((1 : Fin 2), [])),
      p ∈ (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; left; left
    by_cases hs : slotSign ζ m.red.1 = 1 <;> simpa [φr, rBase, hs, addrExt, bPath] using hp'
  have sG : ∀ p ∈ Qg.pairsAt (φg ((0 : Fin 2), [])) (φg ((1 : Fin 2), [])),
      p ∈ (appendChain Xp (cpair m Qr Qg inner)).pairsAt ζ ((0 : Fin 1), []) := fun p hp' => by
    refine hZpairs p ?_
    simp only [cpair, RegChain.pairsAt, List.mem_append]
    left; left; right
    by_cases hs : slotSign ζ m.green.1 = 1 <;> simpa [φg, gBase, hs, addrExt, bPath] using hp'
  refine ⟨⟨Gp, fun z => layerAt LG (φp z.1),
      isLayering_pullback LG Gp φp hφp bP (pair_layer_tree LG hX hdp φp hφp sP)⟩,
    ⟨Gi, fun z => layerAt LG (φi z.1),
      isLayering_pullback LG Gi φi hφi bI (pair_layer_tree LG hX hdi φi hφi sI)⟩,
    ⟨Gr, fun z => layerAt LG (φr z.1),
      isLayering_pullback LG Gr φr hφr bR (pair_layer_couple LG hX hdr φr hφr sR)⟩,
    ⟨Gg, fun z => layerAt LG (φg z.1),
      isLayering_pullback LG Gg φg hφg bG (pair_layer_couple LG hX hdg φg hφg sG)⟩,
    ⟨hX, hwZ, hdp, hsp, hdi, hsi, hdr, hdg, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

end WaveTurbulence.Flower.ProtCut
