/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarFinal

/-! # D3 PROT-PIN (penTerm): the interior of the terminal cut as a protected sub-object

For `X = Xp ++ pair m Qr Qg inner nil` (pieces `CutTermData`), the interior chain `inner` is itself a protected paired
tree in layer `p` with the same canonical ambient: `pen_protShape_inner` (its chain lies on the chain of `X`),
`pen_treeAmb_inner` (the ambient transported by main's `chainEmb_append_right` and `ChainEmb.parts`, as in
`cut_flat`). A gate-form piece multiplier is a `StarMult` (`pen_starMult_gate`: `starMult_tree` with the trivial
dagger). These let D3's `term` bound (`TermStarPerkU`) act on the interior when its terminal node is pinned ((P5)). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- The lone path of the protected chain at the terminal cut. -/
theorem pen_lonePath (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (m.c :: (inner.lonePath ++ [m.lone])) := by
  rw [appendChain_lonePath, cpair_lonePath]
  simp [lonePos, bPath]

/-- **The interior chain lies on the chain of the object.** -/
theorem pen_chainIn_inner (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (hch : ChainIn p (appendChain Xp (cpair m Qr Qg inner)) LG) : ChainIn p inner LGi := by
  intro b hb0 hpre hne
  have hlp := pen_lonePath Xp m Qr Qg inner
  have hpre' : (D.βI b).1.2 <+: (appendChain Xp (cpair m Qr Qg inner)).lonePath := by
    show Xp.lonePath ++ m.c :: b.1.2 <+: _
    rw [hlp]
    exact (List.prefix_append_right_inj Xp.lonePath).2
      ((List.cons_prefix_cons).2 ⟨rfl, hpre.trans (List.prefix_append _ _)⟩)
  have hne' : (D.βI b).1.2 ≠ (appendChain Xp (cpair m Qr Qg inner)).lonePath := by
    show Xp.lonePath ++ m.c :: b.1.2 ≠ _
    rw [hlp]
    intro h
    have h2 := congrArg List.length h
    have h3 := hpre.length_le
    simp only [List.length_append, List.length_cons, List.length_singleton] at h2
    omega
  have h := hch (D.βI b) rfl hpre' hne'
  rw [← layerAt_node] at h
  rw [D.layI b.toNode]
  exact h

/-- **The interior is a protected paired tree.** -/
theorem pen_protShape_inner (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG) : ProtShape p inner LGi := by
  obtain ⟨-, hwfi, -, -⟩ := cut_wf D hsh.1
  obtain ⟨-, -, hli, -, -, -⟩ := cut_layers D hsh
  exact ⟨hwfi, D.decI, hli, pen_chainIn_inner D hsh.2.2.2⟩

/-- A placed sub-chain inherits the tree ambient. -/
theorem pen_treeAmb_sub {p : ℕ} {w' : ℕ} {H : LayeredGarden w'} (hcan : IsCanonGC (p + 1) H)
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Y : RegChain} {LGt : LayeredGarden 1} (hdec : Y.DecodesTree LGt.garden) {r : Fin 1 × TTree.Path}
    {T : TTree} (hCL : ChainEmb LG.garden Y (LGt.garden.sig 0) r T) {aH : Fin w' × TTree.Path} {h : TTree}
    (hCH : ChainEmb H.garden Y (LGt.garden.sig 0) aH h) (haH : aH = addrExt a r.2)
    (hlayt : ∀ z : GNode LGt.garden.tree, LGt.layer z = layerAt LG (addrExt r z.1.2)) : TreeAmb p Y LGt := by
  subst haH
  refine ⟨_, H, _, h, hcan, hCH, fun z => ?_⟩
  have hm : z.1.2 ∈ (Y.plug (LGt.garden.sig 0) T).nodes := by
    have h2 := z.2
    rw [show z.1.1 = 0 from Subsingleton.elim _ _, hdec.1] at h2
    exact nodes_plug_leaf_sub Y _ T h2
  rw [hlayt z, layerAt_sub hlay hCL.node hCL.tree hm]
  simp only [addrExt, List.append_assoc]

/-- **The interior inherits the tree ambient.** -/
theorem pen_treeAmb_inner (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (hA : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) : TreeAmb p inner LGi := by
  obtain ⟨w', H, a, h, hcan, hC, hlay⟩ := hA
  have hCL := ChainEmb.of_decodesTree D.dec
  have hCLz := PL234.chainEmb_append_right hCL
  obtain ⟨-, -, hiL, -⟩ := hCLz.parts
  have hCz := PL234.chainEmb_append_right hC
  obtain ⟨-, -, hi, -⟩ := hCz.parts
  exact pen_treeAmb_sub hcan hlay D.decI (by rw [D.sigI]; exact hiL) (by rw [D.sigI]; exact hi)
    (by simp [addrExt]) (fun z => by rw [D.layI z]; simp [addrExt])

/-- **A gate-form multiplier is a `StarMult`** (D3's multiplier with the trivial dagger). -/
theorem pen_starMult_gate {d : ℕ} {L : ℝ} {LGt : LayeredGarden 1} {Y : RegChain}
    (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star d → ℂ)
    (c : GNode LGt.garden.tree → ℝ) (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ)
    (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ)
    (hG : GateData L S ω c F M Fu Mu) : StarMult L LGt Y (gateM S ω F M Fu Mu) (starCost S c) := by
  have hind : TermChildIndicator Y (fun _ : GNode LGt.garden.tree → Mom d => (1 : ℝ)) :=
    ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => rfl⟩
  have e : gateM S ω F M Fu Mu = (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
      filtWeight Fu (fun _ => false) Mu κ * (((fun _ : GNode LGt.garden.tree → Mom d => (1 : ℝ)) κ : ℝ) : ℂ)) := by
    funext κ
    simp [gateM]
  rw [e]
  intro Xp' m' Qr' Qg' inner' LGp' LGi' LGr' LGg' D hX
  exact starMult_tree (L := L) (X := Y) S ω c hG.1 F M hG.2.1 Fu Mu hG.2.2 _ hind D hX

end WaveTurbulence.Flower.ProtPin
