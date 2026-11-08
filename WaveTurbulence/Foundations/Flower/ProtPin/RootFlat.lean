/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPieces
public import WaveTurbulence.Foundations.Flower.ProtPin.CutFlat
public import WaveTurbulence.Foundations.Flower.ProtPin.None

/-! # D3 PROT-PIN: flatness at the root cut; the suffix gate

* `root_flat`: the suffix inherits the canonical ambient (`TreeAmb p rest LGs`, main's `chainEmb_append_right`), and
  the coherent pieces of the closing pair are flat in layer `p` (as `cut_flat`, with main's `ChainEmb.parts` at the root).
* `suffix_piece_star`: a protected sub-shape `Y` (any lone layer) at one output on `timeBoxGt p p`: its lone leaf is
  relayered to `p` (`loneLayer`; kernels read branch layers only) and `tree_piece_star` applies (a coherent shape is flat
  off its lone leaf, `flat_tree_whole`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain}

/-- **The root cut is flat in the ambient.** -/
theorem root_flat (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {p : ℕ}
    (hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG) (hA : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG) :
    TreeAmb p rest LGs ∧
    (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 → ∀ z, LGi.layer z = p) ∧
    (LGr.incoherency Qr.links = 0 → ∀ z, LGr.layer z = p) ∧
    (LGg.incoherency Qg.links = 0 → ∀ z, LGg.layer z = p) := by
  obtain ⟨w', H, a, h, hcan, hC, hlay⟩ := hA
  have hch := hsh.2.2.2
  obtain ⟨-, hli, hlonei, -, -⟩ := root_layers D hsh
  obtain ⟨-, hwfi, hwfr, hwfg⟩ := root_wf hsh.1
  -- the pieces in the object and in the ambient
  have hCL := ChainEmb.of_decodesTree D.dec
  obtain ⟨hrL, hgL, hiL, -⟩ := hCL.parts
  obtain ⟨hr, hg, hi, -⟩ := hC.parts
  have ha0 : addrExt a ([] : TTree.Path) = a := by simp [addrExt]
  have hstem := stem_layer D.dec hch hlay
  have hlp := root_lonePath m Qr Qg inner rest
  have hxa : layerAt H (addrExt a ([] : TTree.Path)) = p :=
    hstem [] List.nil_prefix (by rw [hlp]; simp [bPath])
  have hxb : layerAt H (addrExt a ([] ++ ([m.c] ++ inner.lonePath))) = p :=
    hstem _ (by rw [hlp]; exact ⟨[m.lone] ++ rest.lonePath, by simp [bPath]⟩) (by rw [hlp]; simp [bPath])
  refine ⟨?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · -- the suffix ambient
    have hCs := PL234.chainEmb_append_right (B := cpair m Qr Qg inner) (D := rest) hC
    refine ⟨w', H, addrExt a (cpair m Qr Qg inner).lonePath, h, hcan, by rw [D.sigS]; exact hCs, fun z => ?_⟩
    rw [D.layS z]
    have hm : (((0 : Fin 1), lonePos m inner ++ z.1.2) : Fin 1 × TTree.Path) = (D.gd.ι₂ z).1 := by
      have hj : z.1.1 = 0 := Subsingleton.elim _ _
      simp [GlueData.ι₂, botAddr, hj, cpair_lonePath]
    rw [hm, Links.layerAt_node, hlay (D.gd.ι₂ z)]
    have hj : z.1.1 = 0 := Subsingleton.elim _ _
    simp [GlueData.ι₂, botAddr, hj, addrExt, cpair_lonePath]
  · -- the interior chain
    exact flat_tree_sub hcan hlay hwfi D.decI (r := ((0 : Fin 1), [m.c])) (by rw [D.sigI]; exact hiL)
      (by rw [D.sigI]; exact hi) (by simp [addrExt]) (fun z => by rw [D.layI z]; simp [addrExt]) hli hlonei h0
  · -- the red side couple
    exact side_flat hcan hlay hwfr D.decR [] ([m.c] ++ inner.lonePath) m.red.1 m.red.2
      (slotSign (LG.garden.sig 0) m.red.1) (rBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [rBase, hs, bPath], by simp [rBase, hs]⟩) hrL (by rw [ha0]; exact hr)
      (fun z => by rw [D.layR z]; rfl) hxa hxb h0
  · -- the green side couple
    exact side_flat hcan hlay hwfg D.decG [] ([m.c] ++ inner.lonePath) m.green.1 m.green.2
      (slotSign (LG.garden.sig 0) m.green.1) (gBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [gBase, hs, bPath], by simp [gBase, hs]⟩) hgL (by rw [ha0]; exact hg)
      (fun z => by rw [D.layG z]; rfl) hxa hxb h0

/-! ### The suffix gate -/

/-- Leaf layers with the lone leaf moved to `p`. -/
def loneLayer (LG : LayeredGarden 1) (X : RegChain) (p : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = X.lonePath then p else LG.layer a

theorem isLayering_lone {p : ℕ} {X : RegChain} {LG : LayeredGarden 1} (h : ProtShape p X LG) :
    IsLayering LG.garden (relayerFun LG (loneLayer LG X p)) := by
  obtain ⟨-, hX, -, hch⟩ := h
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · have hb : relayerFun LG (loneLayer LG X p) b.toNode = LG.layer b.toNode := if_pos b.2
    rw [hb]
    unfold relayerFun loneLayer
    split_ifs with hc hl
    · exact LG.isLayering.1 b i
    · have hpre : b.1.2 <+: X.lonePath := ⟨[i], hl⟩
      have hne : b.1.2 ≠ X.lonePath := by
        intro he
        have := congrArg List.length hl
        change (b.1.2 ++ [i]).length = X.lonePath.length at this
        rw [he] at this
        simp at this
      rw [hch b (Nat.lt_one_iff.mp b.1.1.isLt) hpre hne]
    · exact LG.isLayering.1 b i
  · have h1 := not_mem_branching_of_leaf ℓ
    have h2 := not_mem_branching_of_leaf (LG.garden.pair ℓ)
    unfold relayerFun loneLayer
    rw [if_neg h1, if_neg h2]
    have hp := Links.tree_pair_eq_iff hX ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · rw [hp.2 hl]
    · have hpl : (LG.garden.pair ℓ).1.2 ≠ X.lonePath := by
        intro h'
        have hfix : LG.garden.pair (LG.garden.pair ℓ) = LG.garden.pair ℓ := (Links.tree_pair_eq_iff hX _).2 h'
        have hfix' : ℓ = LG.garden.pair ℓ := (LG.garden.pair_pair ℓ).symm.trans hfix
        exact hl ((congrArg (fun x : GLeaf LG.garden.tree => x.1.2) hfix').trans h')
      change (if ℓ.1.2 = X.lonePath then p else LG.layer ℓ.toNode) =
        (if (LG.garden.pair ℓ).1.2 = X.lonePath then p else LG.layer (LG.garden.pair ℓ).toNode)
      rw [if_neg hl, if_neg hpl]
      exact LG.isLayering.2 ℓ

/-- **A protected sub-shape at one output** (any lone layer), with star weights and filters. -/
theorem suffix_piece_star {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {θ c' : ℝ} (hθc : PieceLoss P θ c')
    (Y : RegChain) (LGt : LayeredGarden 1) (hsh : ProtShape p Y LGt) (hsz : Y.size = 2 * n)
    (hamb : TreeAmb p Y LGt)
    (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGt.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (hHt : LeafwiseControlled LGt Ht Bt)
    (k' : Mom P.d) :
    rn θ (timeBoxGt p p) (fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => x 0) (x 1) k'
        (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c') *
        regBound P n (LGt.incoherency (Y.treeLinks (LGt.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LGt Bt) := by
  have hf := isLayering_lone hsh
  set LG' := relayer LGt (loneLayer LGt Y p) hf with hLG'
  have hdec := hsh.2.1
  -- the kernel does not see leaf layers
  have hker : ∀ x : Fin 2 → ℝ,
      Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG' Ht (fun _ => x 0) (x 1) k' (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ) =
        Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGt Ht (fun _ => x 0) (x 1) k' (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ) := fun x => by
    rw [← cut_kernel_tree_m _ _ _ LG' (Y := Y) hdec, ← cut_kernel_tree_m _ _ _ LGt hdec]
    exact kernelProt_relayer LGt (loneLayer LGt Y p) hf _ _ _ _ _ _ _ _ _ _ _
  rw [← funext hker, ← incoherency_relayer LGt (loneLayer LGt Y p) hf]
  have hlay' : ∀ z : GNode LGt.garden.tree, LG'.layer z = loneLayer LGt Y p z ∨
      (z.1.2 ∈ (LGt.garden.tree z.1.1).branching ∧ LG'.layer z = LGt.layer z) := fun z => by
    by_cases hb : z.1.2 ∈ (LGt.garden.tree z.1.1).branching
    · exact Or.inr ⟨hb, if_pos hb⟩
    · exact Or.inl (if_neg hb)
  have hle : ∀ a, LG'.layer a ≤ p := fun a => by
    rcases hlay' a with h | ⟨-, h⟩ <;> rw [h]
    · unfold loneLayer; split_ifs
      · exact le_rfl
      · exact hsh.2.2.1 a
    · exact hsh.2.2.1 a
  have hlone : ∀ a : GNode LG'.garden.tree, a.1.2 = Y.lonePath → LG'.layer a = p := fun a ha => by
    have hnb : a.1.2 ∉ (LGt.garden.tree a.1.1).branching := by
      rw [ha, show a.1.1 = 0 from Subsingleton.elim _ _]
      exact TTree.not_mem_branching_of_mem_leaves _ (Links.lone_mem_leaves hdec)
    change relayerFun LGt (loneLayer LGt Y p) a = p
    unfold relayerFun loneLayer
    rw [if_neg hnb, if_pos ha]
  have hflat : LG'.incoherency (Y.treeLinks (LG'.garden.sig 0)) = 0 → ∀ a, LG'.layer a = p := fun h0 a => by
    rw [incoherency_relayer] at h0
    obtain ⟨w', H, b, t, hcan, hC, hl⟩ := hamb
    have hfl := flat_tree_whole hcan hsh.1 hdec hC hl hsh.2.2.2 h0
    by_cases ha : a.1.2 = Y.lonePath
    · exact hlone a ha
    · rcases hlay' a with h | ⟨-, h⟩ <;> rw [h]
      · unfold loneLayer; rw [if_neg ha]; exact hfl a ha
      · exact hfl a ha
  exact tree_piece_star K hp hn hθc Y LG' hsh.1 hsz hdec hle hlone hflat S ω cω hpres F M hM Fu Mu hMu Ht Bt hHt k'

end WaveTurbulence.Flower.ProtPin
