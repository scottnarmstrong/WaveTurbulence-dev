/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutBook
public import WaveTurbulence.Foundations.Flower.ProtKer.Bridge
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp
public import WaveTurbulence.Foundations.Spine.PL234Draft.PieceTree

/-! # D3 PROT-PIN, sub-packet D3-PIECES: facts about the (cut-term) pieces

For a protected paired tree `X = appendChain Xp (cpair m Qr Qg inner)` with pieces
`D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg` (D2c, `ProtCut/CutTermTime.lean`):

1. `cut_wf`, `cut_sizes`: the four codes are well formed and have even sizes whose halves add to `n - 1`;
2. `cut_layers`: on a protected object (`ProtShape p X LG`) every piece lies in layers `≤ p`, and the lone leaves'
   parents of the two tree pieces (`𝔫_a` for the prefix, `𝔫_b` for the interior) are in layer `p`;
3. `cut_leafwise`, `cut_leafSize`: the pieces' profiles (`cutHp`, `cutHi`, `cutHr`, `cutHg`) are leafwise controlled
   by the transported bounds (`cutBp`, `cutBi`, `cutBr`, `cutBg`), and the leaf-size product splits over the pieces;
4. `cut_kernel_tree`, `cut_kernel_couple`: with multiplier `1` and no pins the pieces are main's leafwise kernels
   `treeLeaves`, `coupleLeaves`; `cut_cont_tree`, `cut_cont_couple`: those are continuous in their two clocks;
5. `cupR_cases`, `cupG_cases`: one tree of each side couple hangs at `𝔫_a` (clock `u`), the other at `𝔫_b`
   (clock `v`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtPin

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-! ### (1) Well-formedness and sizes -/

theorem cut_wf (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
    (hwf : (appendChain Xp (cpair m Qr Qg inner)).wf = true) :
    Xp.wf = true ∧ inner.wf = true ∧ Qr.wf = true ∧ Qg.wf = true := by
  have hZ := D.wfZ
  rw [appendChain_wf, Bool.and_eq_true] at hwf
  simp only [RegChain.wf, Bool.and_true, Bool.and_eq_true] at hZ
  exact ⟨hwf.1, hZ.2, hZ.1.1, hZ.1.2⟩

theorem cut_sizes {n : ℕ} (hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n) :
    ∃ np ni nr ng : ℕ, Xp.size = 2 * np ∧ inner.size = 2 * ni ∧ Qr.size = 2 * nr ∧ Qg.size = 2 * ng ∧
      np + ni + nr + ng + 1 = n := by
  rw [size_cutTerm] at hsz
  obtain ⟨np, hp⟩ := chain_size_even Xp
  obtain ⟨ni, hi⟩ := chain_size_even inner
  obtain ⟨nr, hr⟩ := code_size_even Qr
  obtain ⟨ng, hg⟩ := code_size_even Qg
  exact ⟨np, ni, nr, ng, by omega, by omega, by omega, by omega, by omega⟩

/-! ### (2) Layers -/

/-- A bound on all layers bounds `layerAt` (which is `0` away from the nodes). -/
theorem layerAt_le_of_forall_layer_le {w : ℕ} {LG : LayeredGarden w} {p : ℕ} (h : ∀ a, LG.layer a ≤ p)
    (x : Fin w × Path) : layerAt LG x ≤ p := by
  unfold layerAt
  split_ifs
  · exact h _
  · exact Nat.zero_le _

theorem cut_layers (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (h : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    (∀ a, LGp.layer a ≤ p) ∧ (∀ a : GNode LGp.garden.tree, a.1.2 = Xp.lonePath → LGp.layer a = p) ∧
    (∀ a, LGi.layer a ≤ p) ∧ (∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = p) ∧
    (∀ a, LGr.layer a ≤ p) ∧ (∀ a, LGg.layer a ≤ p) := by
  have hle := layerAt_le_of_forall_layer_le h.2.2.1
  have hch := h.2.2.2
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  have hlp : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (bPath m inner ++ [m.lone]) := by
    rw [appendChain_lonePath, cpair_lonePath]; rfl
  have layer_of : ∀ (q : Path) (_ : q <+: (appendChain Xp (cpair m Qr Qg inner)).lonePath)
      (_ : q ≠ (appendChain Xp (cpair m Qr Qg inner)).lonePath) (_ : q ∈ (LG.garden.tree 0).branching),
      layerAt LG ((0 : Fin 1), q) = p := by
    intro q hq hne hb
    have := hch ⟨((0 : Fin 1), q), hb⟩ rfl hq hne
    rw [← layerAt_node] at this
    exact this
  have ha : layerAt LG ((0 : Fin 1), Xp.lonePath) = p :=
    layer_of Xp.lonePath (by rw [hlp]; exact List.prefix_append _ _) (by rw [hlp]; simp [bPath])
      (by have := (D.aB hZ hsZ).2; rw [D.aB_path hZ hsZ] at this; exact this)
  have hb : layerAt LG ((0 : Fin 1), Xp.lonePath ++ bPath m inner) = p :=
    layer_of (Xp.lonePath ++ bPath m inner) (by rw [hlp, ← List.append_assoc]; exact List.prefix_append _ _)
      (by rw [hlp]; simp) (by have := (D.bG hZ hsZ).2; rw [D.bG_path hZ hsZ] at this; exact this)
  refine ⟨fun a => (D.layP a).trans_le (hle _), fun a ha' => ?_, fun a => (D.layI a).trans_le (hle _),
    fun a ha' => ?_, fun a => (D.layR a).trans_le (hle _), fun a => (D.layG a).trans_le (hle _)⟩
  · rw [D.layP a, ha']
    exact ha
  · rw [D.layI a, ha']
    simpa [bPath] using hb

/-! ### (3) Leaf bounds -/

/-- The prefix bounds. -/
def cutBp (B : (Fin 1 × TTree.Path) → NNReal) : (Fin 1 × TTree.Path) → NNReal := fun a => B ((0 : Fin 1), a.2)

/-- The interior bounds. -/
def cutBi (Xp : RegChain) (m : MiniTreeCode) (B : (Fin 1 × TTree.Path) → NNReal) : (Fin 1 × TTree.Path) → NNReal :=
  fun a => B ((0 : Fin 1), Xp.lonePath ++ m.c :: a.2)

/-- The red couple bounds. -/
def cutBr (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (B : (Fin 1 × TTree.Path) → NNReal) :
    (Fin 2 × TTree.Path) → NNReal := fun a => B ((0 : Fin 1), Xp.lonePath ++ (rBase m inner ζ a.1 ++ a.2))

/-- The green couple bounds. -/
def cutBg (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (B : (Fin 1 × TTree.Path) → NNReal) :
    (Fin 2 × TTree.Path) → NNReal := fun a => B ((0 : Fin 1), Xp.lonePath ++ (gBase m inner ζ a.1 ++ a.2))

theorem cut_leafwise (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {d : ℕ} {H : LeafProfiles 1 d}
    {B : (Fin 1 × TTree.Path) → NNReal} (hH : LeafwiseControlled LG H B) :
    LeafwiseControlled LGp (cutHp H) (cutBp B) ∧ LeafwiseControlled LGi (cutHi Xp m H) (cutBi Xp m B) ∧
    LeafwiseControlled LGr (cutHr Xp m inner (LG.garden.sig 0) H) (cutBr Xp m inner (LG.garden.sig 0) B) ∧
    LeafwiseControlled LGg (cutHg Xp m inner (LG.garden.sig 0) H) (cutBg Xp m inner (LG.garden.sig 0) B) := by
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofTop D.decP.2.1 (D.hmtop hZ hsZ) ℓ hℓ
    have e : ((0 : Fin 1), ℓ.1.2) = ℓ'.1 := by rw [he]; rfl
    simp only [cutHp, cutBp]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofI ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
    have e : ((0 : Fin 1), Xp.lonePath ++ m.c :: ℓ.1.2) = ℓ'.1 := by
      rw [he, he₁]; simp [botAddr, pφi]
    simp only [cutHi, cutBi]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofR ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
    have e : ((0 : Fin 1), Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2)) = ℓ'.1 := by
      rw [he, he₁]; simp [botAddr, pφr, hsZ]
    simp only [cutHr, cutBr]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofG ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
    have e : ((0 : Fin 1), Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2)) = ℓ'.1 := by
      rw [he, he₁]; simp [botAddr, pφg, hsZ]
    simp only [cutHg, cutBg]
    rw [e]
    exact hH ℓ' hℓ'

theorem cut_leafSize (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) (B : (Fin 1 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = leafSizeProduct LGp (cutBp B) * leafSizeProduct LGi (cutBi Xp m B) *
      leafSizeProduct LGr (cutBr Xp m inner (LG.garden.sig 0) B) *
        leafSizeProduct LGg (cutBg Xp m inner (LG.garden.sig 0) B) := by
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  set f : Fin 1 × Path → ℝ := fun z => (B z : ℝ) with hf
  have e0 : leafSizeProduct LG B = ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := rfl
  rw [e0, (D.gd hZ hsZ).prod_inputLeaves_glue D.decP.2.1 (D.hmtop hZ hsZ) (D.hmbot hZ hsZ) f,
    (D.hp hZ hsZ).prod_inputLeaves_pair (fun z => f (botAddr Xp.lonePath z))]
  have e1 : ∏ ℓ ∈ inputLeaves LGp.garden, f (topAddr ℓ.1) = leafSizeProduct LGp (cutBp B) :=
    Finset.prod_congr rfl fun ℓ _ => rfl
  have e2 : ∏ ℓ ∈ inputLeaves LGi.garden, f (botAddr Xp.lonePath (pφi m ℓ.1)) =
      leafSizeProduct LGi (cutBi Xp m B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, botAddr, pφi, cutBi]
  have e3 : ∏ ℓ ∈ inputLeaves LGr.garden, f (botAddr Xp.lonePath (pφr m inner (GZ.sig 0) ℓ.1)) =
      leafSizeProduct LGr (cutBr Xp m inner (LG.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, botAddr, pφr, cutBr, hsZ]
  have e4 : ∏ ℓ ∈ inputLeaves LGg.garden, f (botAddr Xp.lonePath (pφg m inner (GZ.sig 0) ℓ.1)) =
      leafSizeProduct LGg (cutBg Xp m inner (LG.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, botAddr, pφg, cutBg, hsZ]
  rw [e1, e2, e3, e4]
  ring

/-! ### (4) The pieces with multiplier `1`: main's leafwise kernels, continuous in their clocks -/

theorem not_flowerParent_of_decodesTree_piece {G : Garden 1} {Y : RegChain} (hY : Y.DecodesTree G)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  exact not_flower_of_decodesTree hY ℓ hℓ

theorem kernelLeavesW_one_piece {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl (fun _ => 1) =
      kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold Flower.Stage1W.kernelLeavesW kernelLeaves
  simp only [one_mul]

theorem cut_kernel_tree {d : ℕ} (L γ δ : ℝ) (LGt : LayeredGarden 1) {Y : RegChain} (hY : Y.DecodesTree LGt.garden)
    (Ht : LeafProfiles 1 d) (T u : ℝ) (k : Mom d) :
    kernelProt L γ δ LGt Ht (fun _ => 1) (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 =
      treeLeaves L γ δ LGt Ht T u k := by
  rw [kernelProtBridge L γ δ LGt Ht (fun _ => 1) (fun _ => T) u k (fun _ => 0) 0
    (not_flowerParent_of_decodesTree_piece hY), kernelLeavesW_one_piece]
  rfl

theorem cut_kernel_couple {d : ℕ} (L γ δ : ℝ) (LGc : LayeredGarden 2) {Q : RegCpl} (hQ : Q.Decodes LGc.garden)
    (Hc : LeafProfiles 2 d) (c : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LGc Hc (fun _ => 1) (fun y => c y.1.1) 0 (fun _ => none) k (fun _ => 0) 0 =
      coupleLeaves L γ δ LGc Hc (c 0) (c 1) k := by
  rw [kernelProtBridge L γ δ LGc Hc (fun _ => 1) (fun y => c y.1.1) 0 k (fun _ => 0) 0
    (no_flowerParent_of_plain LGc.garden hQ.1.1), kernelLeavesW_one_piece]
  have hc : ∀ j : Fin 2, c j = if j = 0 then c 0 else c 1 := by
    intro j
    fin_cases j <;> simp
  have hup : (fun y : GBranch LGc.garden.tree => c y.1.1) = fun b => if b.1.1 = 0 then c 0 else c 1 := by
    funext b
    exact hc b.1.1
  rw [hup]
  rfl

/-- Leafwise control gives the coset summability (for `d = 0` the lattice is a point). -/
theorem summable_coset_piece {w d : ℕ} {LG : LayeredGarden w} {H : LeafProfiles w d}
    {B : (Fin w × TTree.Path) → NNReal} (h : LeafwiseControlled LG H B) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)| := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro ℓ _
    exact Summable.of_finite
  · exact h.summable_coset (Nat.succ_le_of_lt hd) hL k

theorem cut_cont_tree {d : ℕ} (L γ δ : ℝ) (hL : 1 ≤ L) (LGt : LayeredGarden 1) {Y : RegChain}
    (hY : Y.DecodesTree LGt.garden) (Ht : LeafProfiles 1 d) (Bt : (Fin 1 × TTree.Path) → NNReal)
    (hHt : LeafwiseControlled LGt Ht Bt) (k : Mom d) :
    Continuous (fun x : Fin 2 → ℝ => treeLeaves L γ δ LGt Ht (x 0) (x 1) k) :=
  PL234.continuous_treeLeaves_time L γ δ LGt Ht (not_flowerParent_of_decodesTree_piece hY)
    (card_lone_le_of_decodesTree hY) k (summable_coset_piece hHt hL k)

theorem cut_cont_couple {d : ℕ} (L γ δ : ℝ) (hL : 1 ≤ L) (LGc : LayeredGarden 2) {Q : RegCpl}
    (hQ : Q.Decodes LGc.garden) (Hc : LeafProfiles 2 d) (Bc : (Fin 2 × TTree.Path) → NNReal)
    (hHc : LeafwiseControlled LGc Hc Bc) (k : Mom d) :
    Continuous (fun x : Fin 2 → ℝ => coupleLeaves L γ δ LGc Hc (x 0) (x 1) k) :=
  continuous_coupleLeaves_time L γ δ Hc LGc hQ.1.1 k (summable_coset_piece hHc hL k)

/-! ### (5) Orientation of the side couples -/

theorem cupR_cases (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    (∀ u v, (cupR m inner ζ u v 0 = u ∧ cupR m inner ζ u v 1 = v)) ∨
    (∀ u v, (cupR m inner ζ u v 0 = v ∧ cupR m inner ζ u v 1 = u)) := by
  by_cases hs : slotSign ζ m.red.1 = 1
  · exact Or.inl fun u v => ⟨cupR_top (by simp [rBase, hs]), cupR_bot (by simp [rBase, hs])⟩
  · exact Or.inr fun u v => ⟨cupR_bot (by simp [rBase, hs]), cupR_top (by simp [rBase, hs])⟩

theorem cupG_cases (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    (∀ u v, (cupG m inner ζ u v 0 = u ∧ cupG m inner ζ u v 1 = v)) ∨
    (∀ u v, (cupG m inner ζ u v 0 = v ∧ cupG m inner ζ u v 1 = u)) := by
  by_cases hs : slotSign ζ m.green.1 = 1
  · exact Or.inl fun u v => ⟨cupG_top (by simp [gBase, hs]), cupG_bot (by simp [gBase, hs])⟩
  · exact Or.inr fun u v => ⟨cupG_bot (by simp [gBase, hs]), cupG_top (by simp [gBase, hs])⟩

/-! ### Exact-type checks (the D3-PIECES brief's statements, verbatim) -/

section Check

example (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
    (hwf : (appendChain Xp (cpair m Qr Qg inner)).wf = true) :
    Xp.wf = true ∧ inner.wf = true ∧ Qr.wf = true ∧ Qg.wf = true := cut_wf D hwf

example {n : ℕ} (hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n) :
    ∃ np ni nr ng : ℕ, Xp.size = 2 * np ∧ inner.size = 2 * ni ∧ Qr.size = 2 * nr ∧ Qg.size = 2 * ng ∧
      np + ni + nr + ng + 1 = n := cut_sizes hsz

example (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (h : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    (∀ a, LGp.layer a ≤ p) ∧ (∀ a : GNode LGp.garden.tree, a.1.2 = Xp.lonePath → LGp.layer a = p) ∧
    (∀ a, LGi.layer a ≤ p) ∧ (∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = p) ∧
    (∀ a, LGr.layer a ≤ p) ∧ (∀ a, LGg.layer a ≤ p) := cut_layers D h

example (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {d : ℕ} {H : LeafProfiles 1 d}
    {B : (Fin 1 × TTree.Path) → NNReal} (hH : LeafwiseControlled LG H B) :
    LeafwiseControlled LGp (cutHp H) (cutBp B) ∧ LeafwiseControlled LGi (cutHi Xp m H) (cutBi Xp m B) ∧
    LeafwiseControlled LGr (cutHr Xp m inner (LG.garden.sig 0) H) (cutBr Xp m inner (LG.garden.sig 0) B) ∧
    LeafwiseControlled LGg (cutHg Xp m inner (LG.garden.sig 0) H) (cutBg Xp m inner (LG.garden.sig 0) B) :=
  cut_leafwise D hH

example (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) (B : (Fin 1 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = leafSizeProduct LGp (cutBp B) * leafSizeProduct LGi (cutBi Xp m B) *
      leafSizeProduct LGr (cutBr Xp m inner (LG.garden.sig 0) B) *
        leafSizeProduct LGg (cutBg Xp m inner (LG.garden.sig 0) B) :=
  cut_leafSize D B

example {d : ℕ} (L γ δ : ℝ) (LGt : LayeredGarden 1) {Y : RegChain} (hY : Y.DecodesTree LGt.garden)
    (Ht : LeafProfiles 1 d) (T u : ℝ) (k : Mom d) :
    kernelProt L γ δ LGt Ht (fun _ => 1) (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 =
      treeLeaves L γ δ LGt Ht T u k :=
  cut_kernel_tree L γ δ LGt hY Ht T u k

example {d : ℕ} (L γ δ : ℝ) (LGc : LayeredGarden 2) {Q : RegCpl} (hQ : Q.Decodes LGc.garden)
    (Hc : LeafProfiles 2 d) (c : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LGc Hc (fun _ => 1) (fun y => c y.1.1) 0 (fun _ => none) k (fun _ => 0) 0 =
      coupleLeaves L γ δ LGc Hc (c 0) (c 1) k :=
  cut_kernel_couple L γ δ LGc hQ Hc c k

example {d : ℕ} (L γ δ : ℝ) (hL : 1 ≤ L) (LGt : LayeredGarden 1) {Y : RegChain}
    (hY : Y.DecodesTree LGt.garden) (Ht : LeafProfiles 1 d) (Bt : (Fin 1 × TTree.Path) → NNReal)
    (hHt : LeafwiseControlled LGt Ht Bt) (k : Mom d) :
    Continuous (fun x : Fin 2 → ℝ => treeLeaves L γ δ LGt Ht (x 0) (x 1) k) :=
  cut_cont_tree L γ δ hL LGt hY Ht Bt hHt k

example {d : ℕ} (L γ δ : ℝ) (hL : 1 ≤ L) (LGc : LayeredGarden 2) {Q : RegCpl}
    (hQ : Q.Decodes LGc.garden) (Hc : LeafProfiles 2 d) (Bc : (Fin 2 × TTree.Path) → NNReal)
    (hHc : LeafwiseControlled LGc Hc Bc) (k : Mom d) :
    Continuous (fun x : Fin 2 → ℝ => coupleLeaves L γ δ LGc Hc (x 0) (x 1) k) :=
  cut_cont_couple L γ δ hL LGc hQ Hc Bc hHc k

example (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    (∀ u v, (cupR m inner ζ u v 0 = u ∧ cupR m inner ζ u v 1 = v)) ∨
    (∀ u v, (cupR m inner ζ u v 0 = v ∧ cupR m inner ζ u v 1 = u)) := cupR_cases m inner ζ

example (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    (∀ u v, (cupG m inner ζ u v 0 = u ∧ cupG m inner ζ u v 1 = v)) ∨
    (∀ u v, (cupG m inner ζ u v 0 = v ∧ cupG m inner ζ u v 1 = u)) := cupG_cases m inner ζ

end Check

end WaveTurbulence.Flower.ProtPin
