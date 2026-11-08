/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.NoneGate
public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnPin

/-! # D6b: the `X^{1/4}` bound of an unpinned protected object with any filter annotations

`noneAnnGate : WTPrefix NoneAnnAt`: an unpinned protected object (paired tree or cap couple, no designated branches)
with star weights and two filter layers whose first layer carries **any** annotation `ann` (a selected `chiD` filter
included) satisfies `‖·‖_{X^{1/4}(timeBoxGt p q')} ≤ ∏ cω · L^{4d} · regBound(protIncoh) · leafSize`, for every
`q' ≤ p`.

Adapted by source from D3's `ProtPin/None.lean` (`none_tree`, `none_cap`, `none_tree_kernel`, `none_cap_kernel`) and
`ProtPin/NoneGate.lean` (`noneAt_of`, `protBoundNoneGate`); see `COPIED-SHA256SUMS`. Changes: the first filter layer
has a general annotation `ann` (both gates accept it), the weight is fixed to `θ = 1/4` with D5's own loss `L^{4d}`
(D3 states the weaker `L^{47d+2}`), the multiplier carries no dagger, and the kernel lemmas are stated for a general
multiplier. Incoherent objects: FILT-GATE (`FiltIncoherentDecayAt`) after relayering the leaves (kernels read branch
layers only; the lone leaf goes to `q'`); coherent objects: D3's flat gate `CohFlatAt` (FiltCoh's single-layer
D5 oracles), via the canonical ambient (`ProtAmbient`, R172). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtPin

/-! ### Unpinned kernels as weighted leafwise kernels -/

/-- An unpinned paired-tree kernel is the weighted leafwise kernel of any leaf relayering. -/
theorem tree_kernel_none (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 1) (X : RegChain) (hX : X.DecodesTree LG.garden)
    (f : GNode LG.garden.tree → ℕ) (hf : IsLayering LG.garden (relayerFun LG f)) (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (ts : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1) (fun _ => none) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW L γ δ (relayer LG f hf) H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 m :=
  (kernelProt_relayer LG f hf L γ δ H m _ _ _ _ _ _).symm.trans
    (kernelProtBridge L γ δ (relayer LG f hf) H m _ _ _ _ _
      (not_flowerParent_of_decodesTree (G := (relayer LG f hf).garden) hX))

/-- An unpinned cap-couple kernel is the weighted couple kernel of any leaf relayering. -/
theorem cap_kernel_none (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 2) (h1 : LG.garden.tree 1 = TTree.leaf)
    (hplain : LG.garden.IsPlain) (f : GNode LG.garden.tree → ℕ) (hf : IsLayering LG.garden (relayerFun LG f))
    (H : LeafProfiles 2 d) (m : (GNode LG.garden.tree → Mom d) → ℂ) (ts : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1) (fun _ => none) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW L γ δ (relayer LG f hf) H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
        (fun _ => 0) 0 m := by
  have hup : (fun _ : GBranch LG.garden.tree => ts 0) = fun b => if b.1.1 = 0 then ts 0 else ts 1 :=
    funext fun b => (if_pos (cap_branch_zero h1 b)).symm
  rw [kernelProt_s_irrel L γ δ LG H m _ (ts 1) 0 _ _ _ _ (not_loneParent_of_isPlain hplain), hup]
  exact (kernelProt_relayer LG f hf L γ δ H m _ _ _ _ _ _).symm.trans
    (kernelProtBridge L γ δ (relayer LG f hf) H m _ _ _ _ _
      (not_flowerParent_of_isPlain (G := (relayer LG f hf).garden) hplain))

/-! ### The statement -/

/-- **The `X^{1/4}` bound of an unpinned protected object**, any annotation on the first filter layer. -/
def NoneAnnAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n → ProtAmbient p X LG → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ),
    (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') Set.univ
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)
        (fun _ => ts 0) (ts 1) (fun _ => none) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (4 * P.d : ℝ)) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

/-! ### Paired trees -/

theorem noneAnn_tree {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {q' : ℕ} (hq' : q' ≤ p)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) :
    XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') Set.univ
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)
        (fun _ => ts 0) (ts 1) (fun _ => none) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (4 * P.d : ℝ)) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
  have hsh' := hsh
  obtain ⟨hwf, hX, hle, hch⟩ := hsh'
  have hsize : X.size = 2 * n := hsz
  have hc0 : (0 : ℝ) ≤ 4 * P.d := by positivity
  by_cases hg : protIncoh X LG = 0
  · -- coherent: flat in the canonical ambient; lone leaf to `q'`, the other leaves to `p`
    obtain ⟨w', Hm, a, h, hcan, hC, hlay⟩ := treeAmb_of_protAmbient hamb
    have hflat0 := flat_tree_whole hcan hwf hX hC hlay hch hg
    have hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p := fun b =>
      hflat0 b.toNode fun he => by
        have hb := b.2
        rw [show b.1.2 = X.lonePath from he, show b.1.1 = 0 from Subsingleton.elim _ _] at hb
        exact TTree.not_mem_branching_of_mem_leaves _ (Links.lone_mem_leaves hX) hb
    have hf := isLayering_flat (q' := q') hX hflat hq'
    rw [XNormRestr_congr (fun ts _ k _ => tree_kernel_none P.L P.γ P.δ LG X hX _ hf H _ ts k)]
    refine ((K.hC p hp n (by rw [N_with]; exact hn) (1 / 4) (by norm_num) le_rfl).2 p q' X hq' hwf hsize
      (relayer LG (flatLeafLayer LG X p q') hf) hX (relayer_flat_layer hX hflat hf)
      S ω cω hpres F ann M hM Fu Mu hMu H B hH).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL hc0 n 0 _ _
  · -- incoherent: FILT-GATE, lone leaf to `q'`, the other leaves to `0`
    set LG' := relayer LG (treeLeafLayer LG X q') (isLayering_tree hsh hq') with hLG'
    have hle' : ∀ a, LG'.layer a ≤ p := relayerFun_le LG _ hle fun a => by
      unfold treeLeafLayer; split_ifs <;> omega
    have hlone : ∀ a : GNode LG'.garden.tree, a.1.2 = X.lonePath → LG'.layer a = q' := fun a ha => by
      have hnb : a.1.2 ∉ (LG.garden.tree a.1.1).branching := by
        rw [ha]
        exact fun h => TTree.not_mem_branching_of_mem_leaves _
          ((Subsingleton.elim (α := Fin 1) a.1.1 0) ▸ Links.lone_mem_leaves hX) h
      rw [relayer_layer_leaf LG _ _ a hnb]
      exact if_pos ha
    have hinc : LG'.incoherency (X.treeLinks (LG'.garden.sig 0)) = protIncoh X LG :=
      incoherency_relayer LG _ _ _
    rw [XNormRestr_congr (fun ts _ k _ => tree_kernel_none P.L P.γ P.δ LG X hX _ (isLayering_tree hsh hq') H _
      ts k)]
    refine ((K.hI p hp n (by rw [N_with]; exact hn) (1 / 4) (4 * P.d) (Or.inr ⟨rfl, rfl⟩)).2 X hwf hsize LG' hX
      hle' p q' hq' le_rfl (hle' _) hlone (by rw [hinc]; omega) S ω cω hpres F ann M hM Fu Mu hMu H B hH).trans ?_
    rw [hinc]
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

/-! ### Cap couples -/

theorem noneAnn_cap {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {q' : ℕ} (hq' : q' ≤ p)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) :
    XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') Set.univ
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)
        (fun _ => ts 0) (ts 1) (fun _ => none) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (4 * P.d : ℝ)) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
  have hsh' := hsh
  obtain ⟨hwf, hdec, h1, hle, -⟩ := hsh'
  have hsize : (RegCpl.type2 X .nil .triv).size = 2 * n := hsz
  have hplain : LG.garden.IsPlain := hdec.1.1
  have hc0 : (0 : ℝ) ≤ 4 * P.d := by positivity
  by_cases hg : protIncoh X LG = 0
  · -- coherent: the paired tree of the cap is flat in the (sign-normalized) ambient; all leaves to `p`
    obtain ⟨LG1, Dc, hsh1, -, hinc1⟩ := ProtCut.cap_pieces hsh
    obtain ⟨w', Hm, a, h, hcan, hC, hlay⟩ := treeAmb_of_cap hamb Dc
    have hflat1 := flat_tree_whole hcan hsh1.1 Dc.dec1 hC hlay hsh1.2.2.2 (hinc1.symm.trans hg)
    have hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p := fun b => by
      have hb0 : b.1.1 = 0 := cap_branch_zero h1 b
      have hbm : b.1.2 ∈ (LG1.garden.tree 0).nodes := by
        have h2 := TTree.branching_subset_nodes _ b.2
        rw [hb0, Dc.tree0] at h2
        rw [Dc.treeT]
        exact h2
      have hbl : b.1.2 ≠ X.lonePath := by
        intro he
        have hb := b.2
        rw [he, hb0, Dc.tree0] at hb
        have hl1 := Links.lone_mem_leaves Dc.dec1
        rw [Dc.treeT] at hl1
        exact TTree.not_mem_branching_of_mem_leaves _ hl1 hb
      have e1 := (Dc.lay ⟨((0 : Fin 1), b.1.2), hbm⟩).symm.trans (hflat1 ⟨((0 : Fin 1), b.1.2), hbm⟩ hbl)
      rw [← Links.layerAt_node LG b.toNode]
      have hbe : b.toNode.1 = ((0 : Fin 2), b.1.2) := Prod.ext hb0 rfl
      rw [hbe]
      exact e1
    have hf := isLayering_const (p := p) hflat
    set Fk : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ
      (relayer LG (fun _ => p) hf) H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ *
        filtWeight Fu (fun _ => false) Mu κ) with hFk
    rw [XNormRestr_congr (fun ts _ k _ => cap_kernel_none P.L P.γ P.δ LG h1 hplain _ hf H _ ts k)]
    refine (XNormRestr_mono_set (fun ts hts => hts.1) subset_rfl _).trans ?_
    refine (VineEstS5C.P2.XNormRestr_mono_idx le_rfl (Nat.zero_le (30 * P.d)) _ _ _).trans ?_
    refine (Regref.XNormRestr_shift_le (1 / 4) (30 * P.d) (30 * P.d) (B := timeBox (p : ℝ) p) (F := Fk) (F' := Fk)
      (fun i => if i = 0 then 0 else (q' : ℝ) - p) (fun ts hts => ?_) (fun ts _ k _ => ?_)).trans ?_
    · obtain ⟨h0, h1'⟩ := hts
      refine ⟨by simpa using h0, ?_⟩
      have e : (ts - fun i : Fin 2 => if i = 0 then (0 : ℝ) else (q' : ℝ) - p) 1 = ts 1 - ((q' : ℝ) - p) := by
        simp
      rw [e, Set.mem_Icc]
      rw [Set.mem_Icc] at h1'
      constructor <;> linarith [h1'.1, h1'.2]
    · have e : (ts - fun i : Fin 2 => if i = 0 then (0 : ℝ) else (q' : ℝ) - p) 0 = ts 0 := by simp
      simp only [hFk, e]
      exact kernelLeavesW_port_irrel (LG := relayer LG (fun _ => p) hf) _ _ _ h1 H _ _ _ _ _
    refine ((K.hC p hp n (by rw [N_with]; exact hn) (1 / 4) (by norm_num) le_rfl).1 p _ hwf hsize
      (relayer LG (fun _ => p) hf) hdec (relayer_const_layer hflat hf) S ω cω hpres F ann M hM Fu Mu hMu H B
      hH).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL hc0 n 0 _ _
  · -- incoherent: FILT-GATE, all leaves to `0`
    set LG' := relayer LG (fun _ => 0) (isLayering_zero LG) with hLG'
    have hle' : ∀ a, LG'.layer a ≤ p := relayerFun_le LG _ hle fun _ => Nat.zero_le _
    have hroot1 : LG'.layer (GNode.root LG'.garden.tree 1) ≤ q' := by
      have hnb : (GNode.root LG.garden.tree 1).1.2 ∉
          (LG.garden.tree (GNode.root LG.garden.tree 1).1.1).branching := by
        change ([] : TTree.Path) ∉ (LG.garden.tree 1).branching
        rw [h1]
        simp [TTree.branching]
      exact (relayer_layer_leaf LG (fun _ => 0) (isLayering_zero LG) _ hnb).trans_le (Nat.zero_le _)
    have hinc : LG'.incoherency (RegCpl.type2 X .nil .triv).links = protIncoh X LG :=
      incoherency_relayer LG _ _ _
    rw [XNormRestr_congr (fun ts _ k _ => cap_kernel_none P.L P.γ P.δ LG h1 hplain _ (isLayering_zero LG) H _
      ts k)]
    refine (XNormRestr_mono_set (fun ts hts => hts.1) subset_rfl _).trans ?_
    refine (VineEstS5C.P2.XNormRestr_mono_idx le_rfl (Nat.zero_le (30 * P.d)) _ _ _).trans ?_
    refine ((K.hI p hp n (by rw [N_with]; exact hn) (1 / 4) (4 * P.d) (Or.inr ⟨rfl, rfl⟩)).1 _ hwf hsize LG' hdec
      hle' p q' le_rfl hq' (hle' _) hroot1 (by rw [hinc]; omega) S ω cω hpres F ann M hM Fu Mu hMu H B hH).trans ?_
    rw [hinc]
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL le_rfl n _ _ _

/-! ### One parameter set, the gate, monotonicity -/

theorem noneAnnAt_of {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) : NoneAnnAt P := by
  intro p hp n hn w LG X hsh hsz hamb q' hq' S ω cω hpres F ann M hM Fu Mu hMu H B hH
  match w, LG, hsh, hamb, S, ω, cω, hpres, F, ann, M, hM, Fu, Mu, hMu, H, B, hH, hsz with
  | 1, LG, hsh, hamb, S, ω, cω, hpres, F, ann, M, hM, Fu, Mu, hMu, H, B, hH, hsz =>
    exact noneAnn_tree K hp hn LG X hsh hsz hamb hq' S ω cω hpres F ann M hM Fu Mu hMu H B hH
  | 2, LG, hsh, hamb, S, ω, cω, hpres, F, ann, M, hM, Fu, Mu, hMu, H, B, hH, hsz =>
    exact noneAnn_cap K hp hn LG X hsh hsz hamb hq' S ω cω hpres F ann M hM Fu Mu hMu H B hH
  | 0, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
  | _ + 3, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim

/-- **The gate** (FILT-GATE and D3's flat coherent gate in prefix form, as `ProtPin.protBoundNoneGate`). -/
theorem noneAnnGate : WTPrefix NoneAnnAt := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  refine ⟨min (min η₁ η₂) (1 / 4), lt_min (lt_min hη₁ hη₂) (by norm_num), fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hη2 : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁a, hC₁a, ν₁, hν₁, HI1⟩ := HI η hη1 φin hφ τs hτs φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, HC1⟩ := HC η hη2 φin hφ τs hτs φ hW
  refine ⟨max C₁a C₁b, le_max_of_le_left hC₁a, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, HI2⟩ := HI1 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, HC2⟩ := HC1 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, -, HI3⟩ := HI2 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, -, L₂, -, HC3⟩ := HC2 δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  refine ⟨1, le_rfl, max (max L₁ L₂) 2, le_max_right _ _, fun L hL => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : (2 : ℝ) ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  exact noneAnnAt_of (⟨HI3 L hL₁, HC3 L hL₂, by linarith, by linarith, le_max_left _ _, le_max_right _ _, hδ.1.le,
    hL1, hη.1.le, hη4, hd⟩ : AlphaConsts ⟨d, γ, η, φin, τs, φ, max C₁a C₁b, ν, δ, D, 1, L⟩ C₁a C₂a C₁b C₂b)

theorem noneAnnAt_mono : LargeConstantMonotone NoneAnnAt := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 a3 q' a4 S ω cω a5 F ann M a6 Fu Mu a7 H B a8
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 a3 q' a4 S ω cω a5 F ann M a6 Fu Mu a7 H B a8).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

end WaveTurbulence.Flower.ProtWhole
