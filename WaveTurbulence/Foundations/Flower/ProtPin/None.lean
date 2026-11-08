/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Flat
public import WaveTurbulence.Foundations.Flower.FiltGate.Gate
public import WaveTurbulence.Foundations.IncohInst.Regref.NormShift
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckAlpha

/-! # D3 PROT-PIN, configuration `none` (unfiltered): the gates applied to the whole object

With `cfg = none` the protected kernel is an ordinary leafwise kernel (`KernelProtBridge`); kernels read branch
layers only, so leaves may be relayered.
* `protIncoh ≥ 1`: FILT-GATE at `(p, q')`, the lone leaf of a paired tree relayered to `q'`, the leaves of a cap couple
  to `0`.
* `protIncoh = 0`: the object is flat in its canonical ambient (`flat_tree_whole`; R172 `ProtAmbient`). A paired tree,
  its lone leaf relayered to `q'` and its other leaves to `p`, is a flat-tree carrier of `CohFlatAt` at `(p, q')`. A
  cap couple (ambient normalized to sign `1`, `capAmb_norm`), its leaves relayered to `p`, is a flat couple in layer
  `p`; its kernel does not read the port clock, so the bound on `timeBox p p` moves to `timeBox p q'` by time
  translation (main `XNormRestr_shift_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-! ### Relayering a protected paired tree / cap couple -/

/-- Leaf layers of a protected paired tree: `q'` at the lone leaf, `0` elsewhere. -/
def treeLeafLayer (LG : LayeredGarden 1) (X : RegChain) (q' : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = X.lonePath then q' else 0

theorem isLayering_tree {p q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (h : ProtShape p X LG) (hq' : q' ≤ p) :
    IsLayering LG.garden (relayerFun LG (treeLeafLayer LG X q')) := by
  obtain ⟨-, hX, -, hch⟩ := h
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · have hb : relayerFun LG (treeLeafLayer LG X q') b.toNode = LG.layer b.toNode := if_pos b.2
    rw [hb]
    unfold relayerFun treeLeafLayer
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
      exact hq'
    · exact Nat.zero_le _
  · have h1 := not_mem_branching_of_leaf ℓ
    have h2 := not_mem_branching_of_leaf (LG.garden.pair ℓ)
    unfold relayerFun treeLeafLayer
    rw [if_neg h1, if_neg h2]
    have hp := Links.tree_pair_eq_iff hX ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · rw [hp.2 hl]
    · have hpl : (LG.garden.pair ℓ).1.2 ≠ X.lonePath := by
        intro h'
        have hfix : LG.garden.pair (LG.garden.pair ℓ) = LG.garden.pair ℓ := (Links.tree_pair_eq_iff hX _).2 h'
        have hfix' : ℓ = LG.garden.pair ℓ := (LG.garden.pair_pair ℓ).symm.trans hfix
        exact hl ((congrArg (fun x : GLeaf LG.garden.tree => x.1.2) hfix').trans h')
      change (if ℓ.1.2 = X.lonePath then q' else 0) = (if (LG.garden.pair ℓ).1.2 = X.lonePath then q' else 0)
      rw [if_neg hl, if_neg hpl]

/-- All leaves in layer `0` (any garden). -/
theorem isLayering_zero {w : ℕ} (LG : LayeredGarden w) : IsLayering LG.garden (relayerFun LG fun _ => 0) := by
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · have hb : relayerFun LG (fun _ => 0) b.toNode = LG.layer b.toNode := if_pos b.2
    rw [hb]
    unfold relayerFun
    split_ifs
    · exact LG.isLayering.1 b i
    · exact Nat.zero_le _
  · unfold relayerFun
    rw [if_neg (not_mem_branching_of_leaf ℓ), if_neg (not_mem_branching_of_leaf (LG.garden.pair ℓ))]

theorem relayerFun_le {w p : ℕ} (LG : LayeredGarden w) (f : GNode LG.garden.tree → ℕ) (hle : ∀ a, LG.layer a ≤ p)
    (hf : ∀ a, f a ≤ p) (a : GNode LG.garden.tree) : relayerFun LG f a ≤ p := by
  unfold relayerFun
  split_ifs
  · exact hle a
  · exact hf a

/-! ### The `none` configuration -/

theorem Rdown_with (P : WTParams) (C C' : ℝ) (k : ℕ) :
    ({ P with C₁ := C, C₂ := C' } : WTParams).Rdown k = P.Rdown k := by
  induction k with
  | zero => simp only [WTParams.Rdown]
  | succ k ih => simp only [WTParams.Rdown, ih]

theorem N_with (P : WTParams) (C C' : ℝ) (p : ℕ) : ({ P with C₁ := C, C₂ := C' } : WTParams).N p = P.N p := by
  simp only [WTParams.N, WTParams.R, Rdown_with]

/-- Constants: the gate parameters differ from `P` only in `C₁, C₂`. -/
structure AlphaConsts (P : WTParams) (C₁a C₂a C₁b C₂b : ℝ) : Prop where
  hI : FiltIncoherentDecayAt { P with C₁ := C₁a, C₂ := C₂a }
  hC : CohFlatAt { P with C₁ := C₁b, C₂ := C₂b }
  ha0 : 0 ≤ C₁a
  hb0 : 0 ≤ C₁b
  ha : C₁a ≤ P.C₁
  hb : C₁b ≤ P.C₁
  hδ : 0 ≤ P.δ
  hL : 1 ≤ P.L
  hη0 : 0 ≤ P.η
  hη : P.η ≤ 1 / 4
  hd : 3 ≤ P.d

/-- The weight/loss pairs of D3 contain those of FILT-GATE. -/
theorem gateWeight_of {P : WTParams} {θ c : ℝ}
    (h : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) :
    ∃ c' : ℝ, ((θ = P.η ∧ c' = 0) ∨ (θ = 1 / 4 ∧ c' = 4 * P.d)) ∧ c' ≤ c := by
  rcases h with ⟨hθ, hc⟩ | ⟨hθ, hc⟩
  · exact ⟨0, Or.inl ⟨hθ, rfl⟩, by rw [hc]; positivity⟩
  · refine ⟨4 * P.d, Or.inr ⟨hθ, rfl⟩, ?_⟩
    rw [hc]
    have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
    linarith

theorem theta_range {P : WTParams} {θ c : ℝ} (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 4)
    (h : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) : 0 ≤ θ ∧ θ ≤ 1 / 4 := by
  rcases h with ⟨hθ, -⟩ | ⟨hθ, -⟩ <;> subst hθ
  · exact ⟨hη0, hη⟩
  · norm_num

theorem one_le_Lpow {P : WTParams} (hL : 1 ≤ P.L) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ P.L ^ c :=
  Real.one_le_rpow hL hc

theorem c_nonneg {P : WTParams} {θ c : ℝ}
    (h : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) : 0 ≤ c := by
  rcases h with ⟨-, hc⟩ | ⟨-, hc⟩ <;> subst hc <;> positivity

/-- Final comparison for the `none` cases. -/
theorem none_rhs_le {P : WTParams} {C₁' C₂' : ℝ} (h0 : 0 ≤ C₁') (h : C₁' ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    {c' c : ℝ} (hcc : c' ≤ c) (n g : ℕ) (β : ℝ) :
    ENNReal.ofReal (P.L ^ c') * regBound { P with C₁ := C₁', C₂ := C₂' } n g * ENNReal.ofReal β ≤
      ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal β := by
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL hcc))
    (regBound_mono_C₁ P h0 h hδ (by linarith) n g)) le_rfl

/-- The final comparison with a star product in front. -/
theorem star_rhs_le {P : WTParams} {C₁' C₂' : ℝ} (h0 : 0 ≤ C₁') (h : C₁' ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    {c' c : ℝ} (hcc : c' ≤ c) (n g : ℕ) (β : ℝ) (SP : ℝ≥0∞) :
    SP * ENNReal.ofReal (P.L ^ c') * regBound { P with C₁ := C₁', C₂ := C₂' } n g * ENNReal.ofReal β ≤
      SP * ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal β := by
  have h1 := none_rhs_le (C₂' := C₂') h0 h hδ hL hcc n g β
  calc SP * ENNReal.ofReal (P.L ^ c') * regBound { P with C₁ := C₁', C₂ := C₂' } n g * ENNReal.ofReal β
      = SP * (ENNReal.ofReal (P.L ^ c') * regBound { P with C₁ := C₁', C₂ := C₂' } n g * ENNReal.ofReal β) := by
        ring
    _ ≤ SP * (ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal β) := mul_le_mul' le_rfl h1
    _ = _ := by ring

/-- The same without a loss on the left (coherent bounds). -/
theorem star_rhs_le0 {P : WTParams} {C₁' C₂' : ℝ} (h0 : 0 ≤ C₁') (h : C₁' ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    {c : ℝ} (hc : 0 ≤ c) (n g : ℕ) (β : ℝ) (SP : ℝ≥0∞) :
    SP * regBound { P with C₁ := C₁', C₂ := C₂' } n g * ENNReal.ofReal β ≤
      SP * ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal β := by
  have h1 := star_rhs_le (C₂' := C₂') h0 h hδ hL hc n g β SP
  rwa [Real.rpow_zero, ENNReal.ofReal_one, mul_one] at h1

/-- D3's multiplier with `ind = 1` is the gates' multiplier. -/
theorem mult_ind_one {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F Fu : Finset (GBranch G.tree)) (M Mu : GBranch G.tree → ℝ) (ind : (GNode G.tree → Mom d) → ℝ)
    (hind : ∀ κ, ind κ = 1) :
    (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) =
      fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ := by
  funext κ
  rw [hind κ, Complex.ofReal_one, mul_one]

/-- The `none` kernel of a protected paired tree is the weighted leafwise kernel of any leaf relayering. -/
theorem none_tree_kernel {P : WTParams} (LG : LayeredGarden 1) (X : RegChain) (hX : X.DecodesTree LG.garden)
    (f : GNode LG.garden.tree → ℕ) (hf : IsLayering LG.garden (relayerFun LG f)) (s t : ℝ)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (F Fu : Finset (GBranch LG.garden.tree)) (M Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1) (H : LeafProfiles 1 P.d)
    (ts : Fin 2 → ℝ) (k : Mom P.d) :
    kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW P.L P.γ P.δ (relayer LG f hf) H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ) := by
  have hfix : (ProtCfg.none.fix X s t (ts 0) : GBranch LG.garden.tree → Option ℝ) = fun _ => none :=
    funext fun b => protCfg_none_fix X s t (ts 0) b
  rw [hfix, mult_ind_one S ω F Fu M Mu ind hind]
  refine (kernelProt_relayer LG f hf _ _ _ H _ _ _ _ _ _ _).symm.trans ?_
  exact kernelProtBridge _ _ _ (relayer LG f hf) H _ _ _ _ _ _
    (not_flowerParent_of_decodesTree (G := (relayer LG f hf).garden) hX)

/-- **`none`, protected paired tree** (star weights and filters). -/
theorem none_tree {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {θ c : ℝ}
    (hθc : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) (s t : ℝ) {q' : ℕ} (hq' : q' ≤ p)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
  have hsh' := hsh
  obtain ⟨hwf, hX, hle, hch⟩ := hsh'
  have hsize : X.size = 2 * n := hsz
  have hθ := theta_range K.hη0 K.hη hθc
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
    rw [XNormRestr_congr (fun ts _ k _ => none_tree_kernel LG X hX _ hf s t S ω F Fu M Mu ind hind H ts k)]
    refine (XNormRestr_mono_set subset_rfl (Set.subset_univ _) _).trans ?_
    refine ((K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).2 p q' X hq' hwf hsize
      (relayer LG (flatLeafLayer LG X p q') hf) hX (relayer_flat_layer hX hflat hf)
      S ω cω hpres F (fun _ => false) M hM Fu Mu hMu H B hH).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL (c_nonneg hθc) n 0 _ _
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
    rw [XNormRestr_congr (fun ts _ k _ => none_tree_kernel LG X hX _ (isLayering_tree hsh hq') s t S ω F Fu M Mu
      ind hind H ts k)]
    refine (XNormRestr_mono_set subset_rfl (Set.subset_univ _) _).trans ?_
    obtain ⟨c', hc', hcc⟩ := gateWeight_of hθc
    refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hc').2 X hwf hsize LG' hX hle' p q' hq' le_rfl (hle' _)
      hlone (by rw [hinc]; omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu H B hH).trans ?_
    rw [hinc]
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL hcc n _ _ _

/-- The branches of a cap couple are in tree `0`. -/
theorem cap_branch_zero {LG : LayeredGarden 2} (h1 : LG.garden.tree 1 = TTree.leaf) (b : GBranch LG.garden.tree) :
    b.1.1 = 0 := by
  rcases Fin.exists_fin_two.mp ⟨b.1.1, rfl⟩ with h | h
  · exact h
  · exfalso
    have hb := b.2
    rw [h, h1] at hb
    simp [TTree.branching] at hb

/-- The `none` kernel of a protected cap couple is the weighted couple kernel of any leaf relayering. -/
theorem none_cap_kernel {P : WTParams} (LG : LayeredGarden 2) (X : RegChain) (h1 : LG.garden.tree 1 = TTree.leaf)
    (hplain : LG.garden.IsPlain) (f : GNode LG.garden.tree → ℕ) (hf : IsLayering LG.garden (relayerFun LG f))
    (s t : ℝ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (F Fu : Finset (GBranch LG.garden.tree)) (M Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1) (H : LeafProfiles 2 P.d)
    (ts : Fin 2 → ℝ) (k : Mom P.d) :
    kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0 =
      Flower.Stage1W.kernelLeavesW P.L P.γ P.δ (relayer LG f hf) H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
        (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ) := by
  have hfix : (ProtCfg.none.fix X s t (ts 0) : GBranch LG.garden.tree → Option ℝ) = fun _ => none :=
    funext fun b => protCfg_none_fix X s t (ts 0) b
  have hup : (fun _ : GBranch LG.garden.tree => ts 0) = fun b => if b.1.1 = 0 then ts 0 else ts 1 :=
    funext fun b => (if_pos (cap_branch_zero h1 b)).symm
  rw [hfix, kernelProt_s_irrel _ _ _ LG H _ _ (ts 1) 0 _ _ _ _ (not_loneParent_of_isPlain hplain), hup,
    mult_ind_one S ω F Fu M Mu ind hind]
  refine (kernelProt_relayer LG f hf _ _ _ H _ _ _ _ _ _ _).symm.trans ?_
  exact kernelProtBridge _ _ _ (relayer LG f hf) H _ _ _ _ _ _
    (not_flowerParent_of_isPlain (G := (relayer LG f hf).garden) hplain)

/-- A cap couple kernel does not read the port clock. -/
theorem kernelLeavesW_port_irrel {d : ℕ} (L γ δ : ℝ) {LG : LayeredGarden 2} (h1 : LG.garden.tree 1 = TTree.leaf)
    (H : LeafProfiles 2 d) (t u u' : ℝ) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else u) 0 k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else u') 0 k (fun _ => 0) 0 m := by
  have e : ∀ v : ℝ, (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then t else v) = fun _ => t :=
    fun v => funext fun b => if_pos (cap_branch_zero h1 b)
  rw [e u, e u']

/-- **`none`, protected cap couple** (star weights and filters). -/
theorem none_cap {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {θ c : ℝ}
    (hθc : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) (s t : ℝ) {q' : ℕ} (hq' : q' ≤ p)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
  have hsh' := hsh
  obtain ⟨hwf, hdec, h1, hle, -⟩ := hsh'
  have hsize : (RegCpl.type2 X .nil .triv).size = 2 * n := hsz
  have hplain : LG.garden.IsPlain := hdec.1.1
  have hθ := theta_range K.hη0 K.hη hθc
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
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ) with hFk
    rw [XNormRestr_congr (fun ts _ k _ => none_cap_kernel LG X h1 hplain _ hf s t S ω F Fu M Mu ind hind H ts k)]
    refine (XNormRestr_mono_set (fun ts hts => hts.1) (Set.subset_univ _) _).trans ?_
    refine (VineEstS5C.P2.XNormRestr_mono_idx le_rfl (Nat.zero_le (30 * P.d)) _ _ _).trans ?_
    refine (Regref.XNormRestr_shift_le θ (30 * P.d) (30 * P.d) (B := timeBox (p : ℝ) p) (F := Fk) (F' := Fk)
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
    refine ((K.hC p hp n (by rw [N_with]; exact hn) θ hθ.1 hθ.2).1 p _ hwf hsize (relayer LG (fun _ => p) hf)
      hdec (relayer_const_layer hflat hf) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu H B hH).trans ?_
    rw [hg]
    exact star_rhs_le0 K.hb0 K.hb K.hδ K.hL (c_nonneg hθc) n 0 _ _
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
    rw [XNormRestr_congr (fun ts _ k _ => none_cap_kernel LG X h1 hplain _ (isLayering_zero LG) s t S ω F Fu M Mu
      ind hind H ts k)]
    refine (XNormRestr_mono_set (fun ts hts => hts.1) (Set.subset_univ _) _).trans ?_
    refine (VineEstS5C.P2.XNormRestr_mono_idx le_rfl (Nat.zero_le (30 * P.d)) _ _ _).trans ?_
    obtain ⟨c', hc', hcc⟩ := gateWeight_of hθc
    refine ((K.hI p hp n (by rw [N_with]; exact hn) θ c' hc').1 _ hwf hsize LG' hdec hle' p q' le_rfl hq'
      (hle' _) hroot1 (by rw [hinc]; omega) S ω cω hpres F (fun _ => false) M hM Fu Mu hMu H B hH).trans ?_
    rw [hinc]
    exact star_rhs_le K.ha0 K.ha K.hδ K.hL hcc n _ _ _

/-- **`none`, protected paired tree**, milestone α form (no stars, no filters). -/
theorem alpha_none_tree {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {θ c : ℝ}
    (hθc : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) (s t : ℝ) {q' : ℕ} (hq' : q' ≤ p)
    (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ) (M Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ *
          filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  have h := none_tree K hp hn LG X hsh hsz hamb hθc s t hq' ∅ ω (fun _ => 0) (by simp) ∅ M (by simp) ∅ Mu
    (by simp) ind hind H B hH b₀ c₀
  rwa [Finset.prod_empty, one_mul] at h

/-- **`none`, protected cap couple**, milestone α form (no stars, no filters). -/
theorem alpha_none_cap {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) {θ c : ℝ}
    (hθc : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2)) (s t : ℝ) {q' : ℕ} (hq' : q' ≤ p)
    (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ) (M Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : ∀ κ, ind κ = 1)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ *
          filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.none.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  have h := none_cap K hp hn LG X hsh hsz hamb hθc s t hq' ∅ ω (fun _ => 0) (by simp) ∅ M (by simp) ∅ Mu
    (by simp) ind hind H B hH b₀ c₀
  rwa [Finset.prod_empty, one_mul] at h

end WaveTurbulence.Flower.ProtPin
