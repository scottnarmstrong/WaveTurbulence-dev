/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PairPack
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckRoot
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCap

/-! # D3 PROT-PIN: the pieces of the root cut with a suffix (`RootData`)

`X = pair m Qr Qg inner rest`, `rest ≠ nil` (D2c `RootData`): the closing pair (pieces `LGi`, `LGr`, `LGg`, placed at
the root) and the suffix `LGs` (code `rest`, at `lonePos m inner`). Bookkeeping as for the terminal cut (Pieces.lean):
well-formedness, sizes, layers (the suffix is itself a protected shape), leaf bounds, the leaf-size product, the
placed pieces as `PieceEmb`s, D3's multiplier in gate form (`ind ≡ 1`, the configurations `root`/`trace`), the star
cost split. -/

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

/-! ### Well-formedness, sizes -/

theorem root_wf (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) :
    rest.wf = true ∧ inner.wf = true ∧ Qr.wf = true ∧ Qg.wf = true := by
  simp only [RegChain.wf, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨hwr, hwg⟩, hwi⟩, hws⟩ := hwf
  exact ⟨hws, hwi, hwr, hwg⟩

theorem root_sizes {n : ℕ} (hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n) :
    ∃ ns ni nr ng : ℕ, rest.size = 2 * ns ∧ inner.size = 2 * ni ∧ Qr.size = 2 * nr ∧ Qg.size = 2 * ng ∧
      ns + ni + nr + ng + 1 = n := by
  rw [size_rootCut] at hsz
  obtain ⟨ns, hs⟩ := chain_size_even rest
  obtain ⟨ni, hi⟩ := chain_size_even inner
  obtain ⟨nr, hr⟩ := code_size_even Qr
  obtain ⟨ng, hg⟩ := code_size_even Qg
  exact ⟨ns, ni, nr, ng, by omega, by omega, by omega, by omega, by omega⟩

/-! ### Layers -/

theorem root_lonePath (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) :
    (RegChain.pair m Qr Qg inner rest).lonePath = bPath m inner ++ ([m.lone] ++ rest.lonePath) := by
  simp [RegChain.lonePath, bPath]

/-- **The suffix is a protected shape**, and the pieces of the closing pair have layers `≤ p` (the interior's lone
position `𝔫_b` in layer `p`). -/
theorem root_layers (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {p : ℕ}
    (h : ProtShape p (RegChain.pair m Qr Qg inner rest) LG) :
    ProtShape p rest LGs ∧
    (∀ a, LGi.layer a ≤ p) ∧ (∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = p) ∧
    (∀ a, LGr.layer a ≤ p) ∧ (∀ a, LGg.layer a ≤ p) := by
  have hle := layerAt_le_of_forall_layer_le h.2.2.1
  have hch := h.2.2.2
  have hlp := root_lonePath m Qr Qg inner rest
  refine ⟨⟨(root_wf h.1).1, D.decS, fun a => (D.layS a).trans_le (hle _), fun b hb0 hpre hne => ?_⟩,
    fun a => (D.layI a).trans_le (hle _), fun a ha' => ?_, fun a => (D.layR a).trans_le (hle _),
    fun a => (D.layG a).trans_le (hle _)⟩
  · -- the suffix chain
    rw [D.hl₂ b]
    refine hch _ (Nat.lt_one_iff.mp (D.gd.ofSum (.inr b)).1.1.isLt) ?_ ?_
    · have e : (D.gd.ofSum (.inr b)).1.2 = lonePos m inner ++ b.1.2 := congrArg Prod.snd (D.inr_path b)
      rw [e, show (RegChain.pair m Qr Qg inner rest).lonePath = lonePos m inner ++ rest.lonePath by
        simp [RegChain.lonePath, lonePos, bPath]]
      exact (List.prefix_append_right_inj _).2 hpre
    · have e : (D.gd.ofSum (.inr b)).1.2 = lonePos m inner ++ b.1.2 := congrArg Prod.snd (D.inr_path b)
      rw [e, show (RegChain.pair m Qr Qg inner rest).lonePath = lonePos m inner ++ rest.lonePath by
        simp [RegChain.lonePath, lonePos, bPath]]
      exact fun he => hne (List.append_cancel_left he)
  · -- the interior's lone position is `𝔫_b`
    rw [D.layI a, ha']
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    have e : layerAt LG ((0 : Fin 1), bPath m inner) = p := by
      rw [← D.layer_bR]
      refine hch D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
      · rw [hbp, hlp]; exact List.prefix_append _ _
      · rw [hbp, hlp]; simp
    simpa [bPath] using e

/-! ### Leaf bounds -/

/-- The suffix bounds. -/
def rootBs (m : MiniTreeCode) (inner : RegChain) (B : (Fin 1 × TTree.Path) → NNReal) :
    (Fin 1 × TTree.Path) → NNReal := fun a => B ((0 : Fin 1), lonePos m inner ++ a.2)

theorem root_leafwise (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {d : ℕ} {H : LeafProfiles 1 d}
    {B : (Fin 1 × TTree.Path) → NNReal} (hH : LeafwiseControlled LG H B) :
    LeafwiseControlled LGs (rootHs m inner H) (rootBs m inner B) ∧
    LeafwiseControlled LGi (cutHi .nil m H) (cutBi .nil m B) ∧
    LeafwiseControlled LGr (cutHr .nil m inner (LG.garden.sig 0) H) (cutBr .nil m inner (LG.garden.sig 0) B) ∧
    LeafwiseControlled LGg (cutHg .nil m inner (LG.garden.sig 0) H) (cutBg .nil m inner (LG.garden.sig 0) B) := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofBot D.hmbot ℓ hℓ
    have e : ((0 : Fin 1), lonePos m inner ++ ℓ.1.2) = ℓ'.1 := by
      rw [he, cpair_lonePath]
      have hj : ℓ.1.1 = 0 := Subsingleton.elim _ _
      simp [botAddr, hj]
    simp only [rootHs, rootBs]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofI ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
    have e : ((0 : Fin 1), RegChain.nil.lonePath ++ m.c :: ℓ.1.2) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφi, RegChain.lonePath]
    simp only [cutHi, cutBi]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofR ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
    have e : ((0 : Fin 1), RegChain.nil.lonePath ++ (rBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2)) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφr, RegChain.lonePath, D.sigZ]
    simp only [cutHr, cutBr]
    rw [e]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofG ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
    have e : ((0 : Fin 1), RegChain.nil.lonePath ++ (gBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2)) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφg, RegChain.lonePath, D.sigZ]
    simp only [cutHg, cutBg]
    rw [e]
    exact hH ℓ' hℓ'

theorem root_leafSize (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) (B : (Fin 1 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = leafSizeProduct LGs (rootBs m inner B) * (leafSizeProduct LGi (cutBi .nil m B) *
      leafSizeProduct LGr (cutBr .nil m inner (LG.garden.sig 0) B) *
        leafSizeProduct LGg (cutBg .nil m inner (LG.garden.sig 0) B)) := by
  set f : Fin 1 × Path → ℝ := fun z => (B z : ℝ) with hf
  have e0 : leafSizeProduct LG B = ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := rfl
  rw [e0, D.gd.prod_inputLeaves_glue D.decZ.2.1 D.hmtop D.hmbot f,
    D.hp.prod_inputLeaves_pair (fun z => f (topAddr z))]
  have e1 : ∏ ℓ ∈ inputLeaves LGs.garden, f (botAddr (cpair m Qr Qg inner).lonePath ℓ.1) =
      leafSizeProduct LGs (rootBs m inner B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hj : ℓ.1.1 = 0 := Subsingleton.elim _ _
    simp [hf, botAddr, hj, rootBs, cpair_lonePath]
  have e2 : ∏ ℓ ∈ inputLeaves LGi.garden, f (topAddr (pφi m ℓ.1)) = leafSizeProduct LGi (cutBi .nil m B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφi, cutBi, RegChain.lonePath]
  have e3 : ∏ ℓ ∈ inputLeaves LGr.garden, f (topAddr (pφr m inner (LGZ.garden.sig 0) ℓ.1)) =
      leafSizeProduct LGr (cutBr .nil m inner (LG.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφr, cutBr, D.sigZ, RegChain.lonePath]
  have e4 : ∏ ℓ ∈ inputLeaves LGg.garden, f (topAddr (pφg m inner (LGZ.garden.sig 0) ℓ.1)) =
      leafSizeProduct LGg (cutBg .nil m inner (LG.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφg, cutBg, D.sigZ, RegChain.lonePath]
  rw [e1, e2, e3, e4]
  ring

/-! ### The placed pieces -/

theorem rootEmbZ (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) :
    PieceEmb D.gd.ι₁ (fun x => D.gd.ofSum (.inl x)) :=
  ⟨fun _ => rfl, fun x i => D.gd.ofSum_inl_child x i⟩

theorem rootEmbS (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) :
    PieceEmb D.ιS (fun y => D.gd.ofSum (.inr y)) :=
  ⟨fun y => D.gd.ofSum_inr_toNode y, fun y i => D.gd.ofSum_inr_child y i⟩

theorem rootEmbI (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) :
    PieceEmb D.ιI (fun x => D.gd.ofSum (.inl (D.hp.βi x))) :=
  (⟨D.hp.βi_toNode, D.hp.βi_child⟩ : PieceEmb D.hp.ιi D.hp.βi).comp (rootEmbZ D)

theorem rootEmbR (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) :
    PieceEmb D.ιR (fun y => D.gd.ofSum (.inl (D.hp.βr y))) :=
  (⟨D.hp.βr_toNode, D.hp.βr_child⟩ : PieceEmb D.hp.ιr D.hp.βr).comp (rootEmbZ D)

theorem rootEmbG (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) :
    PieceEmb D.ιG (fun y => D.gd.ofSum (.inl (D.hp.βg y))) :=
  (⟨D.hp.βg_toNode, D.hp.βg_child⟩ : PieceEmb D.hp.ιg D.hp.βg).comp (rootEmbZ D)

/-- **D3's multiplier at the root cut, gate-form pieces** (`ind ≡ 1`: the configurations `root`, `trace`). -/
theorem star_root_mult (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {d : ℕ}
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind1 : ∀ κ, ind κ = 1) :
    D.MultFactors
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F (fun _ => false) M Fu Mu D.aR A * fD3' S ω F (fun _ => false) M Fu Mu D.bR B)
      (pullMult D.ιI (fun x => D.gd.ofSum (.inl (D.hp.βi x))) S ω F M Fu Mu)
      (pullMult D.ιR (fun y => D.gd.ofSum (.inl (D.hp.βr y))) S ω F M Fu Mu)
      (pullMult D.ιG (fun y => D.gd.ofSum (.inl (D.hp.βg y))) S ω F M Fu Mu)
      (pullMult D.ιS (fun y => D.gd.ofSum (.inr y)) S ω F M Fu Mu) := by
  intro K
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  have h := D.multFactors_local (fD3' S ω F (fun _ => false) M Fu Mu) K
  simp only at h ⊢
  have e1 : ∀ κ, (ind κ : ℂ) = 1 := fun κ => by rw [hind1, Complex.ofReal_one]
  rw [e1, mul_one, starFilt_local' S (hroot_tree hX D.dec S), h]
  simp only [pullMult]
  rw [pull_mult (rootEmbI D), pull_mult (rootEmbR D), pull_mult (rootEmbG D), pull_mult (rootEmbS D)]

/-- The cut factor at the root cut is bounded by the star costs of the two linked nodes. -/
theorem star_root_Mc_le (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {d : ℕ}
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) {J : ℕ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (A B : Fin 4 → Mom d) :
    ‖fD3' S ω F (fun _ => false) M Fu Mu D.aR A * fD3' S ω F (fun _ => false) M Fu Mu D.bR B‖ ≤
      costB S cω D.aR * costB S cω D.bR := by
  rw [norm_mul]
  exact mul_le_mul (norm_fD3'_le S ω cω hpres F M Fu Mu _ _) (norm_fD3'_le S ω cω hpres F M Fu Mu _ _)
    (norm_nonneg _) (costB_nonneg _ _ _)

/-- **The star cost splits at the root cut.** -/
theorem star_root_cost (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) (S : Finset (GNode LG.garden.tree))
    (cω : GNode LG.garden.tree → ℝ) :
    ∏ a ∈ S, max (cω a) 0 = costB S cω D.aR * costB S cω D.bR *
      ((∏ a ∈ pullS D.ιS S, max (cω (D.ιS a)) 0) * ((∏ a ∈ pullS D.ιI S, max (cω (D.ιI a)) 0) *
        ((∏ a ∈ pullS D.ιR S, max (cω (D.ιR a)) 0) * ∏ a ∈ pullS D.ιG S, max (cω (D.ιG a)) 0))) := by
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  rw [prod_cost_branch S (hroot_tree hX D.dec S) cω, D.prod_branch_root, pull_cost (rootEmbS D),
    pull_cost (rootEmbI D), pull_cost (rootEmbR D), pull_cost (rootEmbG D)]

end WaveTurbulence.Flower.ProtPin
