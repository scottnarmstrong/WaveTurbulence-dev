/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapKer

/-! # B3s-HELPER8 / CAP: the per-slot factor of a cap couple is a D3/D6 filter weight

On a nontrivial cap slot `K`, the per-slot factor transported to the paired tree, `CapK.capθ1`, is the product over
the branches `b1` of the paired tree (reconstruction branch `capE b1`) that are non-core capped-stem nodes
(`capStem`) of σ's dyadic filter `chi0(|Ω|/2^i L)`, the selection shell `chi0(|Ω|/Rs)` (stem nodes other than the
selected vertex of the tree) and the selected filter `chiD(|Ω|/Rs)` (at the selected vertex):
**`capθ1_eq`**: `capθ1 = filtWeight (capFT ∪ capSelT) (· ∈ capSelT) (Rs at capSelT, 2^i L else) ·
filtWeight capFuT false capMuT`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo
  WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB

namespace WaveTurbulence.Flower.MkSlotsO

namespace CapK

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-! ### Branches of the paired tree in the reconstruction -/

/-- The reconstruction branch of a branch of the paired tree. -/
abbrev capE (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    GBranch (layeredReconstruction D hS layer hLayer).garden.tree :=
  embBr K.emb b1.1.2 b1.2

theorem capE_toNode (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    (capE K layer hLayer b1).toNode = K.e1 layer hLayer b1.toNode :=
  Subtype.ext (K.e1_val layer hLayer b1.toNode).symm

theorem capE_fst (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) : (capE K layer hLayer b1).1.1 = K.u.1 := rfl

/-- The node of a branch of the paired tree is a core node. -/
def capCore (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) : Prop :=
  ∃ β : GBranch S.tree, K.e1 layer hLayer b1.toNode = (D.coreBranch hS β).toNode

/-- A non-core capped-stem branch of the paired tree. -/
def capStemB (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) : Prop :=
  ¬ capCore K layer hLayer b1 ∧ ∃ j, capE K layer hLayer b1 ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j

/-- The selected filters (`chiD`, scale `Rs`). -/
def capSelT (kSel : Fin w → Option ℕ) : Finset (GBranch (K.Dq layer hLayer).T1.garden.tree) :=
  Finset.univ.filter fun b1 => capStemB K layer hLayer b1 ∧
    capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel

/-- σ's dyadic filters off the selected vertex. -/
def capFT (σ kSel : Fin w → Option ℕ) : Finset (GBranch (K.Dq layer hLayer).T1.garden.tree) :=
  Finset.univ.filter fun b1 => capStemB K layer hLayer b1 ∧ (σ K.u.1).isSome ∧
    capE K layer hLayer b1 ∉ selSetCap (layeredReconstruction D hS layer hLayer) J kSel

/-- The second layer: the selection shells, and σ's filter at the selected vertex. -/
def capFuT (σ kSel : Fin w → Option ℕ) : Finset (GBranch (K.Dq layer hLayer).T1.garden.tree) :=
  Finset.univ.filter fun b1 => capStemB K layer hLayer b1 ∧
    ((∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ capE K layer hLayer b1) ∨
      (capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel ∧ (σ K.u.1).isSome))

/-- σ's dyadic scale of the chain's tree. -/
def capMσ (L : ℝ) (σ : Fin w → Option ℕ) : ℝ := 2 ^ ((σ K.u.1).getD 0) * L

/-- The scales of the second layer. -/
def capMuT (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    ℝ :=
  if capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel then capMσ K L σ
  else Rs K.u.1

/-! ### The factor at one branch -/

theorem branching_e1_iff (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    (K.e1 layer hLayer a1).1.2 ∈ ((D.garden hS).tree (K.e1 layer hLayer a1).1.1).branching ↔
      a1.1.2 ∈ (K.X.plug K.ζ .leaf).branching := by
  rw [K.e1_val layer hLayer a1]
  exact (node_iff_of_subtree K.emb.node K.emb.tree a1.1.2).2.2

theorem genNW_e1 (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) (x : ℝ) :
    MkSlotsI.genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (K.e1 layer hLayer b1.toNode) x =
      if ∃ j, capE K layer hLayer b1 ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
          (capE K layer hLayer b1)) x : ℂ) *
          (if capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel then
            ((chiD (|x| / Rs K.u.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hb : (K.e1 layer hLayer b1.toNode).1.2 ∈ ((layeredReconstruction D hS layer hLayer).garden.tree
      (K.e1 layer hLayer b1.toNode).1.1).branching := (branching_e1_iff K layer hLayer b1.toNode).2 b1.2
  have e : (⟨(K.e1 layer hLayer b1.toNode).1, hb⟩ : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) =
      capE K layer hLayer b1 := Subtype.ext (K.e1_val layer hLayer b1.toNode)
  unfold MkSlotsI.genNW
  simp only [hb, ↓reduceDIte]
  simp only [e, K.e1_fst layer hLayer]
  rfl

theorem omegaAt_ι {d : ℕ} (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d)
    (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    MkSlotsS.omegaAt (fun a => K' ((K.Dq layer hLayer).ρ a)) ((K.Dq layer hLayer).ι b1.toNode) =
      omegaNode (K.Dq layer hLayer).T1.garden K' b1 := by
  rw [← (K.Dq layer hLayer).βc_toNode b1]
  have hb : (((K.Dq layer hLayer).βc b1).toNode).1.2 ∈ ((nativeCoupleLayered D hS layer hLayer q).garden.tree
      (((K.Dq layer hLayer).βc b1).toNode).1.1).branching := ((K.Dq layer hLayer).βc b1).2
  unfold MkSlotsS.omegaAt
  simp only [hb, ↓reduceDIte]
  exact (K.Dq layer hLayer).omegaNode_βc K' b1

theorem prod_mem_eq_ite {α M : Type*} [Fintype α] [CommMonoid M] (A : Finset α) (f : α → M) :
    ∏ b ∈ A, f b = ∏ b, if b ∈ A then f b else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem radProd_single (r x : ℝ) : MkSlotsT.radProd [r] x = chi0 (|x| / r) := by
  simp [MkSlotsT.radProd]

theorem mem_capSelT (kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    b1 ∈ capSelT K layer hLayer kSel ↔ capStemB K layer hLayer b1 ∧
      capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel := by
  unfold capSelT; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_capFT (σ kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    b1 ∈ capFT K layer hLayer σ kSel ↔ capStemB K layer hLayer b1 ∧ (σ K.u.1).isSome ∧
      capE K layer hLayer b1 ∉ selSetCap (layeredReconstruction D hS layer hLayer) J kSel := by
  unfold capFT; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_capFuT (σ kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    b1 ∈ capFuT K layer hLayer σ kSel ↔ capStemB K layer hLayer b1 ∧
      ((∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ capE K layer hLayer b1) ∨
        (capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel ∧
          (σ K.u.1).isSome)) := by
  unfold capFuT; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem radSigma_eq (L : ℝ) (σ : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) (x : ℝ) :
    MkSlotsT.radProd (MkSlotsT.radSigma L σ (capE K layer hLayer b1)) x =
      if (σ K.u.1).isSome then chi0 (|x| / capMσ K L σ) else 1 := by
  unfold MkSlotsT.radSigma capMσ
  rw [capE_fst K layer hLayer b1]
  cases σ K.u.1 with
  | none => rfl
  | some i => simp [radProd_single]

/-- The factor at one branch, as the two filter layers. -/
theorem factor_eq (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) (x : ℝ) :
    (if capCore K layer hLayer b1 then (1 : ℂ) else
      if ∃ j, capE K layer hLayer b1 ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
          (capE K layer hLayer b1)) x : ℂ) *
          (if capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel then
            ((chiD (|x| / Rs K.u.1) : ℝ) : ℂ) else 1)
      else 1) =
      (if b1 ∈ capFT K layer hLayer σ kSel ∪ capSelT K layer hLayer kSel then
          (((if decide (b1 ∈ capSelT K layer hLayer kSel) then FlShell.chiD else chi0)
            (|x| / (if b1 ∈ capSelT K layer hLayer kSel then Rs K.u.1 else capMσ K L σ)) : ℝ) : ℂ)
        else 1) *
      (if b1 ∈ capFuT K layer hLayer σ kSel then
          (((if (false : Bool) = true then FlShell.chiD else chi0) (|x| / capMuT K layer hLayer L σ kSel Rs b1) : ℝ) : ℂ)
        else 1) := by
  have hz : (capE K layer hLayer b1).1.1 = K.u.1 := rfl
  by_cases hcore : capCore K layer hLayer b1
  · have hs : ¬ capStemB K layer hLayer b1 := fun h => h.1 hcore
    have h1 : b1 ∉ capFT K layer hLayer σ kSel := fun h => hs ((mem_capFT K layer hLayer σ kSel b1).1 h).1
    have h2 : b1 ∉ capSelT K layer hLayer kSel := fun h => hs ((mem_capSelT K layer hLayer kSel b1).1 h).1
    have h3 : b1 ∉ capFuT K layer hLayer σ kSel := fun h => hs ((mem_capFuT K layer hLayer σ kSel b1).1 h).1
    simp only [hcore, h1, h2, h3, Finset.mem_union, or_self, ↓reduceIte, mul_one]
  by_cases hst : ∃ j, (capE K layer hLayer b1) ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j
  swap
  · have hs : ¬ capStemB K layer hLayer b1 := fun h => hst h.2
    have h1 : b1 ∉ capFT K layer hLayer σ kSel := fun h => hs ((mem_capFT K layer hLayer σ kSel b1).1 h).1
    have h2 : b1 ∉ capSelT K layer hLayer kSel := fun h => hs ((mem_capSelT K layer hLayer kSel b1).1 h).1
    have h3 : b1 ∉ capFuT K layer hLayer σ kSel := fun h => hs ((mem_capFuT K layer hLayer σ kSel b1).1 h).1
    simp only [hcore, hst, h1, h2, h3, Finset.mem_union, or_self, ↓reduceIte, mul_one]
  have hs : capStemB K layer hLayer b1 := ⟨hcore, hst⟩
  have hradR : MkSlotsG.radRaw (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (capE K layer hLayer b1) = MkSlotsT.radSigma L σ (capE K layer hLayer b1) ++ MkSlotsG.shellRad (layeredReconstruction D hS layer hLayer) J kSel Rs (capE K layer hLayer b1) := rfl
  by_cases hsel : (capE K layer hLayer b1) ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel
  · have hv := (selSetCap_spec hsel).2.1
    rw [hz] at hv
    have hn : ¬ ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ (capE K layer hLayer b1) := by
      rintro ⟨v, hv', hne⟩
      rw [hv] at hv'
      exact hne (Option.some.inj hv').symm
    have hsh : MkSlotsG.shellRad (layeredReconstruction D hS layer hLayer) J kSel Rs (capE K layer hLayer b1) = [] := by
      unfold MkSlotsG.shellRad
      rw [hz]
      simp only [hn, ↓reduceIte]
    have h1 : b1 ∉ capFT K layer hLayer σ kSel := fun h => ((mem_capFT K layer hLayer σ kSel b1).1 h).2.2 hsel
    have h2 : b1 ∈ capSelT K layer hLayer kSel := (mem_capSelT K layer hLayer kSel b1).2 ⟨hs, hsel⟩
    have hFu : b1 ∈ capFuT K layer hLayer σ kSel ↔ (σ K.u.1).isSome := by
      rw [mem_capFuT]
      exact ⟨fun h => h.2.resolve_left hn |>.2, fun h => ⟨hs, Or.inr ⟨hsel, h⟩⟩⟩
    have hMu : capMuT K layer hLayer L σ kSel Rs b1 = capMσ K L σ := by
      unfold capMuT; simp only [hsel, ↓reduceIte]
    rw [hradR, MkSlotsT.radProd_append, hsh, radSigma_eq]
    simp only [hcore, hst, hsel, h1, h2, hFu, hMu, Finset.mem_union, or_true, decide_true, ↓reduceIte,
      MkSlotsT.radProd_nil, mul_one, Bool.false_eq_true]
    by_cases hσ : (σ K.u.1).isSome
    · simp only [hσ, ↓reduceIte]
      rw [mul_comm]
      rfl
    · simp only [hσ, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_one, one_mul, mul_one]
      rfl
  · have hsh : MkSlotsG.shellRad (layeredReconstruction D hS layer hLayer) J kSel Rs (capE K layer hLayer b1) =
        if ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ (capE K layer hLayer b1) then [Rs K.u.1] else [] := by
      unfold MkSlotsG.shellRad
      rw [hz]
    have h2 : b1 ∉ capSelT K layer hLayer kSel := fun h => hsel ((mem_capSelT K layer hLayer kSel b1).1 h).2
    have h1 : b1 ∈ capFT K layer hLayer σ kSel ↔ (σ K.u.1).isSome := by
      rw [mem_capFT]
      exact ⟨fun h => h.2.1, fun h => ⟨hs, h, hsel⟩⟩
    have h3 : b1 ∈ capFuT K layer hLayer σ kSel ↔ ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ (capE K layer hLayer b1) := by
      rw [mem_capFuT]
      exact ⟨fun h => h.2.resolve_right fun h' => hsel h'.1, fun h => ⟨hs, Or.inl h⟩⟩
    have hMu : capMuT K layer hLayer L σ kSel Rs b1 = Rs K.u.1 := by
      unfold capMuT; simp only [hsel, ↓reduceIte]
    rw [hradR, MkSlotsT.radProd_append, hsh, radSigma_eq]
    simp only [hcore, hst, hsel, h1, h2, h3, hMu, Finset.mem_union, or_false, decide_false, ↓reduceIte,
      mul_one, Bool.false_eq_true]
    by_cases hσ : (σ K.u.1).isSome
    · by_cases hsv : ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ (capE K layer hLayer b1)
      · simp only [hσ, hsv, ↓reduceIte, radProd_single, Complex.ofReal_mul]
      · simp only [hσ, hsv, ↓reduceIte, MkSlotsT.radProd_nil, mul_one]
    · by_cases hsv : ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel K.u.1 = some v ∧ v ≠ (capE K layer hLayer b1)
      · simp only [hσ, hsv, Bool.false_eq_true, ↓reduceIte, radProd_single, one_mul]
      · simp only [hσ, hsv, Bool.false_eq_true, ↓reduceIte, MkSlotsT.radProd_nil, mul_one, Complex.ofReal_one]

/-! ### The product -/

include hGeo in
/-- **The per-slot factor of the cap couple on the paired tree is D3/D6's two-layer filter weight.** -/
theorem capθ1_eq {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    capθ1 K layer hLayer L σ kSel Rs K' =
      filtWeight (capFT K layer hLayer σ kSel ∪ capSelT K layer hLayer kSel)
          (fun b => decide (b ∈ capSelT K layer hLayer kSel))
          (fun b => if b ∈ capSelT K layer hLayer kSel then Rs K.u.1 else capMσ K L σ) K' *
        filtWeight (capFuT K layer hLayer σ kSel) (fun _ => false) (capMuT K layer hLayer L σ kSel Rs) K' := by
  unfold capθ1 capΘ
  rw [(K.Dq layer hLayer).prod_nodes]
  have hc : (if ∃ β : GBranch S.tree, (nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c) = (D.coreBranch hS β).toNode then (1 : ℂ)
      else MkSlotsI.genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c))
        (MkSlotsS.omegaAt (fun a => K' ((K.Dq layer hLayer).ρ a))
          (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c))) = 1 := by
    split_ifs
    · rfl
    · have h1 : ((nativeCoupleForest D hS q).nodeEmbedding
          (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)).1.1 = K.cleaf.1.1 := by
        rw [K.cRoot_val layer hLayer]; exact inflatedPosition_index S D.tree _
      have hnb : ¬ ((nativeCoupleForest D hS q).nodeEmbedding
          (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)).1.2 ∈
          ((layeredReconstruction D hS layer hLayer).garden.tree ((nativeCoupleForest D hS q).nodeEmbedding
            (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)).1.1).branching := by
        intro hb
        rw [h1, hGeo.cap_leaf _ K.cJ] at hb
        simp [TTree.branching] at hb
      unfold MkSlotsI.genNW
      simp only [hnb, ↓reduceDIte]
  rw [hc, one_mul]
  rw [prod_node_eq_prod_branch (fun a1 : GNode (K.Dq layer hLayer).T1.garden.tree =>
    if ∃ β : GBranch S.tree, (nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1) = (D.coreBranch hS β).toNode
    then (1 : ℂ) else MkSlotsI.genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1))
      (MkSlotsS.omegaAt (fun a => K' ((K.Dq layer hLayer).ρ a)) ((K.Dq layer hLayer).ι a1))) (fun a1 ha1 => ?_)]
  · unfold filtWeight
    rw [prod_mem_eq_ite (capFT K layer hLayer σ kSel ∪ capSelT K layer hLayer kSel),
      prod_mem_eq_ite (capFuT K layer hLayer σ kSel), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b1 _ => ?_
    have e1 := genNW_e1 K layer hLayer L σ kSel Rs b1 (omegaNode (K.Dq layer hLayer).T1.garden K' b1)
    have e2 := omegaAt_ι K layer hLayer K' b1
    have e := factor_eq K layer hLayer L σ kSel Rs b1 (omegaNode (K.Dq layer hLayer).T1.garden K' b1)
    rw [← e1] at e
    rw [e2]
    convert e using 2
    · exact Iff.rfl
    · simp only [decide_eq_true_eq]
    · split_ifs <;> rfl
  · split_ifs
    · rfl
    · have hnb := fun hb => ha1 ((branching_e1_iff K layer hLayer a1).1 hb)
      unfold MkSlotsI.genNW
      exact dite_eq_right_of_eq_false (eq_false hnb)

end CapK

end WaveTurbulence.Flower.MkSlotsO
