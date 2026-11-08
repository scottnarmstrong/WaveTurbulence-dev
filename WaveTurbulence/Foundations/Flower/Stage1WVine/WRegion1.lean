/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenModes
public import WaveTurbulence.Foundations.Flower.V5W.RowData
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WLeaves
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeLayer
public import WaveTurbulence.Foundations.Flower.CohTrunk.Kernel
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr6
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr8

/-! # STAGE1W-VINE (T3): the regional rows of the frontier-weighted slot family

The frontier-weighted slot family of a reconstruction is O4′'s weighted native slot kernel `slotFnNW … (fwNodeV LG p g)`
(STAGE1W-O4 row T2: `Stage1WNoVine.kernelLeaves_skeleton_reduction_selNW`, module `WLeaves`), with the frontier node
weight `fwNodeV` (= O4′'s `fwNode`, row T1; its embedding lemma is copied here by source, see `COPIED-SHA256SUMS`, because
O4′'s `FwNode` module is still being edited).  At the regional
slots of a unit (all nodes in the tree `j₁` of the unit's upper joint, all native roots garden-nonroot) it is:

* `slotFnNW_regional_couple/_chain`: the pinned `coupleLeavesTop`/`treeLeavesTop` with the single weight `g j₁`, the
  root parent layers `coupleRootParents`/`treeRootParent` and the unit's layer profile (P* lemma 1);
* `coupleLeavesTop_coherent`, `treeLeavesTop_coherent`: on a coherent row (incoherency `0`) the crossing factor times
  main's `KQstar`/`KTstar` (COH-TRUNK `coupleLeavesTopR_factor`, `rowTopAgreementTree`; supplement Lemma 5.1);
* `norm_slotFnNW_regional_couple_le/_chain_le`: the bound `cψ^{#nodes}` times V5's `pairBound`/`chainBound`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W

/-! ## Generic facts on the weighted leaf kernel -/

theorem kernelLeavesW_congr_H {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H H' : LeafProfiles w d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = H' ℓ.1)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeavesW L γ δ LG H' up s k₀ nroot nfl m := by
  unfold kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  exact Finset.prod_congr rfl fun ℓ hℓ => by rw [hH ℓ hℓ]

theorem kernelLeavesW_one {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (hm : ∀ k, m k = 1) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold kernelLeavesW kernelLeaves
  simp only [hm, one_mul]

theorem kernelLeavesW_const' {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (c : ℂ)
    (hm : ∀ κ : GenDecoration LG.garden d nroot nfl, m (cosetDecoration LG.garden L k₀ κ.1) = c) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = c * kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold kernelLeavesW kernelLeaves
  simp_rw [hm]
  rw [tsum_mul_left]
  ring

theorem rowTopWeightR_one' {w d : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) : rowTopWeightR p (fun _ _ => (1 : ℂ)) LG qr k = 1 := by
  unfold rowTopWeightR topPsi
  simp

/-- The norm of a weighted leaf kernel at layer profiles: `M` times the bound of the unweighted kernel. -/
theorem norm_kernelLeavesW_le {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (M : ℝ) (hm : ∀ k, ‖m k‖ ≤ M)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    ‖kernelLeavesW L γ δ LG (layerProfiles LG F) up s k₀ nroot nfl m‖ ≤
      M * (|coupling d L γ δ| ^ LG.garden.order *
        ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hm (fun _ => 0))
  have hmaj := summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF
  have hsumm : ∀ κ : GenDecoration LG.garden d nroot nfl,
      ‖m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, ((layerProfiles LG F) ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))‖ ≤
        M * inputLeafMajorant L F LG k₀ κ := by
    intro κ
    rw [norm_mul]
    refine mul_le_mul (hm _) ?_ (norm_nonneg _) hM
    have e : (∏ ℓ ∈ inputLeaves LG.garden,
        ((layerProfiles LG F) ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
        ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) :=
      Finset.prod_congr rfl fun ℓ _ => by rw [layerProfiles_leaf]
    rw [e]
    exact norm_kernel_summand_le_inputLeafMajorant L γ δ F LG up s k₀ κ
  have hs : Summable fun κ : GenDecoration LG.garden d nroot nfl => M * inputLeafMajorant L F LG k₀ κ :=
    hmaj.mul_left M
  unfold kernelLeavesW
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hz := VineEstS4.norm_zeta_le_one LG.garden
  have hb := (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsumm hs)).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsumm hs).tsum_le_tsum hsumm hs)
  rw [tsum_mul_left] at hb
  have hc : 0 ≤ |coupling d L γ δ| ^ LG.garden.order := by positivity
  calc |coupling d L γ δ| ^ LG.garden.order * ‖LG.garden.zeta‖ * ‖_‖
      ≤ |coupling d L γ δ| ^ LG.garden.order * 1 *
          (M * ∑' κ : GenDecoration LG.garden d nroot nfl, inputLeafMajorant L F LG k₀ κ) := by
        gcongr
    _ = _ := by ring

/-! ## The frontier node weight and its embedding (copied from STAGE1W-O4 `FwNode`, row T1) -/

/-- The frontier node weight of a layered garden (`1` at the roots); O4′'s `fwNode`, verbatim body. -/
def fwNodeV {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) (z : GNode LG.garden.tree)
    (x : Mom d) : ℂ :=
  if z.1.2 ≠ [] then topPsi p (g z.1.1) (LG.layer z) (LG.parentLayer p z) x else 1

theorem fwWeight_eq_prod_fwNodeV {P : WTParams} {R : ℕ} (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (base : Mom P.d)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (LG : LayeredGarden (2 * R))
    (κ : GenDecoration LG.garden P.d roots 0) :
    fwWeight p g base LG κ = ∏ z, fwNodeV LG p g z (cosetDecoration LG.garden P.L base κ.1 z) := rfl

theorem norm_fwNodeV_le {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) (cψ : ℝ)
    (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (z : GNode LG.garden.tree) (x : Mom d) :
    ‖fwNodeV LG p g z x‖ ≤ cψ := by
  unfold fwNodeV topPsi
  split_ifs
  · exact hg _ _
  · simpa using hc
  · simpa using hc

theorem parentLayer_nonroot {w : ℕ} (LG : LayeredGarden w) (top : ℕ) (a : GNode LG.garden.tree)
    (ha : a.1.2 ≠ []) : LG.parentLayer top a = LG.layer (a.parent ha).toNode := by
  unfold LayeredGarden.parentLayer
  rw [if_neg ha]
  rfl

/-- An object embedded by address prefixing with garden-nonroot roots: its node weights are its `rowTopWeight`
factors with the garden parent layers of its roots (copy of O4′'s `fwNode_embed`, nonroot case). -/
theorem fwNodeV_embed {v w d : ℕ} (LG : LayeredGarden w) (LG' : LayeredGarden v)
    (e : GNode LG'.garden.tree → GNode LG.garden.tree) (r : Fin v → Fin w × TTree.Path)
    (he : ∀ a, (e a).1 = ((r a.1.1).1, (r a.1.1).2 ++ a.1.2)) (hl : ∀ a, LG'.layer a = LG.layer (e a))
    (hr : ∀ j, (r j).2 ≠ []) (p : ℕ) (g : Fin w → Mom d → ℂ) (a : GNode LG'.garden.tree) (x : Mom d) :
    fwNodeV LG p g (e a) x = topPsi p (g (r a.1.1).1) (LG'.layer a)
      (rowParentLayer LG' (fun j => LG.parentLayer p (e (GNode.root LG'.garden.tree j))) a) x := by
  have hi : (e a).1.1 = (r a.1.1).1 := by rw [he]
  unfold fwNodeV rowParentLayer
  rw [hl a]
  by_cases ha : a.1.2 = []
  · have hea : (e a).1.2 = (r a.1.1).2 := by rw [he]; simp [ha]
    have hra : a = GNode.root LG'.garden.tree a.1.1 := Subtype.ext (Prod.ext rfl ha)
    rw [if_pos ha]
    have hn : (e a).1.2 ≠ [] := by rw [hea]; exact hr _
    rw [if_pos hn, hi]
    beta_reduce
    rw [← hra]
  · have hea : (e a).1.2 ≠ [] := by rw [he]; simp [ha]
    rw [if_pos hea, if_neg ha, hi]
    congr 1
    have e1 : (e (a.parent ha).toNode).1 = ((r a.1.1).1, (r a.1.1).2 ++ a.1.2.dropLast) := he _
    have e2 : ((e a).parent hea).toNode.1 = ((r a.1.1).1, (r a.1.1).2 ++ a.1.2.dropLast) := by
      show ((e a).1.1, (e a).1.2.dropLast) = _
      rw [he]; simp [List.dropLast_append_of_ne_nil ha]
    rw [parentLayer_nonroot LG p (e a) hea, parentLayer_nonroot LG' 0 a ha, hl]
    exact congrArg LG.layer (Subtype.ext (e2.trans e1.symm))

/-- `kernelNodeW` with a node profile that agrees with a leaf profile at the input leaves is `kernelLeavesW`. -/
theorem kernelNodeW_eq_kernelLeavesW {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (H : LeafProfiles w d)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden, A ℓ.toNode = H ℓ.1)
    (m m' : (GNode LG.garden.tree → Mom d) → ℂ) (hm : ∀ k, m k = m' k)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    Stage1WNoVine.kernelNodeW L γ δ LG A m up s k₀ nroot nfl = kernelLeavesW L γ δ LG H up s k₀ nroot nfl m' := by
  unfold Stage1WNoVine.kernelNodeW kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  rw [hm]
  congr 2
  exact Finset.prod_congr rfl fun ℓ hℓ => by rw [hA ℓ hℓ]

/-! ## P* lemma 1 at the leaves (from `VineB.pstar_couple`/`pstar_chain`) -/

section PStar
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)

theorem pstar_couple_leaf (u : CLBlock S) {p : SourcePair S} (hp : p ∈ clRegionalPairs hS u.atoms)
    (ℓ : GLeaf (nativeCoupleLayered D hS layer hLayer p).garden.tree) :
    nativeCoupleProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) p ℓ.1 =
      layerProfiles (nativeCoupleLayered D hS layer hLayer p) (fun q => h q u.upper.1.1 u.upper.1.1) ℓ.1 := by
  rw [layerProfiles_leaf]
  have hmem : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeCoupleProfiles, hmem, dite_true]
  set E := nativeCoupleForest D hS p
  set e : GLeaf (D.forest hS) := Comb.RootedSubforest.leafEmbedding E ℓ
  have he : (E.nodeEmbedding ⟨ℓ.1, hmem⟩).1 = e.1 := rfl
  obtain ⟨hf, hs⟩ := regionalPair_trees hS u hp
  have hroot : ∀ i : Fin 2, (E.root i).1.1 = u.upper.1.1 := by
    intro i
    fin_cases i
    · show (inflatedPosition S D.tree (p.firstLeaf hS).toNode).1 = _
      rw [inflatedPosition_index]; exact hf
    · show (inflatedPosition S D.tree (p.secondLeaf hS).toNode).1 = _
      rw [inflatedPosition_index]; exact hs
  have h1 : e.1.1 = u.upper.1.1 := hroot ℓ.1.1
  have hmemE : e ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) E :=
    Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, rfl⟩
  have hcl := (nativeCoupleForest_closed D hS p e hmemE).2
  obtain ⟨i, hi⟩ := (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) E _).mp hcl
  have h2 : ((D.garden hS).pair e).1.1 = u.upper.1.1 := by
    rw [← hroot i]; exact hi.1.symm
  rw [he]
  exact typeProfiles_leaf_eq (layeredReconstruction D hS layer hLayer) h e _ h1 h2

theorem pstar_chain_leaf (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms)
    (ℓ : GLeaf (nativeChainLayered D hS layer hLayer v).garden.tree)
    (hℓ : ℓ ∈ inputLeaves (nativeChainLayered D hS layer hLayer v).garden) :
    nativeChainProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) v ℓ.1 =
      layerProfiles (nativeChainLayered D hS layer hLayer v) (fun q => h q u.upper.1.1 u.upper.1.1) ℓ.1 := by
  rw [layerProfiles_leaf]
  have hl : ℓ.1.2 ≠ (D.tree v).lonePath := fun he => not_mem_inputLeaves_chain_lone D v ℓ he hℓ
  set T := Reg.decodedTree (D.tree v) (nodeSign S.sig v.1)
  have hd := Reg.decodedTree_decodes (D.tree v) (nodeSign S.sig v.1)
  have hl' : (T.pair ℓ).1.2 ≠ (D.tree v).lonePath := by
    intro he
    have hm : T.mark (T.pair ℓ) ≠ none := by
      rw [hd.2.1 (T.pair ℓ), if_pos he]; decide
    have hp := (T.pair_eq_iff _).mpr hm
    have hp2 : ℓ = T.pair ℓ := (T.pair_pair ℓ).symm.trans hp
    rw [← hp2] at he
    exact hl he
  set e := chainContextLeaf D hS v ⟨ℓ, hl⟩
  set e' := chainContextLeaf D hS v ⟨T.pair ℓ, hl'⟩
  have hpair : (D.garden hS).pair e = e' :=
    chainContext_pair D hS v ℓ hl e e' (chainContextLeaf_toNode D hS v _) (chainContextLeaf_toNode D hS v _)
  have hvt : v.1.1 = u.upper.1.1 := real_tree u ((branch_real_iff u v).mpr hv)
  have h1 : e.1.1 = u.upper.1.1 := by
    show (inflatedPosition S D.tree v.toNode).1 = _
    rw [inflatedPosition_index]; exact hvt
  have h2 : ((D.garden hS).pair e).1.1 = u.upper.1.1 := by
    rw [hpair]
    show (inflatedPosition S D.tree v.toNode).1 = _
    rw [inflatedPosition_index]; exact hvt
  have hmem : ℓ.1.2 ∈ ((Reg.decodedTree (D.tree v) (nodeSign S.sig v.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeChainProfiles, hmem, dite_true]
  exact typeProfiles_leaf_eq (layeredReconstruction D hS layer hLayer) h e _ h1 h2

end PStar

/-! ## The regional rows of `slotFnNW … (fwNode …)` -/

section Regional
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ)
  (gT : Fin w → Mom d → ℂ)

/-- The frontier-weighted slot family of a reconstruction, at the type-family profile `h`. -/
abbrev slotFW : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ :=
  Stage1WNoVine.slotFnNW D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h)
    (fwNodeV (layeredReconstruction D hS layer hLayer) p gT) layer hLayer

theorem couple_root_tree (u : CLBlock S) {pr : SourcePair S} (hp : pr ∈ clRegionalPairs hS u.atoms) (i : Fin 2) :
    ((nativeCoupleForest D hS pr).root i).1.1 = u.upper.1.1 := by
  obtain ⟨hf, hs⟩ := regionalPair_trees hS u hp
  fin_cases i
  · show (inflatedPosition S D.tree (pr.firstLeaf hS).toNode).1 = _
    rw [inflatedPosition_index]; exact hf
  · show (inflatedPosition S D.tree (pr.secondLeaf hS).toNode).1 = _
    rw [inflatedPosition_index]; exact hs

theorem couple_root_nonroot (u : CLBlock S) {pr : SourcePair S} (hp : pr ∈ clRegionalPairs hS u.atoms) (i : Fin 2) :
    ((nativeCoupleForest D hS pr).root i).1.2 ≠ [] := by
  have hf : Mole.IsInternalLeaf S u.atoms (pr.firstLeaf hS) := by
    classical
    exact (Finset.mem_filter.mp hp).2
  have hs := (second_internal_iff hS u.atoms pr).mpr hf
  obtain ⟨_, hn1, _, _⟩ := hf
  obtain ⟨_, hn2, _, _⟩ := hs
  fin_cases i
  · exact LFTwist.inflatedPosition_nonroot S D.tree _ hn1
  · exact LFTwist.inflatedPosition_nonroot S D.tree _ hn2

/-- **The regional couple slot is the pinned `coupleLeavesTop`.** -/
theorem slotFW_regional_couple (u : CLBlock S) {pr : SourcePair S} (hp : pr ∈ clRegionalPairs hS u.atoms)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFW D hS layer hLayer L γ δ h p gT (.inl pr) ts k =
      coupleLeavesTop L γ δ p (gT u.upper.1.1) (coupleRootParents p D hS layer hLayer pr 0)
        (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
        (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) (fun q => h q u.upper.1.1 u.upper.1.1))
        (ts 0) (ts 1) k := by
  show Stage1WNoVine.kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer pr)
      (fun a => typeProfiles (layeredReconstruction D hS layer hLayer) h ((nativeCoupleForest D hS pr).nodeEmbedding a).1)
      (fun k' => ∏ a, fwNodeV (layeredReconstruction D hS layer hLayer) p gT
        ((nativeCoupleForest D hS pr).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 = _
  unfold coupleLeavesTop
  refine kernelNodeW_eq_kernelLeavesW L γ δ _ _ _ (fun ℓ _ => ?_) _ _ (fun k' => ?_) _ _ _ _ _
  · rw [← pstar_couple_leaf D hS layer hLayer h u hp ℓ]
    have hmem : ℓ.1.2 ∈ ((nativeCoupleGarden D hS pr).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeCoupleProfiles, hmem, dite_true]
    rfl
  · unfold rowTopWeight
    refine Finset.prod_congr rfl fun a _ => ?_
    have := fwNodeV_embed (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer pr)
      (fun a => (nativeCoupleForest D hS pr).nodeEmbedding a) (fun j => ((nativeCoupleForest D hS pr).root j).1)
      (fun a => rfl) (fun a => rfl) (couple_root_nonroot D hS u hp) p gT a (k' a)
    rw [this, couple_root_tree D hS u hp]
    have hq : (fun j => (layeredReconstruction D hS layer hLayer).parentLayer p
        ((nativeCoupleForest D hS pr).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer pr).garden.tree j))) =
        ![coupleRootParents p D hS layer hLayer pr 0, coupleRootParents p D hS layer hLayer pr 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hq]

theorem chain_root_nonroot (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (hva : v ≠ u.upper) :
    (inflatedPosition S D.tree v.toNode).2 ≠ [] := by
  obtain ⟨hn, -⟩ := real_parent u ((branch_real_iff _ _).mpr hv)
    (fun he => hva (Subtype.ext (congrArg (fun x : GNode S.tree => x.1) he)))
  exact LFTwist.inflatedPosition_nonroot S D.tree _ hn

/-- **The regional chain slot is the pinned `treeLeavesTop`.** -/
theorem slotFW_regional_chain (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (hva : v ≠ u.upper)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFW D hS layer hLayer L γ δ h p gT (.inr v) ts k =
      treeLeavesTop L γ δ p (gT u.upper.1.1) (treeRootParent p D hS layer hLayer v)
        (nativeChainLayered D hS layer hLayer v)
        (layerProfiles (nativeChainLayered D hS layer hLayer v) (fun q => h q u.upper.1.1 u.upper.1.1))
        (ts 0) (ts 1) k := by
  show Stage1WNoVine.kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer v)
      (fun a => typeProfiles (layeredReconstruction D hS layer hLayer) h (chainContextNode D hS v a).1)
      (fun k' => ∏ a, fwNodeV (layeredReconstruction D hS layer hLayer) p gT (chainContextNode D hS v a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 = _
  unfold treeLeavesTop
  refine kernelNodeW_eq_kernelLeavesW L γ δ _ _ _ (fun ℓ hℓ => ?_) _ _ (fun k' => ?_) _ _ _ _ _
  · rw [← pstar_chain_leaf D hS layer hLayer h u hv ℓ hℓ]
    have hmem : ℓ.1.2 ∈ ((Reg.decodedTree (D.tree v) (nodeSign S.sig v.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeChainProfiles, hmem, dite_true]
    rfl
  · unfold rowTopWeight
    refine Finset.prod_congr rfl fun a _ => ?_
    have := fwNodeV_embed (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer v)
      (fun a => chainContextNode D hS v a) (fun _ => inflatedPosition S D.tree v.toNode)
      (fun a => rfl) (fun a => rfl) (fun _ => chain_root_nonroot D u hv hva) p gT a (k' a)
    rw [this, inflatedPosition_index, real_tree u ((branch_real_iff u v).mpr hv)]
    have hq : (fun j => (layeredReconstruction D hS layer hLayer).parentLayer p
        (chainContextNode D hS v (GNode.root (nativeChainLayered D hS layer hLayer v).garden.tree j))) =
        ![treeRootParent p D hS layer hLayer v] := by
      funext j
      fin_cases j
      rfl
    rw [hq]

end Regional

/-! ## Coherent rows: the crossing factor times main's starred kernel (supplement Lemma 5.1) -/

section Coherent
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- The crossing factor of a couple with root parent layers `q, q'`. -/
def coupleCross {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (k : Mom d) : ℂ :=
  if q' < p ∧ q = p then g k else if q < p ∧ q' = p then g k else 1

/-- The crossing factor of a tree with root parent layer `q` and lone-leaf layer `q'`. -/
def treeCross {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (k : Mom d) : ℂ :=
  if q' < p ∧ q = p then g k else 1

theorem coupleRootParents_eq_clkLayer (p : ℕ) (pr : SourcePair S) (i : Fin 2) :
    coupleRootParents p D hS layer hLayer pr i =
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl pr) i) := by
  have hcl : argSrc hS (.inl pr) i =
      clkOfNode S (if i = 0 then (pr.firstLeaf hS).toNode else (pr.secondLeaf hS).toNode) := by
    fin_cases i <;> simp [argSrc]
  rw [hcl]
  exact parentLayer_inflated D hS layer hLayer p _ _ (couple_root_node D hS pr i)

theorem treeRootParent_eq_clkLayer (p : ℕ) (v : GBranch S.tree) :
    treeRootParent p D hS layer hLayer v =
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr v) 0) := by
  have hcl : argSrc hS (.inr v) 0 = clkOfNode S v.toNode := by simp [argSrc]
  rw [hcl]
  exact parentLayer_inflated D hS layer hLayer p _ _ (tree_root_node D hS v)

/-- Every branch of tree `j` lies at a layer at most that of the root of tree `j` (copy of O4′'s
`branch_layer_le_root`). -/
theorem branch_layer_le_rootV {w : ℕ} (LG : LayeredGarden w) (b : GBranch LG.garden.tree) :
    LG.layer b.toNode ≤ LG.layer (GNode.root LG.garden.tree b.1.1) := by
  obtain ⟨r, hr1, hr2, hle⟩ := FlowerP7.layer_le_root LG b.1.2.length b rfl
  have e : r.toNode = GNode.root LG.garden.tree b.1.1 := Subtype.ext (Prod.ext hr1 hr2)
  rw [← e]
  exact hle

/-- Every node lies at a layer at most that of its root (copy of O4′'s `node_layer_le_root`). -/
theorem node_layer_le_rootV {w : ℕ} (LG : LayeredGarden w) (x : GNode LG.garden.tree) :
    LG.layer x ≤ LG.layer (GNode.root LG.garden.tree x.1.1) := by
  by_cases hx : x.1.2 = []
  · have e : x = GNode.root LG.garden.tree x.1.1 := Subtype.ext (Prod.ext rfl hx)
    rw [← e]
  · have e := Reg.Skeleton.child_parent x hx
    have h1 : LG.layer x ≤ LG.layer (x.parent hx).toNode := by
      conv_lhs => rw [← e]
      exact LG.isLayering.1 _ _
    exact h1.trans (branch_layer_le_rootV LG (x.parent hx))

theorem layer_le_parentLayer {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (hlay : ∀ x, LG.layer x ≤ p)
    (a : GNode LG.garden.tree) : LG.layer a ≤ LG.parentLayer p a := by
  unfold LayeredGarden.parentLayer
  split_ifs with h
  · exact hlay a
  · have e := Reg.Skeleton.child_parent a h
    have h1 : LG.layer a ≤ LG.layer (a.parent h).toNode := by
      conv_lhs => rw [← e]
      exact LG.isLayering.1 _ _
    exact h1

theorem coupleRootParents_le (p : ℕ) (hlay : ∀ x, layer x ≤ p) (pr : SourcePair S) (i : Fin 2) :
    coupleRootParents p D hS layer hLayer pr i ≤ p := by
  unfold coupleRootParents LayeredGarden.parentLayer
  split_ifs
  · exact le_rfl
  · exact hlay _

theorem treeRootParent_le (p : ℕ) (hlay : ∀ x, layer x ≤ p) (v : GBranch S.tree) :
    treeRootParent p D hS layer hLayer v ≤ p := by
  unfold treeRootParent LayeredGarden.parentLayer
  split_ifs
  · exact le_rfl
  · exact hlay _

/-- **Coherent couple rows**: `coupleLeavesTop = crossing · KQstar`. -/
theorem coupleLeavesTop_coherent {L γ δ : ℝ} (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (hlay : ∀ x, layer x ≤ p) (pr : SourcePair S) (hinc : coupleIncoh D hS layer hLayer pr = 0)
    (g : Mom d → ℂ) (F : ℕ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    coupleLeavesTop L γ δ p g (coupleRootParents p D hS layer hLayer pr 0)
        (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
        (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) F) t s k =
      coupleCross p g (coupleRootParents p D hS layer hLayer pr 0) (coupleRootParents p D hS layer hLayer pr 1) k *
        KQstar L γ δ F (nativeCoupleLayered D hS layer hLayer pr) t s k := by
  have hcoh := couple_coherent_at D hS layer hLayer p hcan pr hinc
  rw [← coupleRootParents_eq_clkLayer D hS layer hLayer p pr 0, ← coupleRootParents_eq_clkLayer D hS layer hLayer p pr 1] at hcoh
  have hf := CohTrunk.coupleLeavesTopR_factor hcoh (coupleRootParents_le D hS layer hLayer p hlay pr 0)
    (coupleRootParents_le D hS layer hLayer p hlay pr 1) (fun _ => g) L γ δ
    (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) F) t s k
  have e1 : coupleLeavesTop L γ δ p g (coupleRootParents p D hS layer hLayer pr 0)
      (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
      (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) F) t s k =
      coupleLeavesTopR L γ δ p (fun _ => g) (coupleRootParents p D hS layer hLayer pr 0)
        (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
        (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) F) t s k := by
    unfold coupleLeavesTop coupleLeavesTopR
    rfl
  have e2 : coupleLeavesTopR L γ δ p (fun _ _ => 1) (coupleRootParents p D hS layer hLayer pr 0)
      (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
      (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) F) t s k =
      KQstar L γ δ F (nativeCoupleLayered D hS layer hLayer pr) t s k := by
    unfold coupleLeavesTopR KQstar
    rw [kernelLeavesW_one _ _ _ _ _ _ _ _ _ _ _ (fun k' => rowTopWeightR_one' p _ _ k'),
      kernelLeaves_layerProfiles]
  rw [e1, hf, e2]
  rfl

/-- **Coherent tree rows**: `treeLeavesTop = crossing · KTstar`. -/
theorem treeLeavesTop_coherent {L γ δ : ℝ} (p : ℕ) (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    (hlay : ∀ x, layer x ≤ p) (v : GBranch S.tree) (hinc : treeIncoh D hS layer hLayer v = 0)
    (g : Mom d → ℂ) (F : ℕ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    treeLeavesTop L γ δ p g (treeRootParent p D hS layer hLayer v) (nativeChainLayered D hS layer hLayer v)
        (layerProfiles (nativeChainLayered D hS layer hLayer v) F) t s k =
      treeCross p g (treeRootParent p D hS layer hLayer v) (layer (D.coreBranch hS v).toNode) k *
        KTstar L γ δ F (nativeChainLayered D hS layer hLayer v) t s k := by
  have hcoh := tree_coherent_at D hS layer hLayer p hcan v hinc
  rw [← treeRootParent_eq_clkLayer D hS layer hLayer p v] at hcoh
  have hq' : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr v) 1) =
      layer (D.coreBranch hS v).toNode := by simp [argSrc, clkLayer]
  rw [hq'] at hcoh
  have hq'q : layer (D.coreBranch hS v).toNode ≤ treeRootParent p D hS layer hLayer v := by
    obtain ⟨_, hX, _, H, a, _, _, _, _, _, _, hlone, hlay'⟩ := hcoh
    let y : GNode (nativeChainLayered D hS layer hLayer v).garden.tree := ⟨(0, (D.tree v).lonePath), by
      show (D.tree v).lonePath ∈ ((nativeChainLayered D hS layer hLayer v).garden.tree 0).nodes
      rw [hX.1]; exact Links.lonePath_mem_plug _ _ _⟩
    have h1 : (nativeChainLayered D hS layer hLayer v).layer y = layer (D.coreBranch hS v).toNode :=
      (hlay' y).trans hlone
    have h2 := node_layer_le_rootV (nativeChainLayered D hS layer hLayer v) y
    have h3 := layer_le_parentLayer (layeredReconstruction D hS layer hLayer) p hlay
      (chainContextNode D hS v (GNode.root (nativeChainLayered D hS layer hLayer v).garden.tree 0))
    rw [← h1]
    exact h2.trans h3
  unfold treeLeavesTop KTstar
  rw [kernelLeavesW_const' L γ δ _ _ _ _ _ _ _ _
      (treeCross p g (treeRootParent p D hS layer hLayer v) (layer (D.coreBranch hS v).toNode) k)
      (fun κ => by
        have := CohTrunk.rowTopAgreementTree p (treeRootParent p D hS layer hLayer v) (layer (D.coreBranch hS v).toNode)
          (D.tree v) (nativeChainLayered D hS layer hLayer v) hq'q (treeRootParent_le D hS layer hLayer p hlay v)
          hcoh g L k κ
        rw [this]; rfl),
    kernelLeaves_layerProfiles]

end Coherent

end WaveTurbulence.Flower.Stage1WVine
