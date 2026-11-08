/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMul2

/-! # B3s MK-SLOTS (cap slots): the multiplier identity and the D3-ready kernel

* `fw_prod`: the frontier node weights of the paired tree are INC-TOP's star weight of the frontier cutoff on the
  frontier set `frontS`;
* `capPairFactor_one`, `capRoot_weight`: the cap pair carries the factor `1` at the cap momentum;
* **`m1_eq`**: on coset decorations at the cap momentum, `m1 = capC0 · starWeight · capInd`;
* **`capTermKer_m1`**: the slot's protected kernel is `capC0` times the kernel with D3's multiplier. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.ProtCut

namespace WaveTurbulence.Flower.MkSlots

/-- `kernelProt` is linear in its multiplier. -/
theorem kernelProt_const_mul (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (c : ℂ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H (fun K => c * m K) up s fix k₀ nroot nfl = c * kernelProt L γ δ LG H m up s fix k₀ nroot nfl := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum]
  unfold protSummand
  simp only [mul_assoc]
  rw [tsum_mul_left]
  ring

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-- The frontier nodes of the paired tree. -/
def frontS (p : ℕ) : Finset (GNode (K.Dq layer hLayer).T1.garden.tree) :=
  Finset.univ.filter fun a1 => (K.e1 layer hLayer a1).1.2 ≠ [] ∧
    (layeredReconstruction D hS layer hLayer).layer (K.e1 layer hLayer a1) < p ∧
    (layeredReconstruction D hS layer hLayer).parentLayer p (K.e1 layer hLayer a1) = p

theorem fw_prod {d : ℕ} (p : ℕ) (Rf : Fin w → Option ℝ) (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    ∏ a1, fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) (K.e1 layer hLayer a1)
        (K' a1) =
      IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' := by
  unfold IncTop.starWeight frontS
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun a1 _ => ?_
  have hst : IncTop.topStar (fun _ => frontierG (Rf K.u.1)) a1 (IncTop.starMomenta K' a1) =
      frontierG (Rf K.u.1) (K' a1) := by
    unfold IncTop.topStar
    rw [IncTop.starMomenta_zero]
  rw [hst]
  unfold fwNode topPsi
  rw [K.e1_fst layer hLayer a1]
  by_cases h1 : (K.e1 layer hLayer a1).1.2 ≠ []
  · by_cases h2 : (layeredReconstruction D hS layer hLayer).layer (K.e1 layer hLayer a1) < p ∧
        (layeredReconstruction D hS layer hLayer).parentLayer p (K.e1 layer hLayer a1) = p
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem norm_starWeight_le {d : ℕ} (p : ℕ) (Rf : Fin w → Option ℝ)
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) :
    ‖IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K'‖ ≤ 1 := by
  unfold IncTop.starWeight
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
  unfold IncTop.topStar frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases Rf K.u.1 with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

/-! ### The cap pair -/

theorem pairTrees_fst {w : ℕ} (G : Garden w) (a : Fin w × Path) : (pairTrees G a).1 = a.1 := by
  unfold pairTrees
  split_ifs <;> rfl

theorem cRoot_val :
    ((nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree
      K.c)).1 = ((inflatedPosition S D.tree K.cleaf.toNode).1, (inflatedPosition S D.tree K.cleaf.toNode).2 ++ []) := by
  show (((nativeCoupleForest D hS q).root K.c).1.1, ((nativeCoupleForest D hS q).root K.c).1.2 ++ []) = _
  rw [K.root_c]
  rfl

include hGeo in
theorem cRoot_path :
    ((nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree
      K.c)).1.2 = [] := by
  set z := (nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)
  have h1 : z.1.1 = K.cleaf.1.1 := by
    rw [K.cRoot_val layer hLayer]; exact inflatedPosition_index S D.tree _
  have h2 := z.2
  have hc : D.forest hS K.cleaf.1.1 = TTree.leaf := hGeo.cap_leaf _ K.cJ
  rw [h1, hc] at h2
  simpa [TTree.nodes] using h2

include hGeo in
theorem capRoot_weight {d : ℕ} (L γ δ s : ℝ) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (x : Mom d) :
    capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag
      ((nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree
        K.c)) x = 1 := by
  set z := (nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)
  have hz : z.1.2 = [] := K.cRoot_path layer hLayer hGeo
  have hfw : fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) z x = 1 := by
    unfold fwNode
    rw [if_neg (fun h => h hz)]
  unfold capNodeW
  rw [hfw, one_mul]
  cases dag with
  | none => rfl
  | some cc =>
    unfold dagNodeW
    simp only [Option.elim]
    have hn1 : ¬ ∃ b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree, b.toNode = z ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
      rintro ⟨b, hbz, -⟩
      have hb := b.2
      have e : b.1 = z.1 := congrArg Subtype.val hbz
      have h1 : z.1.1 = K.cleaf.1.1 := by
        rw [K.cRoot_val layer hLayer]; exact inflatedPosition_index S D.tree _
      rw [e, h1, hGeo.cap_leaf _ K.cJ] at hb
      simp [TTree.branching] at hb
    have hn2 : ¬ ∃ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i : Fin 3), b.child i = z ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
      rintro ⟨b, i, hbz, -⟩
      have e : (b.child i).1.2 = z.1.2 := congrArg (fun y : GNode (D.forest hS) => y.1.2) hbz
      rw [hz] at e
      simp [GBranch.child] at e
    rw [dif_neg hn1, dif_neg hn2, mul_one]

include hGeo in
theorem capPairFactor_one {d : ℕ} (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ))
    (κ : GenDecoration (K.Dq layer hLayer).T1.garden d (fun _ => 0) 0) :
    CapG.capPairFactor (K.Dq layer hLayer) (Hq (q := q) layer hLayer
        (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots))
      (cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1) = 1 := by
  unfold CapG.capPairFactor
  refine Finset.prod_eq_one fun ℓ hℓ => ?_
  have hcap := (Finset.mem_filter.1 hℓ).2
  have hlone : cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1 ((K.Dq layer hLayer).ρ ℓ.toNode) =
      latticePoint L (roots K.cleaf.1.1) := by
    rcases (K.Dq layer hLayer).leaf_cases ℓ with h0 | h0 | ⟨ℓ1, hne, rfl⟩
    · rw [h0, (K.Dq layer hLayer).ρ_ℓ0]; exact (K.Dq layer hLayer).lone_coset L _ κ
    · rw [(K.Dq layer hLayer).ρ_c ℓ.toNode (fun he => (K.Dq layer hLayer).ne (he.symm.trans (congrArg Prod.fst h0)))]
      exact (K.Dq layer hLayer).lone_coset L _ κ
    · exfalso
      rcases hcap with hc | hc
      · exact (K.Dq layer hLayer).ne (Finset.mem_singleton.1 hc)
      · rw [(K.Dq layer hLayer).pair_ιL ℓ1 hne] at hc
        exact (K.Dq layer hLayer).ne (Finset.mem_singleton.1 hc)
  rw [hlone]
  show ((Hq (q := q) layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots) ℓ.1 (latticePoint L (roots K.cleaf.1.1)) : ℝ) : ℂ) = 1
  rw [Hq_def, capProfiles_leaf]
  beta_reduce
  rcases (K.Dq layer hLayer).leaf_cases ℓ with h0 | h0 | ⟨ℓ1, hne, rfl⟩
  · -- the capped flower
    subst h0
    have hv : ((nativeCoupleForest D hS q).nodeEmbedding (K.Dq layer hLayer).ℓ0.toNode).1 = K.flower.1 := K.emb_ι layer hLayer (K.Dq layer hLayer).lone1
    rw [hv]
    have hpt : pairTrees (layeredReconstruction D hS layer hLayer).garden K.flower.1 = (K.u.1, K.cleaf.1.1) := by
      have := pairTrees_leaf (D.garden hS) K.flower
      rw [K.lone K.flower rfl, inflatedPosition_index] at this
      exact this
    have hu : K.u.1 ∉ J := (K.isCapFlower layer hLayer).1
    unfold anchProfiles
    rw [hpt]
    simp only
    rw [if_neg hu, if_pos K.cJ, if_pos rfl, Complex.ofReal_one]
  · -- the cap root
    have hv : ((nativeCoupleForest D hS q).nodeEmbedding ℓ.toNode).1.1 = K.cleaf.1.1 := by
      have : ℓ.toNode = GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c :=
        Subtype.ext h0
      rw [this, K.cRoot_val layer hLayer]
      exact inflatedPosition_index S D.tree _
    unfold anchProfiles
    rw [pairTrees_fst, hv, if_pos K.cJ, if_pos rfl, Complex.ofReal_one]
  · exfalso
    rcases hcap with hc | hc
    · exact (K.Dq layer hLayer).ne (Finset.mem_singleton.1 hc)
    · rw [(K.Dq layer hLayer).pair_ιL ℓ1 hne] at hc
      exact (K.Dq layer hLayer).ne (Finset.mem_singleton.1 hc)

include hGeo in
/-- **The multiplier identity.** -/
theorem m1_eq {d : ℕ} (L γ δ s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (κ : GenDecoration (K.Dq layer hLayer).T1.garden d (fun _ => 0) 0) :
    K.m1 layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag)
        (cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1) =
      K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
        (IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1)))
          (cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1) *
        (K.capInd layer hLayer dag
          (cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1) : ℂ)) := by
  set K' := cosetDecoration (K.Dq layer hLayer).T1.garden L (latticePoint L (roots K.cleaf.1.1)) κ.1 with hK'
  unfold m1
  rw [hK', K.capPairFactor_one layer hLayer hGeo h L roots κ, ← hK', mul_one,
    (K.Dq layer hLayer).prod_nodes, K.capRoot_weight layer hLayer hGeo L γ δ s Rf dag, one_mul]
  simp only [(K.Dq layer hLayer).ρ_ι]
  unfold capNodeW
  rw [Finset.prod_mul_distrib, K.fw_prod layer hLayer p Rf, hK',
    K.dag_prod_coset layer hLayer hGeo L γ δ s _ dag κ]
  ring

include hGeo in
/-- **The slot's protected kernel with D3's multiplier.** -/
theorem capTermKer_m1 {d : ℕ} (L γ δ s t : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (H1 : LeafProfiles 1 d) (x : ℝ) :
    capTermKer L γ δ (K.Dq layer hLayer) H1
        (K.m1 layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
          (capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag)) s t
        (latticePoint L (roots K.cleaf.1.1)) x =
      K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
        capTermKer L γ δ (K.Dq layer hLayer) H1
          (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
            (K.capInd layer hLayer dag K' : ℂ)) s t (latticePoint L (roots K.cleaf.1.1)) x := by
  unfold capTermKer
  rw [kernelProt_congr_m L γ δ _ H1 _ (fun K' => K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
      (IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
        (K.capInd layer hLayer dag K' : ℂ))) _ 0 _ _ _ _ (fun κ => K.m1_eq layer hLayer hGeo L γ δ s h roots Rf dag κ)]
  exact kernelProt_const_mul L γ δ _ H1 _ _ _ 0 _ _ _ _

end CapSide

end WaveTurbulence.Flower.MkSlots
