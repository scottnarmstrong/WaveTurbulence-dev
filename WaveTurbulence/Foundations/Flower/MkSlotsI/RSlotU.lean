/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlot
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne

/-! # B3s-HELPER7 WP6 (R-slot, unit slots): inside a unit the general kernel is B3's frontier-weighted kernel

**`unitSlot_plain`**: for a slot `sl` of the skeleton of a member `y` that is not the image `Φ_y.iota s'` of a `G_sb`
slot (a slot inside a unit of `y`), the member's general slot kernel is B3's frontier-weighted slot kernel
`Stage1WVine.slotFW y.1.data y.1.plain (stateLayer y.1) _ L γ δ h p (fun j => frontierG (Rf j)) sl`.

* such a slot is not retained (`slotRet_iota`), so its skeleton nodes are interior unit nodes, children of unit
  atoms (`real_parent`); it is not a cap pair (a cap root is a skeleton root, retained with its partner);
* no native branch is pinned (`fixCap_none_of`): no capped flower parent (non-cap natives), no garden root, the core of
  the chain branch and the cores above the native tops are unit atoms (α's `member_unit_not_cfp`);
* no native node is on the capped stem (γ's retention `kindMember_spec`: the stem stays in retained slots), so
  `genΘs ≡ 1` (`genNode_eq_one_unit`); without stem filters `genNode_none`;
* then β's relaxed kernel is the pinned kernel `slotFnNWF` without pins (`slotFnGWFRL_plain`: `kDomainR_none`,
  `kernelNodeWR_one_eq`), which is `slotFW` off the cap pairs (α's `nonCap_slotFn_eq_slotFW`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore WaveTurbulence.Flower.MkSlots.IntCapT

namespace WaveTurbulence.Flower.MkSlotsI

theorem kernelNodeWR_Θ_one {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Dom : Set (GBranch LG.garden.tree → ℝ)) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (Θn : GenDecoration LG.garden d nroot nfl → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) (h : ∀ κ, Θn κ = 1) :
    MkSlotsB.kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl Θn fix =
      MkSlotsB.kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl (fun _ => 1) fix := by
  have e : Θn = fun _ => 1 := funext h
  rw [e]

/-- **Without native pins and with trivial per-node factors, β's relaxed kernel is the pinned kernel without pins.** -/
theorem slotFnGWFRL_plain {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (L : ℝ)
    (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (γ δ : ℝ) (H : LeafProfiles w d)
    (W : GNode (D.forest hS) → Mom d → ℂ) (fixG : GBranch (D.forest hS) → Option ℝ) (sl : ReplacementSlot S)
    (hF : MkSlots.fixNative D hS fixG sl = fun _ => none)
    (hΘ : ∀ (a : NativeNode D sl) (v : ℝ), genNode D hS layer hLayer J L σ kSel Rs (nativeNodeAt D hS sl a) v = 1) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG sl =
      slotFnNWF D hS L γ δ H W layer hLayer (fun _ => none) sl := by
  funext ts k
  cases sl with
  | inl q =>
    rw [slotFnGWFRL_inl_eq]
    unfold kerC
    rw [hF]
    refine (kernelNodeWR_Θ_one L γ δ _ _ _ _ _ _ _ _ _ (fun κ => Finset.prod_eq_one fun a _ => hΘ a _)).trans ?_
    exact MkSlotsB.kernelNodeWR_one_eq L γ δ _ _ _ _ _ 0 k _ 0 _
      (fun τ _ => Set.ext_iff.mp (MkSlotsB.kDomainR_none _ _ _ _ _) τ)
  | inr b =>
    rw [slotFnGWFRL_inr_eq]
    unfold kerT
    rw [hF]
    refine (kernelNodeWR_Θ_one L γ δ _ _ _ _ _ _ _ _ _ (fun κ => Finset.prod_eq_one fun a _ => hΘ a _)).trans ?_
    exact MkSlotsB.kernelNodeWR_one_eq L γ δ _ _ _ _ _ (ts 1) k _ 0 _
      (fun τ _ => Set.ext_iff.mp (MkSlotsB.kDomainR_none _ _ _ _ _) τ)

/-- The stem node weight is `1` off the capped stem. -/
theorem genNW_off_stem {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (z : GNode LG.garden.tree) (hz : ¬ MkSlotsT.OnStemAddr LG J z.1) (x : ℝ) :
    genNW LG J L σ kSel Rs z x = 1 := by
  by_cases hb : z.1.2 ∈ (LG.garden.tree z.1.1).branching
  · unfold genNW
    rw [dite_eq_left hb, ite_eq_right]
    rintro ⟨j, hj⟩
    exact hz (MkSlotsT.onStemAddr_of_mem_stemSetCap hj)
  · exact genNW_not_branch LG J L σ kSel Rs z hb x

/-- A non-retained skeleton node is an interior node of a unit: a child of one of its atoms. -/
theorem interior_parent {w : ℕ} {S : Garden w} {Ju : Type} {blk : Ju → CLBlock S} (x : GNode S.tree)
    (hx : ¬ Ret blk x) :
    ∃ j, x ∈ clRealizationNodes S (blk j).atoms ∧ ∃ hn : x.1.2 ≠ [], x.parent hn ∈ (blk j).atoms := by
  unfold Ret at hx
  push Not at hx
  obtain ⟨j, h1, h2⟩ := hx
  exact ⟨j, h1, real_parent (blk j) h1 h2⟩

/-- The attached node of a skeleton node is a garden root iff the node is a skeleton root. -/
theorem attached_root_iff_skel {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (ν : GNode S.tree) : (attachedNode D hS ν).1.2 = [] ↔ ν.1.2 = [] := by
  constructor
  · intro h
    by_contra hn
    exact inflatedPosition_nonroot S D.tree ν hn h
  · intro h
    have he : ν = GNode.root S.tree ν.1.1 := Subtype.ext (Prod.ext rfl h)
    show (inflatedPosition S D.tree ν).2 = []
    rw [he, inflatedPosition_root]

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hGeoA hGeoY hrepUP in
/-- **Inside a unit the general slot kernel is B3's frontier-weighted slot kernel.** -/
theorem unitSlot_plain {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (hstem : Stage1MKGate.StemDep σ kSel → Stage1MKGate.CleanPt J a)
    (sl : ReplacementSlot y.1.skeleton) (hsl : ∀ s', (memShape a mk y hy).iota y.1.plain hG s' ≠ sl) :
    MkSlotsB.slotFnGWFRL y.1.data y.1.plain L γ δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) sl =
      Stage1WVine.slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ h p
        (fun j => frontierG (Rf j)) sl := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  have hnr : ¬ MkSlotsT.SlotRet y.1.plain (blk := fun j => unitClBlock (y.2 j)) sl := fun h' => by
    obtain ⟨s', hs'⟩ := slotRet_iota (memShape a mk y hy) y.1.plain hG sl h'
    exact hsl s' hs'
  -- the cores of unit atoms are not capped flower parents
  have hunit : ∀ (ν : GNode y.1.skeleton.tree) (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
      (hn : ν.1.2 ≠ []), ν.parent hn ∈ (unitClBlock (y.2 j)).atoms →
      rcOf LGy J (attachedNode y.1.data y.1.plain ν) = none := by
    intro ν j hn hp
    rw [rcOf_attached y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J, dite_eq_left hn,
      ite_eq_right (member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j _ hp)]
  -- the slot is not a cap pair
  have hnc : ∀ q, sl = Sum.inl q → ¬ IsCapPair y.1.skeleton y.1.plain J q := by
    rintro q rfl hq
    apply hnr
    have hroot : ∀ ℓ : GLeaf y.1.skeleton.tree, ℓ.1.1 ∈ J → Ret (fun j => unitClBlock (y.2 j)) ℓ.toNode := by
      intro ℓ hℓ j
      left
      rw [leaf_mem_clRealizationNodes]
      rintro ⟨-, hn, -⟩
      have hj : y.1.data.forest y.1.plain ℓ.1.1 = TTree.leaf := hcapY _ hℓ
      have hsk := IntGeo.root_mem_leaves (D := y.1.data) (hS := y.1.plain) hj
      exact hn (leaf_prefix_node_eq hsk (TTree.leaves_subset_nodes _ ℓ.2) List.nil_prefix).symm
    rcases hq with h1 | h2
    · have r1 := hroot _ h1
      refine ⟨r1, ?_⟩
      rw [← MkSlotsT.firstLeaf_pair y.1.plain q]
      exact MkSlotsT.ret_pair_leaf r1
    · have r2 := hroot _ h2
      refine ⟨?_, r2⟩
      rw [← Represents.pair_second y.1.plain q]
      exact MkSlotsT.ret_pair_leaf r2
  -- no native branch is pinned
  have hF : MkSlots.fixNative y.1.data y.1.plain (fixCap LGy J pat t s) sl = fun _ => none := by
    funext qb
    show fixCap LGy J pat t s (MkSlotsB.nativeBr y.1.data y.1.plain sl qb) = none
    cases sl with
    | inl q =>
      have hq := hnc q rfl
      -- both leaves are interior
      have hleaf : ∀ c : Fin 2, ¬ Ret (fun j => unitClBlock (y.2 j))
          (if c = 0 then q.firstLeaf y.1.plain else q.secondLeaf y.1.plain).toNode := by
        intro c hc
        apply hnr
        fin_cases c
        · exact ⟨hc, by rw [← MkSlotsT.firstLeaf_pair y.1.plain q]; exact MkSlotsT.ret_pair_leaf hc⟩
        · refine ⟨?_, hc⟩
          rw [← Represents.pair_second y.1.plain q]
          exact MkSlotsT.ret_pair_leaf hc
      have hrootE : ∀ c, (nativeCoupleForest y.1.data y.1.plain q).root c = attachedNode y.1.data y.1.plain
          (if c = 0 then q.firstLeaf y.1.plain else q.secondLeaf y.1.plain).toNode := by
        intro c
        fin_cases c <;> rfl
      have hnJ : ∀ c, (fun c => ((nativeCoupleForest y.1.data y.1.plain q).root c).1.1) c ∉ J := by
        intro c hc
        apply hq
        fin_cases c
        · left
          have e := (inflatedPosition_index y.1.skeleton y.1.data.tree (q.firstLeaf y.1.plain).toNode)
          exact e ▸ hc
        · right
          have e := (inflatedPosition_index y.1.skeleton y.1.data.tree (q.secondLeaf y.1.plain).toNode)
          exact e ▸ hc
      have hfp : ∀ b, ¬ capT_IsFP
          (nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) q)
          (fun c => ((nativeCoupleForest y.1.data y.1.plain q).root c).1.1) J b := by
        rintro b ⟨l, ⟨-, hl⟩, -⟩
        exact hnJ _ hl
      have hB : MkSlotsB.nativeBr y.1.data y.1.plain (.inl q) qb =
          capT_bemb LGy (nativeCoupleForest y.1.data y.1.plain q) (nativeCoupleForest_closed y.1.data y.1.plain q)
            ⟨qb.1, qb.2⟩ := rfl
      rw [hB]
      refine MkSlotsB.fixCap_none_of J pat t s _ ?_ ?_ ?_ ?_
      · exact fun hc => hfp _ ((capT_cfp_iff LGy _ _ J _ (fun _ => rfl) _).mp hc)
      · intro _ h0
        have h1 := ((root_bemb_iff LGy _ _ _).mp h0).2
        obtain ⟨j, -, hn, -⟩ := interior_parent _ (hleaf qb.1.1)
        rw [hrootE] at h1
        exact hn ((attached_root_iff_skel y.1.data y.1.plain _).mp h1)
      · intro _ hpar
        obtain ⟨c, hc, -⟩ := (par_bemb_iff LGy _ _ J _).mp hpar
        exact hfp c hc
      · intro i _ hch
        rcases (ch_bemb_iff LGy _ _ J _ i).mp hch with ⟨c, hc, -⟩ | ⟨-, hrc⟩
        · exact hfp c hc
        · obtain ⟨j, -, hn, hp⟩ := interior_parent _ (hleaf qb.1.1)
          rw [hrootE, hunit _ j hn hp] at hrc
          exact absurd hrc (by simp)
    | inr β =>
      have hβ : ¬ Ret (fun j => unitClBlock (y.2 j)) β.toNode := hnr
      obtain ⟨j, hreal, hn, hp⟩ := interior_parent _ hβ
      have hβa : β ∈ (unitClBlock (y.2 j)).atoms := (branch_mem_clRealizationNodes β).mp hreal
      refine MkSlotsB.fixCap_none_of J pat t s _ ?_ ?_ ?_ ?_
      · exact cfp_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J β hcapY qb
      · intro _ h0
        have h1 := ((root_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) β qb).mp h0).2
        exact hn ((attached_root_iff_skel y.1.data y.1.plain _).mp h1)
      · intro _ hpar
        have h2 := ((par_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J β hcapY
          qb).mp hpar).2
        exact member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j β hβa h2
      · intro i _ hch
        have h2 := ((ch_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J β hcapY
          qb i).mp hch).2
        unfold chRC at h2
        rw [hunit _ j hn hp] at h2
        exact absurd h2 (by simp)
  -- no native node is on the capped stem
  have hΘ : ∀ (a' : NativeNode y.1.data sl) (v : ℝ),
      genNode y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs
        (nativeNodeAt y.1.data y.1.plain sl a') v = 1 := by
    intro a' v
    by_cases hsd : Stage1MKGate.StemDep σ kSel
    · have hc := hstem hsd
      unfold genNode
      split_ifs
      · rfl
      · refine genNW_off_stem LGy J L σ kSel Rs _ (fun hon => hnr ?_) v
        have h4 := (MkSlotsT.kindMember_spec a mk y hy J hcapA hcapY hc hon).2.2.2
        rwa [slotOf_nativeNodeAt] at h4
    · obtain ⟨hσ, hk⟩ := stemDep_none hsd
      subst hσ hk
      exact genNode_none _ _ _ _ J L Rs _ v
  rw [slotFnGWFRL_plain y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs γ δ _ _ _ sl
    hF hΘ]
  rw [IntGeo.slotFnNWF_congr y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ _ _ _ _
    (fun _ => none) (fixCap LGy J (fun _ => FixPat.plain) t s) sl (fun _ => rfl) (fun _ _ => rfl)
    (IntGeo.fixNative_fixCap_none y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY t s sl
      hnc).symm]
  exact nonCap_slotFn_eq_slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY L γ δ p t s h
    roots Rf dag sl hnc

end Class

end WaveTurbulence.Flower.MkSlotsI
