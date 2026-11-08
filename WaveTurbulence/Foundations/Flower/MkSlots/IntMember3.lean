/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember2
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapM
public import WaveTurbulence.Foundations.Flower.MkSlots.PVBInteg

/-! # B3s MK-SLOTS (integration, member identity 3): the member's pinned skeleton value as a mode sum

The combined outer family of the α piece: B3's frontier-weighted family `fam₀` on the slots of `G_sb` that are not cap
pairs, one cap superposition `pc q` (from `CapSlotObligation`) on each cap pair `q` (`capFam`). For a member `y` of
the run class, its pinned skeleton value (`member_skelVal`) is the sum over the modes of the combined family of the
pinned outer values of `G_sb` (`outerValMμ` against `fixMeasure` of the piece's pins, decoration weight `ZwG`), with
`y`'s own unit kernels `unitRecenteredFW` (`member_hasSum`).

Route: the cap swap `skelValF_capSwap` (the member's cap slot kernels at the cap momentum are the representative's,
`member_capSlot`, i.e. the values of the cap superpositions) and `nonCap_slotFn_eq_slotFW` turn the member's pinned
slot family into the swapped B3 family `capSwap slotFW capFnY`; the pinned VINE-B♯ `hasSum_skelValF_outerValMμ` with
B3's regional bound (`memberRBMk`, `RegBound.capSwap`), B3's slot data on the non-cap slots (`memShape_slotFW`) and the
cap pieces on the cap slots; the pins and the unit interiors by R-core (`member_fixCap`, `member_fix_unit`), the unit
kernels by `unitKernelMG_capSwap` and B3's `member_ker_eqWMk`, the shape data by B3's `memShape_*`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.Flower.V5W

namespace WaveTurbulence.Flower.MkSlots.IntMember

open WaveTurbulence.Flower.MkSlots.IntRest WaveTurbulence.Flower.MkSlots.IntCore
  WaveTurbulence.Flower.MkSlots.IntCapM

/-! ### The combined family -/

section Fam
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (J : Finset (Fin w))

/-- The cap slots of `G_sb`. -/
def IsCapSlot (sl : ReplacementSlot G) : Prop := ∃ q, sl = Sum.inl q ∧ IsCapPair G hG J q

/-- The cap superpositions as a family of slot pieces (empty on chain slots). -/
def capPieces (pc : SourcePair G → SlotPiece d) : ReplacementSlot G → SlotPiece d
  | .inl q => pc q
  | .inr _ => SlotPiece.empty d

/-- **The combined outer slot family of the α piece.** -/
def capFam (fam₀ : SlotFam G d) (pc : SourcePair G → SlotPiece d) : SlotFam G d :=
  combineFam fam₀ (IsCapSlot hG J) (capPieces pc)

/-- The member's cap function: on the image of a `G_sb` pair, the value of its cap piece. -/
def capFnY {S : Garden w} (hS : S.IsPlain) {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
    (Φ : SpliceShape blk G) (pc : SourcePair G → SlotPiece d) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) :
    SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ := fun q' =>
  if h : ∃ q : SourcePair G, pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG)) = q' then (pc h.choose).val else Fs (.inl q')

theorem capFnY_iota {S : Garden w} (hS : S.IsPlain) {Ju : Type} [Fintype Ju] [DecidableEq Ju]
    {blk : Ju → CLBlock S} (Φ : SpliceShape blk G) (pc : SourcePair G → SlotPiece d)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (q : SourcePair G) :
    capFnY hG hS Φ pc Fs (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) = (pc q).val := by
  unfold capFnY
  have h : ∃ q' : SourcePair G, pairOfLeaf S hS (Φ.leaf (q'.firstLeaf hG)) = pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG)) :=
    ⟨q, rfl⟩
  rw [dif_pos h]
  have he : h.choose = q := by
    have h1 := h.choose_spec
    have h2 : Φ.iota hS hG (.inl h.choose) = Φ.iota hS hG (.inl q) := congrArg Sum.inl h1
    exact Sum.inl_injective (Φ.iota_inj hS hG h2)
  rw [he]

end Fam

/-- On a cap pair, the pinned slot kernel with the chain weight is the one with the capped node weight. -/
theorem slotFn_chainW_cap {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (p : ℕ) (s : ℝ)
    (J : Finset (Fin w)) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (H : LeafProfiles w d)
    (fix : GBranch (D.forest hS) → Option ℝ) (q : SourcePair S) (hq : IsCapPair S hS J q) :
    slotFnNWF D hS L γ δ H (chainW D hS layer hLayer L γ δ p s J Rf dag) layer hLayer fix (.inl q) =
      slotFnNWF D hS L γ δ H (capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) layer hLayer
        fix (.inl q) := by
  refine IntGeo.slotFnNWF_congr D hS layer hLayer L γ δ H H _ _ fix fix (.inl q) (fun _ => rfl) (fun a x => ?_) rfl
  have hin := IntGeo.inCapNative_nativeNodeAt D hS J q hq a
  unfold chainW capNodeW
  rw [if_pos hin]

/-! ### The member's mode sum -/

/-- The single-type profile family of a profile `h` bounded by `b`. -/
def uFam (P : WTParams) {w : ℕ} (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) : TypeFamily P w where
  ι := Unit
  fin := inferInstance
  sign := fun _ => 1
  h := fun _ => h
  b := fun _ => b.toNNReal
  sign_abs_le := fun _ => by norm_num

/-- **The member's pinned skeleton value is the mode sum of the pinned outer values of `G_sb`.** -/
theorem member_hasSum (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ} {kind : Bool}
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (J : Finset (Fin (2 * R))) (t s : ℝ) (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p)
    (fam₀ : SlotFam (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d)
    (hexp₀ : ∀ s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
      ∀ x, HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts)
        (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ h p
          (fun j => frontierG (Rf j))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
          ts x))
    (pc : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → SlotPiece P.d)
    (hpc : ∀ q, IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q →
      ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
          (.inl q)),
      (pc q).val ts (latticePoint P.L (roots (capTreeOf _ hG J q))) =
        capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
            (.inl q)) ts (latticePoint P.L (roots (capTreeOf _ hG J q))))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hGeoY : CapGeo y.1.layered J p) (hcanY : IsCanonGC (p + 1) y.1.layered)
    (selSk : GenDecoration y.1.skeleton P.d roots 0 → Prop)
    (hZ : ∀ κ, (if selSk κ then (1 : ℝ) else 0) = ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots
      dag ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ)) :
    HasSum (fun ξ : ∀ sl, (capFam hG J fam₀ pc).Λ sl => ((modeWt (capFam hG J fam₀ pc) ξ : ℝ) : ℂ) *
        outerValMμ (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t)
          (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
          (fun z => (ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots dag z : ℂ)) hG
          (fixMeasure (fixAt J (fun _ => FixPat.plain) t s a (mk a.prime)))
          (fun sl => (capFam hG J fam₀ pc).a sl (ξ sl)) (fun sl => (capFam hG J fam₀ pc).m sl (ξ sl))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          (fun j lam t' k => unitRecenteredFW p
            (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1))
            none y.1 (y.2 j) P.L P.γ P.δ
            (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
            0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)))
      (skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk
        (slotFnNWF y.1.data y.1.plain P.L P.γ P.δ
          (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
            h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (stateLayer y.1) (stateLayer_isLayering y.1)
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
            (fun _ => FixPat.plain) t s))
        (fixCore y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
            (fun _ => FixPat.plain) t s))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf := fun j hj => by
    have hroot := IntGeo.root_mem_leaves (D := y.1.data) (hS := y.1.plain) (hcapY j hj)
    cases ht' : y.1.skeleton.tree j with
    | leaf => rfl
    | node l m r =>
      rw [ht'] at hroot
      simp [TTree.leaves, TTree.nil_notMem_pre] at hroot
  have hlay : ∀ x, stateLayer y.1 x ≤ p := fun x => hGeoR.layer_le x
  have htt : ∀ j, (fun _ => t : Fin (2 * R) → ℝ) j ∈ Set.Icc (p : ℝ) (p + 1) :=
    fun _ => ⟨(hs.1.trans hs.2).le, ht⟩
  -- the member's pinned slot family and its cap swap
  set Fs := slotFnNWF y.1.data y.1.plain P.L P.γ P.δ
    (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
      roots)
    (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
    (stateLayer y.1) (stateLayer_isLayering y.1)
    (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (fun _ => FixPat.plain) t s) with hFs
  set Fcap := capFnY hG y.1.plain (memShape a mk y hy) pc Fs with hFcap
  set FW := slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ h p
    (fun j => frontierG (Rf j)) with hFW
  -- step 1: the cap swap
  have hswap : skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk Fs
        (fixCore y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
            (fun _ => FixPat.plain) t s)) =
      skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk
        (capSwap y.1.plain J Fs Fcap)
        (fixCore y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
            (fun _ => FixPat.plain) t s)) := by
    refine skelValF_capSwap y.1.plain J hcapS y.1.data P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk Fs
      Fcap _ (slotBox p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) y.1.plain)
      (fun τ hτ sl => slotTs_mem_slotBox p _ y.1.plain _ htt τ (coreTimeDomainW_subset_spliced _ _ _ hτ) sl) ?_
    intro qy hqy ts hts
    by_cases hex : ∃ q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G,
        pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG)) = qy
    · obtain ⟨q, rfl⟩ := hex
      have hqG := (isCapPair_iota (memShape a mk y hy) y.1.plain hG J q).mp hqy
      rw [hFcap, capFnY_iota, capTreeOf_iota, zero_add]
      have hts' : ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
            (.inl q)) := by
        rw [← memShape_slotBox a mk y hy hG (.inl q)]
        exact hts
      rw [hpc q hqG ts hts', ← member_capSlot a mk y hy hG J hcapA hrepU hGeoA hGeoR q hqG P.L P.γ P.δ t s h roots Rf
        dag]
      have e4 := slotFn_chainW_cap y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J
        Rf dag (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
          h P.L roots)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          (fun _ => FixPat.plain) t s) _ hqy
      exact (congrFun (congrFun e4 ts) _).symm
    · rw [hFcap]
      unfold capFnY
      rw [dif_neg hex]
  -- step 2: off the cap slots the member's family is B3's
  have hcong : capSwap y.1.plain J Fs Fcap = capSwap y.1.plain J FW Fcap :=
    capSwap_congr y.1.plain J Fs FW Fcap fun sl hsl =>
      nonCap_slotFn_eq_slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY P.L P.γ P.δ p t
        s h roots Rf dag sl hsl
  rw [hswap, hcong]
  -- step 3: the pinned VINE-B♯
  have hbB : ∀ (i : (uFam P h b).ι) q j j', q ≤ p →
      SNormR (40 * P.d) (40 * P.d) ((uFam P h b).h i q j j') ≤ ENNReal.ofReal ((uFam P h b).b i : ℝ) := by
    intro i q j j' hq
    show SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal (b.toNNReal : ℝ)
    rw [Real.coe_toNNReal b hb]
    exact hB q hq j j'
  have hg : ∀ j x, ‖frontierG (d := P.d) (Rf j) x‖ ≤ 1 := by
    intro j x
    unfold frontierG
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases Rf j with
    | none => simp
    | some r =>
      simp only [Option.elim]
      rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
      exact XChain.ProductCut.chi0_le_one _
  have RB := RegBound.capSwap y.1.plain J hcapS Fcap
    (memberRBMk a mk y (uFam P h b) hd1 hL1 0 hlay hbB (fun j => frontierG (Rf j)) 1 le_rfl hg ())
  have hexp : ∀ sl, ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      a.prime.prime.1
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG sl),
      ∀ x, HasSum (fun l => ((capFam hG J fam₀ pc).w sl l : ℂ) * (capFam hG J fam₀ pc).a sl l x *
        fsPhase ((capFam hG J fam₀ pc).m sl l) ts)
        (capSwap y.1.plain J FW Fcap ((memShape a mk y hy).iota y.1.plain hG sl) ts x) := by
    intro sl ts hts x
    by_cases hc : IsCapSlot hG J sl
    · obtain ⟨q, rfl, hq⟩ := hc
      have hqy := (isCapPair_iota (memShape a mk y hy) y.1.plain hG J q).mpr hq
      show HasSum _ ((if IsCapPair y.1.skeleton y.1.plain J _ then Fcap _ else FW (.inl _)) ts x)
      rw [if_pos hqy, hFcap, capFnY_iota]
      exact hasSum_combineFam_of_cap fam₀ (IsCapSlot hG J) (capPieces pc) (.inl q) ⟨q, rfl, hq⟩ ts x
    · have hnot : capSwap y.1.plain J FW Fcap ((memShape a mk y hy).iota y.1.plain hG sl) =
          FW ((memShape a mk y hy).iota y.1.plain hG sl) := by
        rcases sl with q | c
        · show (if IsCapPair y.1.skeleton y.1.plain J _ then Fcap _ else FW (.inl _)) = _
          rw [if_neg (fun h' => hc ⟨q, rfl, (isCapPair_iota (memShape a mk y hy) y.1.plain hG J q).mp h'⟩)]
          rfl
        · rfl
      rw [hnot, hFW, memShape_slotFW a mk y hy hG h P.L P.γ P.δ p (fun j => frontierG (Rf j)) sl]
      exact hasSum_combineFam_of_not fam₀ (IsCapSlot hG J) (capPieces pc) sl hc ts x (hexp₀ sl ts hts x)
  have hU : ∀ j, ∀ c ∈ inter (fun j => unitClBlock (y.2 j)) j,
      fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          (fun _ => FixPat.plain) t s) c = none := fun j c hc =>
    member_fix_unit a mk y hy hG J hcapA hcapY hrepU t s j c (mem_inter.mp hc).1
  have hW : ∀ c v, fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          (fun _ => FixPat.plain) t s) c = some v →
      v ≠ (stateLayer y.1 (y.1.data.coreBranch y.1.plain c).toNode : ℝ) ∧
        v ≠ (stateLayer y.1 (y.1.data.coreBranch y.1.plain c).toNode : ℝ) + 1 := by
    intro c v hv
    have hv' := (fixCap_plain _ J t s _).symm.trans hv
    by_cases hcfp : IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)) J (y.1.data.coreBranch y.1.plain c)
    · rw [if_pos hcfp] at hv'
      have hvs : v = s := (Option.some.inj hv').symm
      have hlp := layer_capFlowerParent hGeoR hcfp
      have hlp' : stateLayer y.1 (y.1.data.coreBranch y.1.plain c).toNode = p := hlp
      rw [hlp', hvs]
      exact ⟨ne_of_gt hs.1, ne_of_lt (lt_of_lt_of_le hs.2 ht)⟩
    · rw [if_neg hcfp] at hv'
      exact absurd hv' (by simp)
  have key := hasSum_skelValF_outerValMμ (memShape a mk y hy) RB (source_disjMk a mk y hy) hG hL0 P.γ P.δ y.1.data
    (stateLayer y.1) (fun _ => t) selSk (ZwG a mk J P.L P.γ P.η hL0.ne' roots dag) hZ (capFam hG J fam₀ pc)
    (fun sl => slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG sl))
    hexp (memShape_hbox a mk y hy hG (fun _ => t) htt) _ hU hW
  -- step 4: the shape data, the pins and the unit kernels of the representative
  have hfix : (fun c => fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          (fun _ => FixPat.plain) t s) ((memShape a mk y hy).br c)) =
      fixAt J (fun _ => FixPat.plain) t s a (mk a.prime) :=
    funext fun c => member_fixCap a mk y hy hG J hcapA hcapY hrepU t s c
  rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy, hfix,
    unitKernelMG_capSwap y.1.plain J hcapS y.1.data _ Fcap P.L P.γ P.δ (stateLayer y.1) 0,
    member_ker_eqWMk a mk y hy P.L P.γ P.δ _ 0 (fun j => frontierG (Rf j)) hcanY hlay] at key
  exact key

end WaveTurbulence.Flower.MkSlots.IntMember
