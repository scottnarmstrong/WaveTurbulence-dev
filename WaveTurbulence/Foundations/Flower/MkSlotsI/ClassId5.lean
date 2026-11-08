/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId4
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm1

/-! # B3s-HELPER7 ClassId (part 5): the centre-indexed mode form of a member of the run class

* `relaxPinsS_fixCore`: the skeleton pins `fixCore … (fixCap …)` satisfy β's `RelaxPinsS` (from the garden
  `RelaxPins` of the pattern pins, `relaxPins_fixCap`);
* **`member_classForm`**: for a member `y` of the run class at the unit marking `mk` (`mk a.prime = classMk mkF a`),
  the frozen class summand of `y.1.layered` is `sgnGen · Σ'_X Σ'_ξ modeWt · outerValMμD G_sb … (domOf πM) …
  (ZwC · chiX X) … (famX (fam₀Of sd _) (famCOfData sd) X) … (unitRecenteredFWL of y)`, together with the summability,
  integrability and decoration-summability inputs of the class sum (`weightedClassFactorizationμDLX`). Route:
  `member_skelValG` (MemY2) → `member_Zs_eq` + `skelValWZRL_const_mul` → VBC4's `hasSum_skelValWZRL_centred_cons`
  (box `boxG`, consumed momenta `ConsG`/`ConsCG`, `hexp₀`/`hexpC'` from `SlotDataOK` + RSlot, `hMC` from the masses)
  → the class-common shape data (B3's `memShape_*`, β's `member_fixCap_pat`, the lower bounds `hlbbr`, the unit kernels
  `member_unitKernel`). The class-commonness of the lower bounds (`hlbbr`, `hlbclk`) and `hlbU` are hypotheses here
  (proved in `ClassIdL*`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW fixCore recLG IsCapPair capTreeOf fixAt outerValMμD
  fixMeasure)
open WaveTurbulence.Flower.MkSlots.IntMember (restIndO capConstO)
open WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlotsB (outerIntegrandMD)
open WaveTurbulence.Flower.V5W2L (unitRecenteredFWL)

namespace WaveTurbulence.Flower.MkSlotsI

/-- **β's `RelaxPinsS` for the skeleton pins of the pattern pins** (pins at `s`, or `t` at a root; strict descendants
are pinned at `s`). -/
theorem relaxPinsS_fixCore {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))
    (pat : Fin w → FixPat) {t s : ℝ} (hst : s ≤ t)
    (hRP : MkSlotsB.RelaxPins (layeredReconstruction D hS layer hLayer).layer (fun _ => t)
      (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)) :
    MkSlotsB.RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) (fun _ => t)
      (fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)) where
  val b v hv := ⟨(hRP.val _ v hv).1, (hRP.val _ v hv).2.1, (hRP.val _ v hv).2.2⟩
  mono x y v v' hx hy hxy := by
    have hxn : x.1.2 ≠ [] := by
      intro h0
      have := hxy.length_lt
      rw [h0] at this
      simp at this
    have hcx : (D.coreBranch hS x).1.2 ≠ [] := fun h0 =>
      hxn ((MkSlotsB.core_root_iff D hS x).mp h0).1
    have hv : v = s := by
      rcases MkSlotsB.fixCap_value (show fixCap (layeredReconstruction D hS layer hLayer) J pat t s
          (D.coreBranch hS x) = some v from hx) with h | ⟨-, h0, -⟩
      · exact h
      · exact absurd h0 hcx
    rw [hv]
    exact (fixCap_le_t hst (show fixCap (layeredReconstruction D hS layer hLayer) J pat t s
      (D.coreBranch hS y) = some v' from hy)).1

/-- The domain of the general piece at a marked set, written out. -/
theorem domOf_pieceGenAt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (tt : Fin (2 * R) → ℝ) :
    splicedTimeDomainFix (stSt a.prime.skeleton a.totalSigma Mk).G (a.normalizedPiece 0 Mk).layer tt
        (fixAt J pat t s a Mk) ∩ MkSlotsB.lbDomR (lbGenAt J pat t s a Mk) =
      domOf (pieceGenAt P J pat t s kSel σ Rs a Mk dag) tt := rfl

section Member

variable (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) (hη0 : 0 ≤ P.η) {Kg : ℕ → ℝ → ℝ} {C : ℝ}
  {R p : ℕ} {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
  (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
  (π : PcA R p (objKind (2 * R)) A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
  (hout : a.outputs (p := p) (kind := objKind (2 * R)) mk = a.outputs (p := p) (kind := objKind (2 * R)) mkF)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel σ : Fin (2 * R) → Option ℕ)
  (Rs : Fin (2 * R) → ℝ) (t s : ℝ) (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
  (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb0 : 0 ≤ b)
  (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
  (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
  (hset : mk a.prime = classMk mkF a) (hRs : ∀ j, P.L ≤ Rs j) (hGeoA : CapGeo (recLG a) J p)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)
  (hstem : ¬ StemDep σ kSel ∨ CleanPt J a) (hok : selOK (recLG a) J kSel = 1)
  (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ) → SlotDatum P.d)
  (hsd : SlotDataOK Kg P C p a J pat t s kSel σ Rs roots h b Rf dag (mk a.prime) sd)
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p (objKind (2 * R)) mk)
  (hGeoY : CapGeo y.1.layered J p) (hPatY : CapPatValid y.1.layered J pat p)
  (hrootY : ∀ j ∉ J, ∃ ℓ : GLeaf y.1.layered.garden.tree, IsCapFlower y.1.layered J ℓ ∧ ℓ.1.1 = j)
  (hcanY : IsCanonGC (p + 1) y.1.layered)
  (hlbbr : ∀ c, MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
      ((memShape a mk y hy).br c) = lbGenAt J pat t s a (mk a.prime) c)
  (hlbclk : ∀ (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2)
    (by' : GBranch y.1.skeleton.tree) (ba : GBranch a.prime.skeleton.tree),
    argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inr by' →
    argSrc a.prime.prime.1 ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i = .inr ba →
    MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s by' =
      MkSlotsB.lbS a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) s ba)
  (hlbU : ∀ j, ∀ x ∈ VineB.inter (fun j => unitClBlock (y.2 j)) j,
    MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s x = none)

include hL1 hd1 hη0 hFT hπ hout hs ht hb0 hB hsub hset hRs hGeoA hrepUP hstem hok hsd hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU in
/-- **The centre-indexed mode sums of a member** (VBC4 at the member, with the class-common shape data): the per-`X`
mode sums of the outer values of `G_sb` with the member's unit kernels `unitRecenteredFWL` sum to the member's weighted
relaxed pinned skeleton value at the weight `ZwC ∘ resDec`. -/
theorem member_hasSumX :
    HasSum (fun X : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ) => ∑' ξ : ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t',
      ((modeWt (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ : ℝ) : ℂ) *
      outerValMμD (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t) (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t))
        (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges (fun z => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z * chiX P.L 0 X z) hG
        (fixMeasure (fixAt J pat t s a (mk a.prime)))
        (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j lam t' k => unitRecenteredFWL p
          (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
            j).upper.1.1))
          (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
          0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)))
      (skelValWZRL (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1)
        (fun κ => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ))
        ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
          (stateLayer y.1) (stateLayer_isLayering y.1) (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s),
        genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩
        (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hst : s < t := hs.2
  have htt : t ∈ Set.Icc (p : ℝ) (p + 1) := ⟨(hs.1.trans hs.2).le, ht⟩
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by rw [hspec]; exact hGeoY
  have hPatR : CapPatValid (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat p := by rw [hspec]; exact hPatY
  have hrootR : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).garden.tree, IsCapFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J ℓ ∧ ℓ.1.1 = j := by
    rw [hspec]; exact hrootY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf := fun j hj =>
    MkSlots.IntAsm.skel_tree_leaf y.1.data y.1.plain (hcapY j hj)
  have hlay : ∀ x, stateLayer y.1 x ≤ p := hGeoR.layer_le
  have hstem' : StemDep σ kSel → CleanPt J a := fun hsd' => hstem.resolve_left (not_not.mpr hsd')
  have hRP := relaxPins_fixCap hGeoR hPatR hrootR hs ht
  have hP := relaxPinsS_fixCore y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat hst.le hRP
  have hfix : (fun c => (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) ((memShape a mk y hy).br c)) = fixAt J pat t s a (mk a.prime) :=
    funext fun c => MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c
  have hlbf : (fun c => (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) ((memShape a mk y hy).br c)) = lbGenAt J pat t s a (mk a.prime) := funext hlbbr
  have hker := member_unitKernel a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP
    hstem hok hcanY hlay
  have RB := memberRBG a mk y J P hL1 hd1 pat t s kSel σ Rs h b hb0 hB roots Rf dag hlay
    (member_regAgree a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP hstem hok)
  have hZw : ∀ z, ‖ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z‖ ≤ 1 :=
    norm_ZwC_le P J pat t s kSel σ Rs a dag hL1 mkF hsub hRs mk hset roots
  have hbox := member_hbox a mk y hy hG J pat t s hrepUP hcapA hcapY hst htt hRP hlbclk
  have hexp₀ := member_hexp₀ a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hexpC := member_hexpC a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hcons := member_hcons a mk y hy hG J P.L roots hcapS
  have hU := MkSlotsB.hU_member_pat a mk y hy hG J hcapA hcapY pat t s hrepUP
  obtain ⟨MC, hMC⟩ := exists_hMC hη0 hsd
  have hvbc := hasSum_skelValWZRL_centred_cons (memShape a mk y hy) RB (source_disjMk a mk y hy) hG hL0 P.γ P.δ
    y.1.data (stateLayer y.1) (fun _ => t) (fun κ => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ))
    (ZwC P J pat t s kSel σ Rs a dag hL1 mk roots) hZw (fun κ => rfl) (fam₀Of sd hsd.supp) (famCOfData sd)
    (boxG p a J pat t s (mk a.prime)) (ConsG P.L a J roots (mk a.prime)) (fun κ s' _ => hcons κ s') hexp₀
    (ConsCG P.L) (fun κ c => ⟨_, rfl⟩) hexpC MC hMC _ _ hU hlbU hP hbox
  rw [memShape_lay_eq a mk y hy, hfix, hlbf, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy, hker, domOf_pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag]
    at hvbc
  exact hvbc

include hL1 hd1 hη0 hFT hπ hout hs ht hb0 hB hsub hset hRs hGeoA hrepUP hstem hok hsd hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU in
/-- **The member value in the centre-indexed mode form**: the frozen class summand of a member is
`sgnGen · Σ'_X Σ'_ξ modeWt · outerValMμD … (its unit kernels)`. -/
theorem member_val :
    kernelKgenSel P.L P.γ P.δ y.1.layered (fixCap y.1.layered J pat t s) (offCap y.1.layered J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag y.1.layered) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π y.1.layered) =
      sgnGen J P.L P.γ P.δ s kSel Rs a mk roots dag * ∑' X : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ), ∑' ξ : ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t',
        ((modeWt (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ : ℝ) : ℂ) *
      outerValMμD (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t) (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t))
        (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges (fun z => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z * chiX P.L 0 X z) hG
        (fixMeasure (fixAt J pat t s a (mk a.prime)))
        (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j lam t' k => unitRecenteredFWL p
          (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
            j).upper.1.1))
          (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
          0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)) := by
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by rw [hspec]; exact hGeoY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
  have hsk := member_skelValG P hL1 hd1 hFT π a hπ hout hG J pat kSel σ Rs t s hs ht h b hb0 hB roots Rf dag hcapA
    hrepU hstem y hy hGeoY hPatY hrootY
  rw [show (fun κ => if selAnd
        (fun κS => selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
        (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag) κ then
      genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
        (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ else 0) =
      fun κ => cGen J kSel Rs a mk *
        ZwC P J pat t s kSel σ Rs a dag hL1 mk roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) from
      funext fun κ => member_Zs_eq a mk y hy hG J P hL1 pat t s kSel σ Rs mkF hsub hRs hset roots dag hcapA hrepU
        hGeoA hGeoY hstem κ, skelValWZRL_const_mul] at hsk
  rw [hsk, (member_hasSumX P hL1 hd1 hη0 hFT π a hπ hout hG J pat kSel σ Rs t s hs ht h b hb0 hB roots Rf dag hsub
    hset hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU).tsum_eq, sgnGen_eq,
    mul_assoc]

include hL1 hd1 hη0 hFT hπ hout hs ht hb0 hB hsub hset hRs hGeoA hrepUP hstem hok hsd hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU in
/-- The `ξ`-summability of a member's per-`X` mode sum. -/
theorem member_summξ (X : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ)) :
    Summable (fun ξ : ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t' =>
      ((modeWt (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ : ℝ) : ℂ) *
      outerValMμD (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t) (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t))
        (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges (fun z => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z * chiX P.L 0 X z) hG
        (fixMeasure (fixAt J pat t s a (mk a.prime)))
        (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j lam t' k => unitRecenteredFWL p
          (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
            j).upper.1.1))
          (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
          0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hst : s < t := hs.2
  have htt : t ∈ Set.Icc (p : ℝ) (p + 1) := ⟨(hs.1.trans hs.2).le, ht⟩
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by rw [hspec]; exact hGeoY
  have hPatR : CapPatValid (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat p := by rw [hspec]; exact hPatY
  have hrootR : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).garden.tree, IsCapFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J ℓ ∧ ℓ.1.1 = j := by
    rw [hspec]; exact hrootY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf := fun j hj =>
    MkSlots.IntAsm.skel_tree_leaf y.1.data y.1.plain (hcapY j hj)
  have hlay : ∀ x, stateLayer y.1 x ≤ p := hGeoR.layer_le
  have hstem' : StemDep σ kSel → CleanPt J a := fun hsd' => hstem.resolve_left (not_not.mpr hsd')
  have hRP := relaxPins_fixCap hGeoR hPatR hrootR hs ht
  have hP := relaxPinsS_fixCore y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat hst.le hRP
  have hfix : (fun c => (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) ((memShape a mk y hy).br c)) = fixAt J pat t s a (mk a.prime) :=
    funext fun c => MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c
  have hlbf : (fun c => (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) ((memShape a mk y hy).br c)) = lbGenAt J pat t s a (mk a.prime) := funext hlbbr
  have hker := member_unitKernel a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP
    hstem hok hcanY hlay
  have RB := memberRBG a mk y J P hL1 hd1 pat t s kSel σ Rs h b hb0 hB roots Rf dag hlay
    (member_regAgree a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP hstem hok)
  have hZw : ∀ z, ‖ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z‖ ≤ 1 :=
    norm_ZwC_le P J pat t s kSel σ Rs a dag hL1 mkF hsub hRs mk hset roots
  have hbox := member_hbox a mk y hy hG J pat t s hrepUP hcapA hcapY hst htt hRP hlbclk
  have hexp₀ := member_hexp₀ a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hexpC := member_hexpC a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hcons := member_hcons a mk y hy hG J P.L roots hcapS
  have hU := MkSlotsB.hU_member_pat a mk y hy hG J hcapA hcapY pat t s hrepUP
  have hmod := summable_modes_centred_cons (memShape a mk y hy) RB (source_disjMk a mk y hy) hG hL0 P.γ P.δ
    y.1.data (stateLayer y.1) (fun _ => t) (fun κ => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ))
    (ZwC P J pat t s kSel σ Rs a dag hL1 mk roots) hZw (fun κ => rfl) (fam₀Of sd hsd.supp) (famCOfData sd)
    (boxG p a J pat t s (mk a.prime)) (ConsG P.L a J roots (mk a.prime)) (fun κ s' _ => hcons κ s') hexp₀
    (ConsCG P.L) (fun κ c => ⟨_, rfl⟩) hexpC _ _ hU hlbU hP hbox X
  rw [memShape_lay_eq a mk y hy, hfix, hlbf, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy, hker, domOf_pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag]
    at hmod
  exact hmod

include hL1 hd1 hη0 hFT hπ hout hs ht hb0 hB hsub hset hRs hGeoA hrepUP hstem hok hsd hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU in
/-- The integrability of a member's per-mode outer integrand. -/
theorem member_integ (X : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ)) (ξ : ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t') (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) :
    Integrable (outerIntegrandMD (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t) (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t)) hG
        (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j lam t' k => unitRecenteredFWL p
          (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
            j).upper.1.1))
          (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
          0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)) z)
      (fixMeasure (fixAt J pat t s a (mk a.prime))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hst : s < t := hs.2
  have htt : t ∈ Set.Icc (p : ℝ) (p + 1) := ⟨(hs.1.trans hs.2).le, ht⟩
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by rw [hspec]; exact hGeoY
  have hPatR : CapPatValid (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat p := by rw [hspec]; exact hPatY
  have hrootR : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).garden.tree, IsCapFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J ℓ ∧ ℓ.1.1 = j := by
    rw [hspec]; exact hrootY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf := fun j hj =>
    MkSlots.IntAsm.skel_tree_leaf y.1.data y.1.plain (hcapY j hj)
  have hlay : ∀ x, stateLayer y.1 x ≤ p := hGeoR.layer_le
  have hstem' : StemDep σ kSel → CleanPt J a := fun hsd' => hstem.resolve_left (not_not.mpr hsd')
  have hRP := relaxPins_fixCap hGeoR hPatR hrootR hs ht
  have hP := relaxPinsS_fixCore y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat hst.le hRP
  have hfix : (fun c => (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) ((memShape a mk y hy).br c)) = fixAt J pat t s a (mk a.prime) :=
    funext fun c => MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c
  have hlbf : (fun c => (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) ((memShape a mk y hy).br c)) = lbGenAt J pat t s a (mk a.prime) := funext hlbbr
  have hker := member_unitKernel a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP
    hstem hok hcanY hlay
  have RB := memberRBG a mk y J P hL1 hd1 pat t s kSel σ Rs h b hb0 hB roots Rf dag hlay
    (member_regAgree a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP hstem hok)
  have hZw : ∀ z, ‖ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z‖ ≤ 1 :=
    norm_ZwC_le P J pat t s kSel σ Rs a dag hL1 mkF hsub hRs mk hset roots
  have hbox := member_hbox a mk y hy hG J pat t s hrepUP hcapA hcapY hst htt hRP hlbclk
  have hexp₀ := member_hexp₀ a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hexpC := member_hexpC a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hcons := member_hcons a mk y hy hG J P.L roots hcapS
  have hU := MkSlotsB.hU_member_pat a mk y hy hG J hcapA hcapY pat t s hrepUP
  have hint := integrable_outerIntegrandMDGW_modesR (memShape a mk y hy) RB (source_disjMk a mk y hy)
    y.1.data hG P.γ P.δ (stateLayer y.1) (fun _ => t) (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) (roots := roots) z
  rw [memShape_lay_eq a mk y hy, hfix, hlbf, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy, hker, domOf_pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag]
    at hint
  exact hint

include hL1 hd1 hη0 hFT hπ hout hs ht hb0 hB hsub hset hRs hGeoA hrepUP hstem hok hsd hy hGeoY hPatY hrootY hcanY hlbbr hlbclk hlbU in
/-- The decoration summability of a member's per-mode outer value. -/
theorem member_hsm (X : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ)) (ξ : ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t') :
    Summable (fun z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 =>
      (splicedEpsilon (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges z.1 : ℂ) *
        (ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z * chiX P.L 0 X z) *
        ∫ τ, outerIntegrandMD (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t) (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t)) hG
        (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j lam t' k => unitRecenteredFWL p
          (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
            j).upper.1.1))
          (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
          0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)) z τ
          ∂(fixMeasure (fixAt J pat t s a (mk a.prime)))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hst : s < t := hs.2
  have htt : t ∈ Set.Icc (p : ℝ) (p + 1) := ⟨(hs.1.trans hs.2).le, ht⟩
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by rw [hspec]; exact hGeoY
  have hPatR : CapPatValid (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat p := by rw [hspec]; exact hPatY
  have hrootR : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).garden.tree, IsCapFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J ℓ ∧ ℓ.1.1 = j := by
    rw [hspec]; exact hrootY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf := fun j hj =>
    MkSlots.IntAsm.skel_tree_leaf y.1.data y.1.plain (hcapY j hj)
  have hlay : ∀ x, stateLayer y.1 x ≤ p := hGeoR.layer_le
  have hstem' : StemDep σ kSel → CleanPt J a := fun hsd' => hstem.resolve_left (not_not.mpr hsd')
  have hRP := relaxPins_fixCap hGeoR hPatR hrootR hs ht
  have hP := relaxPinsS_fixCore y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat hst.le hRP
  have hfix : (fun c => (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) ((memShape a mk y hy).br c)) = fixAt J pat t s a (mk a.prime) :=
    funext fun c => MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c
  have hlbf : (fun c => (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) ((memShape a mk y hy).br c)) = lbGenAt J pat t s a (mk a.prime) := funext hlbbr
  have hker := member_unitKernel a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP
    hstem hok hcanY hlay
  have RB := memberRBG a mk y J P hL1 hd1 pat t s kSel σ Rs h b hb0 hB roots Rf dag hlay
    (member_regAgree a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY hrepUP hstem hok)
  have hZw : ∀ z, ‖ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z‖ ≤ 1 :=
    norm_ZwC_le P J pat t s kSel σ Rs a dag hL1 mkF hsub hRs mk hset roots
  have hbox := member_hbox a mk y hy hG J pat t s hrepUP hcapA hcapY hst htt hRP hlbclk
  have hexp₀ := member_hexp₀ a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hexpC := member_hexpC a mk y hy hG J hGeoA' hGeoR pat t s hrepUP kSel σ Rs roots h b Rf dag hstem' sd hsd
  have hcons := member_hcons a mk y hy hG J P.L roots hcapS
  have hU := MkSlotsB.hU_member_pat a mk y hy hG J hcapA hcapY pat t s hrepUP
  have hsm := summable_outer_decorationsGWD_modesR (memShape a mk y hy) RB (source_disjMk a mk y hy)
    y.1.data hG hL0 P.γ P.δ (stateLayer y.1) (fun _ => t) (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ
    (fun z => ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z * chiX P.L 0 X z)
    (norm_mul_chiX_le_one P.L 0 X _ hZw) (fixCore y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) (MkSlotsB.lbS y.1.data y.1.plain (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s)
  rw [memShape_lay_eq a mk y hy, hfix, hlbf, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy, hker, domOf_pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag]
    at hsm
  exact hsm

end Member

end WaveTurbulence.Flower.MkSlotsI
