/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId1
public import WaveTurbulence.Foundations.Flower.MkSlotsI.MemY2
public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlot
public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotU
public import WaveTurbulence.Foundations.Flower.MkUnitsL.MemberL
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Bridge

/-! # B3s-HELPER7 ClassId (part 2): the weight and the unit kernels of a member of the run class

For a member `y` of the run class of the representative `a` at the unit marking `mk` (`mk a.prime = classMk mkF a`):
* **`member_Zs_eq`**: the member weight `[selSk ∧ restIndO] · genZa` of `member_skelValG` is
  `cG · Zw (resDec κ)` with the class constant `cG = selOK(a) · selConst(a) · chiDNorm ^ #selR` and the `G_sb` weight
  `Zw z = pieceAtomW (pieceGenAt … (mk a.prime) dag) (coset z) · [selSkCMk z]` (CoreW's `zatom_member'`, `selOK_member`,
  `selConst_member`, MemY2's `member_selAnd_ZwG`, ClassForm's `zatomG_mul_sibIndAt`); `norm_ZwG_le`: `‖Zw‖ ≤ 1`;
* **`genTw_top_member`**: at the unit tops the top weight `genTw` of the member is B3-2's `topFilterWeightL (SURep …)`
  (CoreW's `top_member`, unit by unit, when the representative's selection exists, `selOK(a) = 1`);
* **`member_regAgree`**, **`member_unitKernel`**, `memberRBG`: the member's general slot family agrees with B3's
  `slotFWW … (memberTopW y SURep)` on the regional slots and the tops (RSlot's `unitSlot_plain`), so its unit kernels are
  `unitRecenteredFWL` (`member_ker_eqWMkL`) and B3-2's regional bound `regBoundFWW` transfers. -/

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
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW fixCore recLG sibIndAt flwAt)
open WaveTurbulence.Flower.MkSlots.IntMember (restIndO capConstO ZwG)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW slotFWW regBoundFWW memberTopW
  memberTopW_apply member_ker_eqWMkL norm_topWeightOf_le)

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## The `G_sb` weight -/

section Weight

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))

/-- **The `G_sb` decoration weight of the class**: the piece's atom weight at the coset decoration times the common
gap selection (`centreForm`'s weight without `chiX`). -/
def ZwC (hL1 : 1 ≤ P.L) (mk : Stage1Mk.MarkFn (2 * R)) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) : ℂ :=
  MkSlotsS.pieceAtomW (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag)
      (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L 0 z.1) *
    (if MkUnits.selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots z then 1 else 0)

/-- The class constant without the dagger constant: `selOK(a) · selConst(a) · chiDNorm ^ #selR`. -/
def cGen (mk : Stage1Mk.MarkFn (2 * R)) : ℂ :=
  (selOK (recLG a) J kSel : ℂ) *
    ((∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
      (chiDNorm : ℂ) ^ (selRAt J kSel a (mk a.prime)).card)

theorem sgnGen_eq (mk : Stage1Mk.MarkFn (2 * R)) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    sgnGen J P.L P.γ P.δ s kSel Rs a mk roots dag =
      capConstO a mk J P.L P.γ P.δ s roots dag * cGen J kSel Rs a mk := rfl

/-- The atom weight of the piece at a marked set equal to the class marking is bounded by `1`. -/
theorem norm_pieceAtomWAt_le (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    (k : GNode (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Mom P.d) :
    ‖MkSlotsS.pieceAtomW (pieceGenAt P J pat t s kSel σ Rs a Mk dag) k‖ ≤ 1 := by
  subst hMk
  exact MkSlotsS.norm_atomWF_le _ _
    (fun c q hq u => (MkSlotsG.filtGen_ok P J pat t s kSel σ Rs mkF a dag hsub hL hRs MkSlotsG.cθGen le_rfl c q
      hq).2.2.1 u)
    (fun k => MkSlotsG.indGen_mem J P.L σ kSel mkF a dag k) k

theorem norm_ZwC_le (hL1 : 1 ≤ P.L) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hRs : ∀ j, P.L ≤ Rs j) (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = classMk mkF a)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) :
    ‖ZwC P J pat t s kSel σ Rs a dag hL1 mk roots z‖ ≤ 1 := by
  unfold ZwC
  rw [norm_mul]
  have h2 : ‖(if MkUnits.selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots z then (1 : ℂ)
      else 0)‖ ≤ 1 := by split_ifs <;> simp
  calc _ ≤ 1 * 1 := mul_le_mul (norm_pieceAtomWAt_le P J pat t s kSel σ Rs a dag mkF hsub hL1 hRs _ hset _) h2
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Weight

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) (J : Finset (Fin (2 * R)))

include hG in
/-- **The member weight is the class constant times the `G_sb` weight at the restricted decoration.** -/
theorem member_Zs_eq (P : WTParams) (hL1 : 1 ≤ P.L) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hRs : ∀ j, P.L ≤ Rs j) (hset : mk a.prime = classMk mkF a) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hGeoA : CapGeo (recLG a) J p) (hGeoY : CapGeo y.1.layered J p) (hstem : ¬ StemDep σ kSel ∨ CleanPt J a)
    (κ : GenDecoration y.1.skeleton P.d roots 0) :
    (if selAnd
        (fun κS => selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
        (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag) κ then
      genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
        (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ else 0) =
      cGen J kSel Rs a mk *
        ZwC P J pat t s kSel σ Rs a dag hL1 mk roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) := by
  set z := (memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ with hz
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  -- the indicator
  have h1 : (if selAnd
        (fun κS => selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
        (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag) κ then
      genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
        (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ else 0) =
      ((ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots dag z : ℝ) : ℂ) *
        genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
          (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ := by
    rw [← member_selAnd_ZwG P hL1 a mk hG J roots dag hcapA hrepU y hy hGeoY κ]
    split_ifs <;> simp
  -- the atom weight
  have h2 : genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
      (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ =
      (selOK (recLG a) J kSel : ℂ) *
        ((∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
          zatomG J P.L σ kSel Rs a (mk a.prime) z) := by
    rcases hstem with hns | hc
    · obtain ⟨rfl, rfl⟩ := eq_none_of_not_stemDep hns
      unfold genZa
      rw [selOK_stemFree, selOK_stemFree, selConst_stemFree, selConst_stemFree, zatomG_stemFree]
      simp only [Complex.ofReal_one, one_mul]
      exact Finset.prod_eq_one fun c _ => genNW_stemFree _ J P.L Rs _ _
    · unfold genZa
      rw [selOK_member a mk y hy J hcapA hcapY hG hc hGeoA.one_flower hGeoR.one_flower kSel,
        selConst_member a mk y hy J hcapA hcapY hG hc hGeoA.one_flower hGeoR.one_flower kSel Rs,
        zatom_member' a mk y hy J hcapA hcapY hG hc hGeoA.one_flower hGeoR.one_flower hrepU P.L σ kSel Rs κ]
  -- the sibling indicator and the atom weight
  have h3 := zatomG_mul_sibIndAt P J pat t s kSel σ Rs a dag mkF hsub hL1 hRs (mk a.prime) hset z
  have e : (((if selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots z then (1 : ℝ) else 0) : ℝ) :
      ℂ) = if selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots z then (1 : ℂ) else 0 := by
    split_ifs <;> simp
  rw [h1, h2]
  unfold ZwG cGen ZwC
  rw [Complex.ofReal_mul, e]
  calc _ = (selOK (recLG a) J kSel : ℂ) *
        ((∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
          (zatomG J P.L σ kSel Rs a (mk a.prime) z *
            ((sibIndAt J a (mk a.prime) dag (flwAt J a (mk a.prime))
              (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L 0 z.1) : ℝ) : ℂ))) *
        (if selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots z then (1 : ℂ) else 0) := by ring
    _ = _ := by rw [h3]; ring

/-! ## The unit tops -/

section Tops
variable (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
  (hc : CleanPt J a)
  (honeA : MkSlotsS.OneFlower (recLG a) J)
  (honeY : MkSlotsS.OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)
  (kSel : Fin (2 * R) → Option ℕ) (L : ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)

-- [copied] world `Flower/MkSlotsI/CoreW2.lean` lines 302–343 (`top_member`, the per-unit step), with the resonance
-- factor replaced by an arbitrary real `x` (the proof never reads it), see COPIED-SHA256SUMS.
include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- **The stem node weight at the core of a unit top of a member is B3-2's top filter**, unit by unit and at every
argument (CoreW's `top_member` before the product). -/
theorem genNW_top_member
    (hselY : ∀ j, (kSel j).isSome → (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) J kSel j).isSome)
    (hrepS : ∀ j, a.prime.data.coreBranch a.prime.prime.1
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper ∉
        selSetCap (recLG a) J kSel)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (x : ℝ) :
    genNW (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J L σ kSel Rs
        (y.1.data.coreBranch y.1.plain (unitClBlock (y.2 j)).upper).toNode x =
      (MkSlotsT.radProd (MkSlotsT.SURep a mk J (radTGen L σ kSel Rs) j) x : ℂ) := by
  set Φ₁ := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set hd₁ := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set c := Φ₁.hinge hd₁ j
  have hh : (memShape a mk y hy).hinge (source_disjMk a mk y hy) j = c :=
    MkSlotsT.hinge_eq_of_hmom Φ₁ (memShape a mk y hy) hd₁ (source_disjMk a mk y hy)
      (fun j i => congrFun (congrFun (memShape_hmom a mk y hy) j) i) j
  have hu₂ : (unitClBlock (y.2 j)).upper = (memShape a mk y hy).br c := by
    rw [← hh, (memShape a mk y hy).br_hinge]
  have hu₁ : (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper = Φ₁.br c :=
    (Φ₁.br_hinge hd₁ j).symm
  have hSU : MkSlotsT.SURep a mk J (radTGen L σ kSel Rs) j =
      MkSlotsT.SUStem y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J
        (fun b => radTGen L σ kSel Rs b.1.1) (blk := fun j => unitClBlock (y.2 j)) j :=
    (MkSlotsT.SUStem_member_eq a mk y hy J hcapA hcapY hG hrepU (radTGen L σ kSel Rs) j).symm
  rw [hSU]
  have hnsY : (y.1.data.coreBranch y.1.plain (unitClBlock (y.2 j)).upper : GBranch (layeredReconstruction y.1.data
      y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).garden.tree) ∉ selSetCap (layeredReconstruction
        y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel := by
    intro h
    have h' : y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c) ∈ selSetCap (layeredReconstruction
        y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel := by
      rw [← hu₂]; exact h
    have hA := (coreY_mem_selSetCap_iff a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel c).1 h'
    apply hrepS j
    have he : coreRec a (mk a.prime) c = a.prime.data.coreBranch a.prime.prime.1
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper := by
      rw [hu₁]; rfl
    rwa [he] at hA
  refine (genNW_top_aux hselY _ hnsY _).trans ?_
  unfold MkSlotsT.SUStem
  exact congrArg (fun rs => ((MkSlotsT.radProd rs _ : ℝ) : ℂ)) (ite_congr rfl (fun _ => rfl) (fun _ => rfl))
-- [end copied]

end Tops

include hy hG in
/-- **The top weight of a member at a unit top is B3-2's top filter** (stem-free, or stem-clean with the
representative's selection present). -/
theorem genTw_top_member (P : WTParams) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hset : mk a.prime = classMk mkF a)
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hGeoA : CapGeo (recLG a) J p) (hGeoY : CapGeo y.1.layered J p) (hstem : ¬ StemDep σ kSel ∨ CleanPt J a)
    (hok : selOK (recLG a) J kSel = 1)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    genTw (d := P.d) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs
        (unitClBlock (y.2 j)).upper =
      V5W2L.topFilterWeightL (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) := by
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  funext q
  rcases hstem with hns | hc
  · obtain ⟨rfl, rfl⟩ := eq_none_of_not_stemDep hns
    have hSU : MkSlotsT.SURep a mk J (radTGen P.L (fun _ => none) (fun _ => none) Rs) j = [] := by
      rw [radTGen_stemFree]
      unfold MkSlotsT.SURep MkSlotsT.SUStem
      split_ifs <;> rfl
    rw [hSU]
    unfold genTw
    exact (genNW_stemFree _ J P.L Rs _ _).trans (by simp [V5W2L.topFilterWeightL])
  · have hselA := (selOK_eq_one_iff _ J kSel).1 hok
    have hselY : ∀ j, (kSel j).isSome → (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)) J kSel j).isSome :=
      (selOK_eq_one_iff _ J kSel).1 ((selOK_member a mk y hy J hcapA hcapY hG hc hGeoA.one_flower hGeoR.one_flower
        kSel).trans hok)
    unfold genTw
    rw [genNW_top_member a mk y hy hG J hcapA hcapY hrepU hc hGeoA.one_flower hGeoR.one_flower kSel P.L σ Rs hselY
      (fun j => rep_tops_not_sel J pat t s kSel mkF hsub a mk hset j) j]
    rfl

/-! ## The unit kernels and the regional bound -/

include hy hG in
/-- **The member's general slot family agrees with B3's frontier-weighted family on the regional slots and the tops.** -/
theorem member_regAgree (P : WTParams) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hset : mk a.prime = classMk mkF a) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hGeoA : CapGeo (recLG a) J p) (hGeoY : CapGeo y.1.layered J p)
    (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
        (a.prime.data.coreBranch a.prime.prime.1 b) = none)
    (hstem : ¬ StemDep σ kSel ∨ CleanPt J a) (hok : selOK (recLG a) J kSel = 1) :
    RegAgree (fun j => unitClBlock (y.2 j)) y.1.plain
      ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
          (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
            h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
          (stateLayer y.1) (stateLayer_isLayering y.1)
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s),
        genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩
      (slotFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ h p
        (fun j => frontierG (Rf j)) (memberTopW y (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs)))) := by
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hGeoA' : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p := hGeoA
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA'.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
  have hstem' : StemDep σ kSel → CleanPt J a := fun hsd => hstem.resolve_left (not_not.mpr hsd)
  intro j
  refine ⟨fun q hq => ?_, fun v hv => ?_, ?_⟩
  · exact unitSlot_plain a mk y hy hG J hGeoA' hGeoR pat t s hrepUP P.L P.γ P.δ σ kSel Rs h roots Rf dag hstem'
      (.inl q) (iota_ne_regPair (memShape a mk y hy) hG j hq)
  · exact unitSlot_plain a mk y hy hG J hGeoA' hGeoR pat t s hrepUP P.L P.γ P.δ σ kSel Rs h roots Rf dag hstem'
      (.inr v) (iota_ne_regChain (memShape a mk y hy) hG j hv)
  · show genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs
        (unitClBlock (y.2 j)).upper = memberTopW y (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs)) (y.2 j).blk.a
    rw [memberTopW_apply a mk y hy]
    exact genTw_top_member a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset hcapA hrepU hGeoA hGeoY hstem hok j

include hy hG in
/-- **The unit kernels of a member** (with its general slot family) are V5W-2L's `unitRecenteredFWL` with the frontier
weight and the representative's unit radius lists `SURep a mk J (radTGen …)`. -/
theorem member_unitKernel (P : WTParams) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hset : mk a.prime = classMk mkF a) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hGeoA : CapGeo (recLG a) J p) (hGeoY : CapGeo y.1.layered J p)
    (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
        (a.prime.data.coreBranch a.prime.prime.1 b) = none)
    (hstem : ¬ StemDep σ kSel ∨ CleanPt J a) (hok : selOK (recLG a) J kSel = 1)
    (hcanY : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p) :
    unitKernelMGW (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain
      ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
          (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
            h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
          (stateLayer y.1) (stateLayer_isLayering y.1)
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s),
        genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩
      P.L P.γ P.δ (stateLayer y.1) 0 =
    fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ) (t' : Fin 3 → ℝ)
        (k : Fin 4 → Mom P.d) =>
      V5W2L.unitRecenteredFWL p
        (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1))
        (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) y.1 (y.2 j) P.L P.γ P.δ
        (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) 0
        (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3) :=
  (unitKernelMGW_agree (member_regAgree a mk y hy hG J P pat t s kSel σ Rs mkF hsub hset h roots Rf dag hGeoA hGeoY
    hrepUP hstem hok) y.1.data P.L P.γ P.δ (stateLayer y.1) 0).trans
    (member_ker_eqWMkL a mk y hy P.L P.γ P.δ h 0 (fun j => frontierG (Rf j)) hcanY hlay
      (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs)))

/-- **The regional bound of a member's general slot family** (B3-2's `regBoundFWW` through the agreement). -/
def memberRBG (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (b : ℝ) (hb0 : 0 ≤ b) (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (hagree : RegAgree (fun j => unitClBlock (y.2 j)) y.1.plain
      ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
          (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
            h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
          (stateLayer y.1) (stateLayer_isLayering y.1)
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s),
        genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩
      (slotFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ h p
        (fun j => frontierG (Rf j)) (memberTopW y (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs))))) :
    RegBoundW (fun j => unitClBlock (y.2 j)) y.1.plain
      ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
          (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
            h P.L roots)
          (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
          (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
          (stateLayer y.1) (stateLayer_isLayering y.1)
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s),
        genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩ P.L 0 :=
  RegBoundW.ofAgree (regBoundFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ h p
    (fun j => frontierG (Rf j)) (fun j => unitClBlock (y.2 j)) 1 le_rfl
    (fun j x => MkSlots.IntMember.frontierG_norm_le P Rf j x) 0 (lt_of_lt_of_le zero_lt_one hL1).ne'
    (fun j => hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 h (stateLayer y.1) 0 p hb0 hlay
      (fun q j j' hq => hB q hq j j') j)
    (memberTopW y (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs))) (norm_topWeightOf_le _ _)) hagree

end Class

end WaveTurbulence.Flower.MkSlotsI
