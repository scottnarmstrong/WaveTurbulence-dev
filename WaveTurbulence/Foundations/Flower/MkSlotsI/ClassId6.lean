/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId5
public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassIdL3
public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassIdL4
public import WaveTurbulence.Foundations.Flower.MkSlots.IntClass

/-! # B3s-HELPER7 ClassId (part 6): the class identity `classCentreIdentity : ClassCentreIdentityAt Kg P`

For every class (the binders of `ClassCentreIdentityAt`), unit marking `mkU` and slot data `sd` with `SlotDataOK`:
* `classValue_eq_outputs` (α): the class value is the sum of the frozen summands over the fine′ output set `T`;
* if the representative's requested selections are missing (`selOK(a) = 0`): every member summand vanishes
  (`member_val_zero`) and so does `sgnGen`;
* otherwise the pinned list-T4 with the centre sum (`weightedClassFactorizationμDLX`) on the members' centre-indexed
  mode forms (`member_val`, `member_hasSumX`, `member_summξ`, `member_integ`, `member_hsm`), the members lying in `A`
  (`outputs_mem_AMk`, the run start is admissible: `startAt_admP`) and the lower bounds being class-common
  (`member_lbS_br`, `member_lbS_clk`, `member_lbS_inter`, ClassIdL*); the class kernels `twistedRecenteredFWL` are
  `unitKerGen` (`MkUnitsL.unitHkFWL`), and the result is `classCentreRHS` verbatim. -/

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
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW fixCore recLG fixAt outerValMμD fixMeasure)
open WaveTurbulence.Flower.MkSlots.IntMember (restIndO capConstO)
open WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic

namespace WaveTurbulence.Flower.MkSlotsI

/-- `selOK` is `0` or `1`. -/
theorem selOK_eq_zero_of_ne_one {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)
    (h : selOK LG J kSel ≠ 1) : selOK LG J kSel = 0 := by
  unfold selOK at h ⊢
  split_ifs at h ⊢
  · exact absurd rfl h
  · rfl

/-- **A member summand vanishes when the representative's requested selections are missing.** -/
theorem member_val_zero (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d)
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
    (hstem : ¬ StemDep σ kSel ∨ CleanPt J a) (hok0 : selOK (recLG a) J kSel = 0)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p (objKind (2 * R)) mk)
    (hGeoY : CapGeo y.1.layered J p) (hPatY : CapPatValid y.1.layered J pat p)
    (hrootY : ∀ j ∉ J, ∃ ℓ : GLeaf y.1.layered.garden.tree, IsCapFlower y.1.layered J ℓ ∧ ℓ.1.1 = j) :
    kernelKgenSel P.L P.γ P.δ y.1.layered (fixCap y.1.layered J pat t s) (offCap y.1.layered J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag y.1.layered) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π y.1.layered) = 0 := by
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
  rw [hsk]
  unfold cGen
  rw [hok0]
  simp

/-- **The class identity**: for every `Kg` and `P`, the class value of every fine′ class is the centre-indexed outer
mode form `classCentreRHS` consumed by `CentreEngine`'s `hval`. -/
theorem classCentreIdentity (Kg : ℕ → ℝ → ℝ) (P : WTParams) : ClassCentreIdentityAt Kg P := by
  intro hd1 hL1 hη0 C p hp R hR1 hR N hN1 hN J hJ pat kSel t ht s hs A hA hpl hTC roots h b Rf σ Rs dag hb hsn hRf
    hRs hhigh mkF hmk π hstemπ mkU hset hout sd hsd
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have haA : (repPt π).layered ∈ A := repPt_layered_memMk π
  have hcan : IsCanonGC (p + 1) (repPt π).layered := (hA _ haA).1.1
  have hGeoA : CapGeo (recLG (repPt π)) J p := by
    show CapGeo (layeredReconstruction (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))) J p
    rw [sourceLayer_reconstructs (repPt π)]
    exact (hA _ haA).2.2.2.2.1
  obtain ⟨T, hT⟩ := exists_outputs_finsetMk (p := p) (repPt π) mkF
  have hMk : ∀ c ∈ markI J pat t s kSel (repPt π).prime, c ∈ vinesV0 (repPt π).prime.skeleton (repPt π).totalSigma →
      c ∈ mkU (repPt π).prime := by
    rw [hset]
    exact MkSlotsB.classMk_hMk J pat t s kSel (repPt π) mkF hmk.sub
  have hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)) j |>.atoms,
      fixCap (layeredReconstruction (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))) J pat t s ((repPt π).prime.data.coreBranch (repPt π).prime.prime.1 b) = none :=
    fun j b hb => MkSlotsB.hU_rep_pat_recon J pat t s kSel (repPt π) (mkU (repPt π).prime) hMk j b hb
  have hstem : ¬ StemDep σ kSel ∨ CleanPt J (repPt π) := hstemπ.imp id fun h' => h' (repPt π) (Relation.EqvGen.refl _)
  have hadm : MkSlots.AdmP R J pat t s kSel (sourceStart (repPt π) mkU) := by
    show MkSlots.AdmP R J pat t s kSel (startAt (repPt π) (mkU (repPt π).prime))
    rw [hset]
    exact MkSlots.startAt_admP J pat t s kSel (repPt π) mkF hmk.sub
  have hmemA : ∀ y ∈ sourceClass (repPt π) p (objKind (2 * R)) mkU, y.1.layered ∈ A := fun y hy =>
    outputs_mem_AMk (MkSlots.twistClosedAdm_of_marked hTC) (repPt π) mkU hadm haA hcan y hy
  rw [MkSlots.classValue_eq_outputs P J pat kSel t s A hTC roots h Rf σ Rs dag mkF hmk π hcan T hT]
  have hT' := sourceClass_hTMk (repPt π) mkU T (hT.trans hout.symm)
  by_cases hok : selOK (recLG (repPt π)) J kSel = 1
  · refine (weightedClassFactorizationμDLX (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
      (sourceAssemblyMk (repPt π) mkU) (unitBlkMk_disj (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.prime T hT'
      (fun LG => kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG))
      (sgnGen J P.L P.γ P.δ s kSel Rs (repPt π) mkU roots dag) (Ξ := fun X => ∀ t', (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).Λ t')
      (fun X ξ => ((modeWt (famX (fam₀Of sd hsd.supp) (famCOfData sd) X) ξ : ℝ) : ℂ)) (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G P.L P.γ P.δ 0 roots (fun _ => t)
      (domOf (pieceGenAt P J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag) (fun _ => t))
      (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).hinges
      (fun X z => ZwC P J pat t s kSel σ Rs (repPt π) dag hL1 mkU roots z * chiX P.L 0 X z) ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1)
      (fixMeasure (fixAt J pat t s (repPt π) (mkU (repPt π).prime)))
      (fun X ξ s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).a s' (ξ s')) (fun X ξ s' => (famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m s' (ξ s'))
      ((stShape (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)).route (repPt π).prime.prime.1 ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1)) ((stShape (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)).hclk (unitBlkMk_disj (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime))) ((stShape (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)).hmom (unitBlkMk_disj (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)))
      (fun j => unitProfile (unitBlkMk (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)) h j) (fun j => frontierG (Rf ((unitBlkMk (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)) j).upper.1.1))
      (MkSlotsT.SURep (repPt π) mkU J (radTGen P.L σ kSel Rs)) ?_ ?_ ?_ ?_ ?_).trans ?_
    · intro y hy
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact member_val P hL1 hd1 hη0 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots Rf dag hmk.sub hset
        hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY
        (member_lbS_br (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_clk (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_inter (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP kSel hMk)
    · intro y hy
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact (member_hasSumX P hL1 hd1 hη0 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots Rf dag hmk.sub hset
        hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY
        (member_lbS_br (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_clk (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_inter (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP kSel hMk)).summable
    · intro X y hy
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact member_summξ P hL1 hd1 hη0 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots Rf dag hmk.sub hset
        hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY
        (member_lbS_br (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_clk (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_inter (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP kSel hMk) X
    · intro X ξ y hy z
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact member_integ P hL1 hd1 hη0 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots Rf dag hmk.sub hset
        hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY
        (member_lbS_br (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_clk (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_inter (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP kSel hMk) X ξ z
    · intro X ξ y hy
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact member_hsm P hL1 hd1 hη0 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots Rf dag hmk.sub hset
        hRs hGeoA hrepUP hstem hok sd hsd y hy hGeoY hPatY hrootY hcanY
        (member_lbS_br (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_clk (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP)
        (member_lbS_inter (repPt π) mkU y hy ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J hGeoA hGeoR pat t s hrepUP kSel hMk) X ξ
    · unfold classCentreRHS centreForm
      rw [Fintype.sum_unique]
      rfl
  · have hok0 := selOK_eq_zero_of_ne_one _ J kSel hok
    rw [sum_layered_eq_sum_classU (Us := unitsSplit (sourceAssemblyMk (repPt π) mkU))
      (A := unitsStart (sourceAssemblyMk (repPt π) mkU) (unitBlkMk_disj (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π))) (repPt π).prime.prime (unitsRegion (sourceAssemblyMk (repPt π) mkU) (unitBlkMk_disj (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma (mkU (repPt π).prime))) T hT' (fun LG => kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG))]
    have hz : ∀ y ∈ sourceClass (repPt π) p (objKind (2 * R)) mkU, (fun LG => kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG)) y.1.layered = 0 := by
      intro y hy
      have hyA := hmemA y hy
      have hGeoY : CapGeo y.1.layered J p := (hA _ hyA).2.2.2.2.1
      have hPatY : CapPatValid y.1.layered J pat p := (hA _ hyA).2.2.2.2.2
      have hcanY : IsCanonGC (p + 1) y.1.layered := (hA _ hyA).1.1
      have hplY : y.1.layered.garden.IsPlain := by rw [← stateLayer_spec y.1]; exact y.1.data.garden_plain y.1.plain
      have hrootY := MkSlotsB.exists_capFlower_of_capGeo hGeoY hplY (hA _ hyA).2.2.1 (by rw [hJ])
      have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          p := by rw [stateLayer_spec y.1]; exact hGeoY
      exact member_val_zero P hL1 hd1 hmk.fine π (repPt π) rfl hout ((stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1) J pat kSel σ Rs t s hs ht.2.le h b hb0 hsn roots
        Rf dag hmk.sub hset hRs hGeoA hrepUP hstem hok0 y hy hGeoY hPatY hrootY
    rw [Finset.sum_eq_zero hz]
    unfold classCentreRHS centreForm
    rw [Fintype.sum_unique, sgnGen_eq]
    unfold cGen
    rw [hok0]
    simp

end WaveTurbulence.Flower.MkSlotsI
