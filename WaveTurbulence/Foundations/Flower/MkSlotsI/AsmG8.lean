/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG7

/-! # B3s-HELPER7 AsmG (4): the unit data and the hinge data of the engine in `classRepGen_at`

B3-2's unit data with the per-unit top filters `SURep a mk J (radTGen L σ kSel Rs)` (W:MkUnitsL/AssemblyL.lean):
`M0Gen` (the unit masses), `lfjGen` (their leaf factors), `cl2Gen`, `gjGen`, `njGen` (B3's exponents); `hM_gen`,
`hlfj_gen`; and **`hhinge_gen`**: B3-2's `unit_hinge_dataWMkL` with the domain conjunct `hHkPropD_pieceGenAt`
(W:MkSlotsI/AsmG1.lean) on `domOf ∩ pinSet` and the mass bound `∏ Mh ≤ ∏ (ChFWL · M0Gen) · ∏ (1+|λ|)^{6η⁶}`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlotsI
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
  WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots (withC₁ recLG outerValMμD fixMeasure)
open WaveTurbulence.Flower.FinalMKDefs (RepresentsIntMKSel)
open scoped ENNReal Classical

section Units

variable (P : WTParams) (hM9 : VINEPARAM) {R : ℕ} (J : Finset (Fin (2 * R))) (σ kSel : Fin (2 * R) → Option ℕ)
  (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (b : ℝ)

/-- The per-unit top-filter radii (CoreW's `top_member`, γ's `unitTopFilters_gen`). -/
abbrev SUGen : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ :=
  MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs)

/-- The unit masses (B3-2: `topFilterMass^{|SU j|}` times B3's `unitMassC`). -/
def M0Gen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℝ :=
  topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length *
    unitMassC P hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (frontierConst P.d) b.toNNReal

/-- The unit leaf factors. -/
def lfjGen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℝ :=
  topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length *
    (frontierConst P.d ^ (9 * (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms.card +
      4 * clLocalOrder2 a.prime.data a.prime.prime.1
        (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j))) *
    regionLeafSize a.prime.data a.prime.prime.1
      (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j))
      (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ)))

/-- B3's `cl2` exponents of the units. -/
def cl2Gen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℕ :=
  clLocalOrder2 a.prime.data a.prime.prime.1
    (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j))

/-- B3's incoherence exponents of the units. -/
def gjGen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℕ :=
  cohmolIndex (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) +
    (step3D hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (canonBadKind hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a))
      (qOutOf a.prime.data a.prime.prime.1 (sourceLayer a)
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower
        (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j)))
      (fun _ => (0 : Mom P.d)) (0 : Mom P.d)).M₁

/-- B3's non-normal counts of the units. -/
def njGen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℕ :=
  (Finset.univ.filter fun i : Fin (unitN a.totalSigma j) =>
    (assemblyShape hM9 (sourceAssemblyMk a mk j)).nor i = false).card

theorem unitMassC_nonneg (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    0 ≤ unitMassC P hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) (frontierConst P.d) b.toNNReal := by
  unfold unitMassC unitMass
  have hc0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst _)
  refine mul_nonneg (pow_nonneg hc0 _) ?_
  exact mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg hL _))
    (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))

theorem hlfj_gen (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    0 ≤ lfjGen P J σ kSel Rs a mk b j := by
  unfold lfjGen
  have hc0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst _)
  exact mul_nonneg (pow_nonneg topFilterMass_nonneg _) (mul_nonneg (pow_nonneg hc0 _)
    (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)))

/-- **`hM`**: the unit masses in the engine's form. -/
theorem hM_gen (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    0 ≤ M0Gen P hM9 J σ kSel Rs a mk b j ∧ M0Gen P hM9 J σ kSel Rs a mk b j ≤
      (P.C₁ * Real.sqrt P.δ) ^ (cl2Gen a mk j) *
        P.L ^ (-(P.η ^ 8) * (gjGen P hM9 a mk j : ℝ) - P.η ^ 2 / 2 * (njGen hM9 a mk j : ℝ) + P.η ^ 7) *
        lfjGen P J σ kSel Rs a mk b j := by
  refine ⟨mul_nonneg (pow_nonneg topFilterMass_nonneg _) (unitMassC_nonneg P hM9 a mk b hC hL j), le_of_eq ?_⟩
  unfold M0Gen lfjGen cl2Gen gjGen njGen unitMassC unitMass
  rw [nor_card_eq hM9 (sourceAssemblyMk a mk j)]
  simp only [neg_mul]
  ring

end Units

/-- **`hhinge`**: the hinge data of the class kernels `unitKerGen` (B3-2's `unit_hinge_dataWMkL`) with the domain
conjunct on `domOf ∩ pinSet` (`hHkPropD_pieceGenAt`), for every vector of unit modes `lam`. -/
theorem hhinge_gen (P : WTParams) (hV : V5W2L.V5FrontierClassBoundAtL P) (hM9 : VINEPARAM)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hL2 : 2 ≤ P.L)
    (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf a.layered.garden.tree, IsCapFlower a.layered J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t < p + 1) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = classMk mkF a)
    (hcan : IsCanonGC (p + 1) a.layered) (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hsn : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
    (lam : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) P.d)
      (Mh : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      MkSlotsS.HHkPropD (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag).toStage1PieceD (fun _ => t) 0 roots
        (selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots)
        (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t) ∩
          MkSlotsB.pinSet (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag).fix)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j => unitKerGen P p J σ kSel Rs a mk h Rf j (lam j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (MkUnitsL.ChFWL P.d P.η * M0Gen P hM9 J σ kSel Rs a mk b j)) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hc0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst _)
  have hgp : ∀ j, GPresented (32 * P.d) (frontierG (Rf j)) (frontierConst P.d) := fun j =>
    gPresented_frontierG P.d (Rf j) (fun r hr => by have := hRf j r hr; linarith)
  have hSU : ∀ j, ∀ x ∈ SUGen P J σ kSel Rs a mk j, 0 < x := by
    intro j x hx
    unfold SUGen MkSlotsT.SURep MkSlotsT.SUStem at hx
    split_ifs at hx
    · exact lt_of_lt_of_le one_pos (one_le_radTGen hL1 hRs _ x hx)
    · simp at hx
  obtain ⟨H, Mh, hsum', hHk, hprod⟩ := MkUnitsL.unit_hinge_dataWMkL P hV hM9 hgate hinc htop hd1 hη0 hη6 hη2 hC1
    hδ hL1 hw hp a mk hcan hord (fun _ => t) 0 roots (fun j => frontierG (Rf j)) (frontierConst P.d)
    (one_le_frontierConst _) hgp (fun j x => frontierG_im _ x) (SUGen P J σ kSel Rs a mk) hSU h b hb
    (fun q j j' hq => hsn q hq j j') lam
  refine ⟨H, Mh, hsum', hHkPropD_pieceGenAt P J pat t s kSel σ Rs mkF hsub a hG hpat hroot hs ht dag (mk a.prime)
    hset roots _ _ H hHk, ?_⟩
  have hpt : ∀ j, MkUnitsL.ChinFWL P.d P.η *
      MkUnitsL.unitMassFWL P (SUGen P J σ kSel Rs a mk j) hM9 (sourceAssemblyMk a mk j) a.prime.data
        a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (frontierConst P.d) b ≤
      MkUnitsL.ChFWL P.d P.η * M0Gen P hM9 J σ kSel Rs a mk b j := fun j => by
    have e : MkUnitsL.ChinFWL P.d P.η *
        MkUnitsL.unitMassFWL P (SUGen P J σ kSel Rs a mk j) hM9 (sourceAssemblyMk a mk j) a.prime.data
          a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (frontierConst P.d) b =
        MkUnitsL.ChinFWL P.d P.η * M0Gen P hM9 J σ kSel Rs a mk b j := by
      unfold MkUnitsL.unitMassFWL M0Gen unitMassC
      rw [Real.coe_toNNReal b hb]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (mul_nonneg (pow_nonneg topFilterMass_nonneg _) (unitMassC_nonneg P hM9 a mk b (by linarith) hL0.le j))
  have hlam : 0 ≤ ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) :=
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
  have hch := MkUnitsL.ChinFWL_spec P.d P.η hη0.le
  rw [hprod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun j _ => mul_nonneg hch
    (MkUnitsL.unitMassFWL_nonneg P _ hM9 _ _ _ _ _ _ b hc0 (by linarith) hL0 hb))
    (fun j _ => hpt j)) hlam

end WaveTurbulence.Flower.MkSlotsI
