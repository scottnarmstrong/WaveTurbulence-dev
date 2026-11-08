/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.ClassL
public import WaveTurbulence.Foundations.Flower.MkUnits.WClass

/-! # MK-UNITS-L (B3-2): the weighted class sum of a fine′ piece with per-unit top filters

* `unitHkFWL`: the weighted class kernel of a unit with the product filter `S : List ℝ`,
  `twistedRecenteredFWL p (g j₁) S … (modW λ)` (Stage1WVine's `unitHkFW`, which is `S = none`).
* `class_sum_modesWMkL`: B3's `class_sum_modesWMk` with the extra weight `E` presented by the unit top filters `SU` on
  every run-class member: the sum of the values over the fine′ output set is the outer mode sum of the representative's
  spliced garden with the unit factors `unitHkFWL P p (SU j)` (list-T4 through `weightedClassFactorization_depL`).

Adapted from `Flower/MkUnits/WClass.lean`, `Flower/Stage1WVine/WHinge1.lean` (`unitHkFW`) (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.VineEstS2 WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Flower.V5W2L (topFilterWeightL twistedRecenteredFWL)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-- **The weighted class kernel of a unit with a product of top filters** (`S = []`: Stage1WVine's `unitHkFW`). -/
def unitHkFWL (P : WTParams) (p : ℕ) (S : List ℝ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (g : Fin w → Mom P.d → ℂ) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun lam t k =>
  twistedRecenteredFWL p (g a.1.1) S G a
    (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
    P.L P.γ P.δ h wBar (VineC.modW (lam : ℝ)) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)

variable {p : ℕ}

open scoped Classical in
/-- **The weighted class sum at a marking with per-unit top filters** (B3's `class_sum_modesWMk` with the extra
weight `E` presented on every run-class member by `SU`, through list-T4). -/
theorem class_sum_modesWMkL {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
    (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (π : PcA R p (objKind (2 * R)) A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
    (hout : a.outputs (p := p) (kind := objKind (2 * R)) mk = a.outputs (p := p) (kind := objKind (2 * R)) mkF)
    (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p (objKind (2 * R)) mk → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p (objKind (2 * R)) mk → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hctrl : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p (objKind (2 * R)) mk → U.toLF.Controlled y.1.layered)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (fam : U.ι → SlotFam (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
      ∀ x, HasSum
        (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
        (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ (U.h i) p g
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
          ts x))
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ)
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (hE : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)), y ∈ sourceClass a p (objKind (2 * R)) mk →
      ∀ κ : GenDecoration (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)).garden P.d roots 0,
      E _ κ = ∏ j, nodeWeight (topFilterWeightL (SU j)) P.L base (y.2 j).blk.a
        (collapseGenDecoration y.1.data y.1.plain κ).1)
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = a.outputs (p := p) (kind := objKind (2 * R)) mkF) :
    ∑ LG ∈ T, valueSelW U.toLF tt base roots LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG)
        (fun κ => fwWeight p g base LG κ * E LG κ) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
            (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
            (fun z => if selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            (fun j lam t k => unitHkFWL P p (SU j) (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) g
              (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
              base lam t k)) := by
  letI : Fintype U.ι := U.fin
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hall := fun y hy => member_hVWMkL hFT π a hπ hout P U hd1 hL1 tt htt base roots hlay hcanM hB g cψ hc hg hG fam
    hexpR SU E y hy (hE y hy) (hctrl y hy)
  have key := weightedClassFactorization_depL a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceAssemblyMk a mk) (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
    a.prime.prime T (sourceClass_hTMk a mk T (hT.trans hout.symm))
    (fun LG => valueSelW U.toLF tt base roots LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG)
      (fun κ => fwWeight p g base LG κ * E LG κ))
    (fun i => ((U.sign i : ℝ) : ℂ)) (Ξ := fun i => ∀ s, (fam i).Λ s) (fun i ξ => ((modeWt (fam i) ξ : ℝ) : ℂ))
    (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
    (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
    (fun z => if selSkCMk a mk P.L P.γ P.η hL0.ne' base roots z then (1 : ℝ) else 0) hG
    (fun i ξ s x => (fam i).a s (ξ s) x) (fun i ξ s => (fam i).m s (ξ s))
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
      (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
      (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    (fun i j => unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
    (fun j => g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1)
    SU
    (fun y hy => (hall y hy).1)
    (fun i y hy => (hall y hy).2 i)
    (fun i i' ξ y hy z => member_integWMkL a mk P U hd1 hL1 tt base roots hlay hcanM hB g cψ hc hg hG
      (fun s x => (fam i').a s (ξ s) x) (fun s => (fam i').m s (ξ s)) SU y hy i z)
    (fun i i' ξ y hy => member_hsmWMkL a mk P U hd1 hL1 tt base roots hlay hcanM hB g cψ hc hg hG
      (fun s x => (fam i').a s (ξ s) x) (fun s => (fam i').m s (ξ s))
      (tsum_ampBound_mode_le (fam i') hG P.L hL0 base roots ξ).1
      (fun z => if selSkCMk a mk P.L P.γ P.η hL0.ne' base roots z then (1 : ℝ) else 0)
      (fun z => by split_ifs <;> simp) SU y hy i)
  unfold unitHkFWL
  exact key

end WaveTurbulence.Flower.MkUnitsL
