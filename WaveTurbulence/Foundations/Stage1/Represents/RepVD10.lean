/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD9
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the class sum (B3/B4)

`class_sum_modes`: the sum of `U.toLF.valueSel (selP π)` over a finite set `T` of gardens with `↑T = (repPt π).outputs` is the outer
mode sum with the unit factors replaced by the class kernels `twistedRecenteredModC` of `canonFinsetK` (VINE-C's
`sum_tauClass_vineD_api_dep`, RepVB12).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic MeasureTheory

variable {p : ℕ}

open scoped Classical in
theorem class_sum_modes {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA R (p) (objKind (2 * R)) A)
    (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hctrl : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn a.prime.data a.prime.prime.1 P.L P.γ P.δ
        (typeProfiles a.layered (U.h i)) (sourceLayer a) (sourceLayer_isLayering a)
        ((profileShape a).iota a.prime.prime.1 hG s') ts x))
    (T : Finset (LayeredGarden (2 * R))) (hT : (T : Set (LayeredGarden (2 * R))) = a.outputs (p := p) (kind := objKind (2 * R))) :
    ∑ LG ∈ T, U.toLF.valueSel tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitHk P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a)
              (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j) base lam t k)) := by
  letI : Fintype U.ι := U.fin
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hall := fun y hy => member_hV π a hπ P U hd1 hL1 tt htt base roots hlay hB hG fam hexpR y hy (hctrl y hy)
  have hZ01 : ∀ z, |(if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0)| ≤ 1 := fun z => by
    split_ifs <;> simp
  exact sum_tauClass_vineD_api_dep a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceAssembly a) (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) a.prime.prime T
    (sourceClass_hT a T hT) (fun LG => U.toLF.valueSel tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG))
    (fun i => ((U.sign i : ℝ) : ℂ)) (fun i ξ => ((modeWt (fam i) ξ : ℝ) : ℂ)) a.fullProfile.piece.gap.garden P.L P.γ P.δ
    base roots tt a.fullProfile.piece.layer a.fullProfile.piece.hinges
    (fun z => if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hG
    (fun i ξ s x => (fam i).a s (ξ s) x) (fun i ξ s => (fam i).m s (ξ s))
    ((profileShape a).route a.prime.prime.1 hG)
    ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
    ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
    (fun i j => unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
    (fun y hy => (hall y hy).1)
    (fun i y hy => (hall y hy).2 i)
    (fun i ξ y hy z => member_integ π a hπ P U hd1 hL1 tt htt base roots hlay hB hG fam y hy i ξ z)
    (fun i ξ y hy => member_hsm a P U hd1 hL1 tt base roots hlay hB hG fam y hy i ξ)

end WaveTurbulence.Represents
