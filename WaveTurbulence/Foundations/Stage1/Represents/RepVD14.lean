/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD13
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2M
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB18
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the outer slot data of the representative (B4)

`vine_slot_data`: from `slots_existM` at the representative `a`, the mode families `fam i` of the slots of `G_sb` with the
superposition identity of the native slot kernels on the boxes `slotBox`, and the per-slot masses `μ i s`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
open scoped ENNReal

open scoped Classical in
theorem vine_slot_data (Pg : WTParams) (E : GateEnv Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotM Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)), p < Pg.D → IsCanonGC (p + 1) a.layered →
      a.prime.data.size ≤ Pg.N (p + 1) ^ 4 → ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
      ∀ (U : TypeFamilyD Pg.d (2 * R)),
      (∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i)) →
      ∀ (hG : a.fullProfile.piece.gap.garden.IsPlain),
      ∃ (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden Pg.d) (μ : U.ι → ReplacementSlot a.fullProfile.piece.gap.garden → ℝ≥0∞),
        (∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
            a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
          (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
          (slotFn a.prime.data a.prime.prime.1 Pg.L Pg.γ Pg.δ (typeProfiles a.layered (U.h i)) (sourceLayer a)
            (sourceLayer_isLayering a) ((profileShape a).iota a.prime.prime.1 hG s') ts x)) ∧
        (∀ i s, ∑' l, maxBracketPow Pg.η (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μ i s) ∧
        (∀ i s, μ i s ≤ ENNReal.ofReal (K * (C * Real.sqrt Pg.δ) ^ slotSize a.prime.data
            ((profileShape a).iota a.prime.prime.1 hG s) *
          Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            ((profileShape a).iota a.prime.prime.1 hG s) : ℝ)) *
          slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
            ((profileShape a).iota a.prime.prime.1 hG s))) := by
  obtain ⟨K, hK1, hKe, hslot⟩ := slots_existM Pg E
  refine ⟨K, hK1, hKe, fun C hC R p a hp hcan hsize tt htt U hctrl hG => ?_⟩
  have hspec := sourceLayer_reconstructs a
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [hspec]; exact hcan
  have h : ∀ i, ∃ Rep : SlotRepM Pg.η a.prime.skeleton a.prime.prime.1 Pg.d
        (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) tt,
      Rep.Box = slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 ∧
      Rep.Fn = slotFn a.prime.data a.prime.prime.1 Pg.L Pg.γ Pg.δ
        (typeProfiles (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
          (U.h i)) (sourceLayer a) (sourceLayer_isLayering a) ∧
      ∀ s, Rep.μ s ≤ ENNReal.ofReal (K * (C * Real.sqrt Pg.δ) ^ slotSize a.prime.data s *
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) s : ℝ)) *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i) s) := fun i =>
    hslot C hC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p hp hsize hcan' tt htt
      (typeProfiles (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        (U.h i)) (fun _ => U.b i) (by rw [hspec]; exact hctrl i)
  choose Rep hBox hFn hμ using h
  have hfam := fun i => slotPackage_of_rep (profileShape a) a.prime.prime.1 hG (Rep i)
  choose fam hfam1 hfam2 using hfam
  refine ⟨fam, fun i s => (Rep i).μ ((profileShape a).iota a.prime.prime.1 hG s), ?_, hfam2, fun i s => hμ i _⟩
  intro i s' ts hts x
  have h1 := hfam1 i s' ts (by rw [hBox i]; exact hts) x
  rw [hFn i, hspec] at h1
  exact h1

end WaveTurbulence.Represents
