/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecProd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecContract
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecEng
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecContract` (sha256 6cc874f13f64f1ef…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 18, step 2): the contraction clause `hcontract` of `freeDict_rec` from `SuppConcl`

`ae_ne_pi`: two distinct coordinates of `τ : ι → ℝ` differ almost everywhere.
`records_ne_zero_of_prod`: if the full product of the term (exceptional weights times native rows) is nonzero then every record factor is nonzero.
`hcontract_of_records`: with `SuppConcl` for every record, `add = recAdd` and distinct clock variables a.e., a nonzero product forces every order atom of `add` strictly and every record branch below the top clock or
below an interior clock; this is exactly the contradiction required.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {hG : G.IsPlain}
variable {R : CLRegionData G U a b} {n : ℕ}

variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- **`hcontract` from `SuppConcl`.**  Almost every clock vector either makes the product vanish or has all order atoms of `recAdd` strict and every record branch
below the top clock or below an interior clock. -/
theorem hcontract_of_recordsΓ (recs : List (ExcRec G d)) (hnp : (recs.map ExcRec.p0).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (hss : ∀ r ∈ recs, SuppConclΓ B hM9 r.X r.bj (zc r) (addr r)) (tt : Fin 3 → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) (Qf : ((assemblyShapeΓ hM9 B).TVar → ℝ) → SourcePair G → ℂ)
    (Tf : ((assemblyShapeΓ hM9 B).TVar → ℝ) → GBranch G.tree → ℂ) :
    ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
      ¬ ((∀ c ∈ recAddΓ B hM9 recs zc addr, τ c.1 < τ c.2) ∧
        ∀ v ∈ bexOf recs, clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) v < tt 0 ∨ ∃ y ∈ U, y ≠ a ∧
          clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) v < clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) y) →
      (∏ p ∈ clRegionalPairs hG U, (if p ∈ pexOf recs then xqOf recs p tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) ξ
          else Qf τ p)) *
        (∏ v ∈ U.erase a, (if v ∈ bexOf recs then 1 else Tf τ v)) = 0 := by
  classical
  filter_upwards [ae_pairs_distinct (recAddΓ B hM9 recs zc addr)] with τ hτ hnot
  by_contra hne
  have hne1 : ∏ p ∈ clRegionalPairs hG U, (if p ∈ pexOf recs then xqOf recs p tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) ξ
          else Qf τ p) ≠ 0 := left_ne_zero_of_mul hne
  have hX := records_ne_zero_of_prod recs hnp hreg tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) ξ (Qf τ) hne1
  have hup : clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) a = tt 0 := clLocalClock_upper R tt _
  refine hnot ⟨fun c hc => ?_, fun v hv => ?_⟩
  · obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    have hr' : r ∈ recs := List.mem_toFinset.mp hr
    have hz : ¬ zc r := by
      intro hzr; rw [if_pos hzr] at hcr; exact absurd hcr (Finset.notMem_empty _)
    rw [if_neg hz] at hcr
    obtain ⟨hpair, -⟩ := hss r hr' _ _ (hX r hr')
    obtain ⟨hle, hdis⟩ := hpair hz c hcr
    rw [clLocalClock_slotΓ, clLocalClock_slotΓ] at hle hdis
    rcases hdis with hne' | hlt
    · exact lt_of_le_of_ne hle (hτ c hc hne')
    · exact hlt
  · obtain ⟨r, hr, rfl⟩ := mem_bexOf.mp hv
    obtain ⟨-, hlt⟩ := hss r hr _ _ (hX r hr)
    rw [← hup]
    exact hlt

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
