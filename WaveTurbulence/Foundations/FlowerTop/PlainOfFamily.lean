/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.FamilyWeightLimit
public import WaveTurbulence.Foundations.FlowerTop.CaseAssembly

/-! The plain (no cutoff) flower clause from FC23's uniform family estimate, by letting the scale `M = 2^j L → ∞`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Filter Topology Set LGSpine WaveTurbulence.FC23
open scoped Classical

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

theorem flowerWeighted_tendsto_one (hL : 0 < P.L)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|) :
    Tendsto (fun j : ℕ => flowerWeighted P F p N kind pat dagger
      (fun LG k => flowerFamilyWeight LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
        (fun _ => false) (fun _ => false) (fun _ => 0) k) ζ t s n n') atTop
      (𝓝 (flowerWeighted P F p N kind pat dagger (fun _ _ => 1) ζ t s n n')) := by
  have hfin := FlowerProbes.finite_flowerSum_support P p N w kind pat ζ
  have e : ∀ weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ,
      flowerWeighted P F p N kind pat dagger weight ζ t s n n' =
        ∑ LG ∈ hfin.toFinset, kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
          (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)
          (fun k => weight LG k * (dagger.elim 1 fun c => LG.sibWeight c k))
          (fun _ => t) 0 (fun _ => n) n' := fun weight =>
    finsum_mem_eq_finite_toFinset_sum _ hfin
  simp_rw [e]
  refine tendsto_finsetSum _ fun LG hLG => ?_
  have hLG' := hfin.mem_toFinset.mp hLG
  have hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower := by
    intro ℓ h
    have hm : LG.garden.mark ℓ ≠ none := by rw [h]; simp
    have := hLG'.1.1.2.1 ℓ hm
    rw [Garden.IsFlower] at this
    rw [h] at this
    exact absurd (Option.some.inj this) (by decide)
  have hg : ∀ k, |(dagger.elim 1 fun c => LG.sibWeight c k)| ≤ 1 := by
    intro k
    cases dagger with
    | none => simp
    | some c =>
      have := sibWeight_mem LG c k
      simp only [Option.elim]
      rw [abs_of_nonneg this.1]; exact this.2
  refine kernelKgen_tendsto_wt P.L P.γ P.δ F LG _ _ _ 0 _ _ hn
    (fun q => by simpa only [zero_add] using hF q)
    (fun j k => flowerFamilyWeight LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
        (fun _ => false) (fun _ => false) (fun _ => 0) k * (dagger.elim 1 fun c => LG.sibWeight c k))
    (fun k => 1 * (dagger.elim 1 fun c => LG.sibWeight c k)) ?_ ?_
  · intro j k
    have hm := family_weight_mem LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ))) k
    rw [abs_mul, abs_of_nonneg hm.1]
    calc _ ≤ 1 * 1 := mul_le_mul hm.2 (hg k) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k
    refine Tendsto.mul_const _ ?_
    exact tendsto_const_nhds.congr' ((family_weight_eventually_one LG p P.L hL N k).mono fun _ h => h.symm)

open Induct in
/-- **Plain clause from the uniform family bound**, at one parameter set, by letting `M = 2^j L → ∞`. -/
theorem flowerCasePlain_of_uniform (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ)
    (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams}
    (hd : 1 ≤ P.d) (hν : 0 < P.ν) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 2 ≤ P.L)
    (H : FC23UniformCut1At C U Pm P) : FlowerCaseAt CasePlain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc _
  obtain ⟨rfl, rfl⟩ := hc
  have hL1 : 1 ≤ P.L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL1
  have hsum := summable_clipped_inputs P R p hp.le hd hL1 hR
  have hlim := flowerWeighted_tendsto_one P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n' hL0 hsum
  have hB : ∀ j : ℕ, ‖flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
      (fun LG k => flowerFamilyWeight LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
        (fun _ => false) (fun _ => false) (fun _ => 0) k) ζ t s n n'‖ ≤
      flowerRootBudget Pm P p ζ n n' *
        P.L ^ (flowerLExponent Pm P pat - ((40 * P.d) * (2 * Pm) : ℕ) - (2 * Pm : ℕ)) *
        P.δ ^ (8 * P.ν * N) := by
    intro j
    rw [flowerWeighted_clip]
    have hM : 0 < (2 : ℝ) ^ j * P.L := by positivity
    exact H hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger j (fun _ => false) (fun _ => false) (fun _ => 0)
      (fun _ => ⟨le_rfl, (extractionRadius_pos (40 * P.d) N (hC P.d) (hU _ _) hM).le⟩)
  have hle := le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) hB
  have key : flowerSumP P (inputsF P R) p N kind pat dagger none none ζ t s n n' =
      flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger (fun _ _ => 1) ζ t s n n' := by
    rw [flowerWeighted_clip]
    simp only [flowerWeighted, flowerSumP, Option.elim_none, mul_one]
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim, mul_one]
  refine hle.trans ?_
  have hroot : 0 ≤ flowerRootBudget Pm P p ζ n n' := by
    unfold flowerRootBudget
    exact Real.rpow_nonneg (by unfold jbr; positivity) _
  unfold flowerLExponent at *
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hroot) ?_ (by positivity) (by unfold jbr; positivity)
  · refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    have : (0 : ℝ) ≤ (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) + ((2 * Pm : ℕ) : ℝ) := by positivity
    linarith
  · refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ?_
    have : (0 : ℝ) ≤ P.ν * N := by positivity
    nlinarith

end WaveTurbulence.FlowerTop
