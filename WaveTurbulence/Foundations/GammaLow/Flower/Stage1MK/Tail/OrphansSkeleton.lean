/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L8-I-ORPHANS port of main `WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonLeg` (marked part) and
-- `…Stage1.ClassCount.SkeletonCode.skeletonCodeLegMk` (sha256 in Tail/Orphans-COPIED-SHA256SUMS), over 𝒱_γ, modelled on
-- L5c's unmarked ports `Famc.ClassCount.{SkeletonLeg,SkeletonCode,Assembly}`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonLeg
/-! # Item I orphans: Leg 1 of the class count at a marking over `𝒱_γ`

Main's `SkeletonCodeLegMk`, `skeletonCodeLegMk`, `card_skeletons_order_leMk`, `SkeletonLegMk`,
`skeletonLegMk_of_codeLegMk` (B2d), over `𝒱_γ`: the marked vine set `Mk : Set (Fama.CLVineG γ S)` and
`ρ̄ = Famc.ClassCount.rbarOfMkG γ S σ Mk`; L5c's `𝒱_γ` unit family gives L5c's constants (`2^118`, `2^141` for main's
`2^57`, `2^80`). The structural code at a marking is L5c's `skeletonCode_{nonempty,empty}Mk`. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton Finset
open WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount (arcLists card_arcLists_le' card_le_of_arc_lists exists_iso_arcs_of_count
  pow_le_factorial_mul)

variable [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput]

/-- The structural code leg over `𝒱_γ` (main `SkeletonCodeLeg`): the molecule of a plain skeleton with a
prescription has an atom labelling whose arc multiset is realized by `arcLists` over the `𝒱_γ` unit family. -/
def SkeletonCodeLegMkLow : Prop :=
  ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) (Mk : Set (Fama.CLVineG γ S)), S.IsPlain →
    ∃ nsb : ℕ, nsb ≤ S.order ∧ ∃ ℓ : GBranch S.tree ≃ Fin S.order,
      ∃ L ∈ arcLists S.order (4 * rbarOfMkG γ S σ Mk) (unitFamily S.order nsb (rbarOfMkG γ S σ Mk) (S.order - nsb)),
        ∀ x : Fin S.order × Fin S.order,
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x


/-- Skeletons of order exactly `n` with `ρ̄ = r` (main `card_skeletons_order_le`). -/
theorem card_skeletons_order_leMkLow (hcode : SkeletonCodeLegMkLow) (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (n r : ℕ)
    (T : Finset (Garden (2 * R))) (h : ∀ S ∈ T, S.IsPlain ∧ S.order = n ∧ ∃ (σ : Prescription S) (Mk : Set (Fama.CLVineG γ S)), rbarOfMkG γ S σ Mk = r) :
    T.card ≤ 3 * (2 ^ 118) ^ n * (13 * r).factorial * ((20736 * R).factorial * 20736 ^ n) := by
  classical
  have hbd := card_le_of_arc_lists (R := R) (n := n) (allListsG n r) T (by
    intro S hS
    obtain ⟨hp, hord, σ, Mk, hr⟩ := h S hS
    refine ⟨hp, hord, ?_⟩
    obtain ⟨nsb, hnsb, ℓ, L, hL, hcount⟩ := hcode γ S σ Mk hp
    subst hord
    refine ⟨L, ?_, exists_iso_arcs_of_count S ℓ L hcount⟩
    unfold allListsG
    rw [hr] at hL
    exact Finset.mem_biUnion.mpr ⟨nsb, Finset.mem_range.mpr (by omega), hL⟩)
  refine hbd.trans ?_
  calc (allListsG n r).card * ((20736 * R).factorial * 20736 ^ n)
      ≤ (3 * (2 ^ 118) ^ n * (13 * r).factorial) * ((20736 * R).factorial * 20736 ^ n) :=
        Nat.mul_le_mul_right _ (card_allListsG_le n r)
    _ = _ := rfl


/-- **Leg 1 over `𝒱_γ`** (main `SkeletonLeg`): plain skeletons of order `≤ N` having a prescription with `ρ̄ = r`
number at most `C₀^N (C₀ r)! (C₀ R)!`, uniformly in `γ ≤ 1/2`. -/
def SkeletonLegMkLow : Prop :=
  ∃ C₀ : ℕ, 2 ≤ C₀ ∧ ∀ (γ : ℝ) (hγ : γ ≤ 1 / 2), ∀ R N r : ℕ, 1 ≤ R → 1 ≤ N → ∀ T : Finset (Garden (2 * R)),
    (∀ S ∈ T, S.IsPlain ∧ S.order ≤ N ∧ haveI : Fact (γ ≤ 1 / 2) := ⟨hγ⟩; ∃ (σ : Prescription S) (Mk : Set (Fama.CLVineG γ S)), rbarOfMkG γ S σ Mk = r) →
    (T.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ)


/-- **Leg 1 over `𝒱_γ`** from the code leg (main `skeletonLeg_of_codeLeg`). -/
theorem skeletonLegMk_of_codeLegMkLow (hcode : SkeletonCodeLegMkLow) : SkeletonLegMkLow := by
  classical
  refine ⟨2 ^ 141, by norm_num, ?_⟩
  intro γ hγ R N r hR hN T hT
  have : Fact (γ ≤ 1 / 2) := ⟨hγ⟩
  have hfib : ∀ n ∈ Finset.range (N + 1), (T.filter (fun S => S.order = n)).card ≤
      3 * (2 ^ 118) ^ N * (13 * r).factorial * ((20736 * R).factorial * 20736 ^ N) := by
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have := card_skeletons_order_leMkLow hcode γ n r (T.filter (fun S => S.order = n)) (by
      intro S hS
      obtain ⟨hS1, hS2⟩ := Finset.mem_filter.mp hS
      obtain ⟨hp, -, σ, Mk, hr⟩ := hT S hS1
      exact ⟨hp, hS2, σ, Mk, hr⟩)
    refine this.trans ?_
    gcongr
  have hsum : T.card ≤ ∑ n ∈ Finset.range (N + 1), (T.filter (fun S => S.order = n)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := T) (t := Finset.range (N + 1)) (f := fun S => S.order)
      (fun S hS => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le (hT S hS).2.1)))
    exact this.le
  have hcard : T.card ≤ (N + 1) * (3 * (2 ^ 118) ^ N * (13 * r).factorial *
      ((20736 * R).factorial * 20736 ^ N)) := by
    refine hsum.trans ?_
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hN2 : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
  have hfr : (13 * r).factorial ≤ (2 ^ 141 * r).factorial := Nat.factorial_le (by nlinarith)
  have hfR : (20736 * R).factorial ≤ (2 ^ 141 * R).factorial := Nat.factorial_le (by nlinarith)
  have h3 : 3 ≤ 3 ^ N := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hs1 : (N + 1) * (3 * (2 ^ 118) ^ N * (13 * r).factorial * ((20736 * R).factorial * 20736 ^ N)) ≤
      2 ^ N * (3 ^ N * (2 ^ 118) ^ N * (2 ^ 141 * r).factorial * ((2 ^ 141 * R).factorial * 20736 ^ N)) := by
    gcongr
  have hs2 : 2 ^ N * (3 ^ N * (2 ^ 118) ^ N * (2 ^ 141 * r).factorial * ((2 ^ 141 * R).factorial * 20736 ^ N)) =
      (2 * 3 * 2 ^ 118 * 20736) ^ N * (2 ^ 141 * r).factorial * (2 ^ 141 * R).factorial := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  have hs3 : (2 * 3 * 2 ^ 118 * 20736) ^ N * (2 ^ 141 * r).factorial * (2 ^ 141 * R).factorial ≤
      (2 ^ 141) ^ N * (2 ^ 141 * r).factorial * (2 ^ 141 * R).factorial := by
    have : 2 * 3 * 2 ^ 118 * 20736 ≤ 2 ^ 141 := by norm_num
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left this N))
  have hmain : T.card ≤ (2 ^ 141) ^ N * (2 ^ 141 * r).factorial * (2 ^ 141 * R).factorial :=
    hcard.trans (hs1.trans (hs2.le.trans hs3))
  exact_mod_cast hmain


/-- **`SkeletonCodeLeg` over `𝒱_γ`** (main `skeletonCodeLeg`, via `skeletonCodeLegMk` at `Mk = ∅`): the structural
code leg, with the T-branch of the unit decoding (`chain_decode`, `vine_chain_codeG`). -/
theorem skeletonCodeLegMkLow : SkeletonCodeLegMkLow := by
  intro γ _ R S σ Mk hS
  classical
  have hcard : Fintype.card (GBranch S.tree) = S.order := by
    rw [← Mole.garden_card_atoms S, ← Finset.card_univ]; rfl
  rw [← hcard]
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    exact skeletonCode_nonemptyMk S σ Mk v0
  · exact skeletonCode_emptyMk S σ Mk (not_nonempty_iff.mp hne)


end WaveTurbulence.GammaLow.Flower
