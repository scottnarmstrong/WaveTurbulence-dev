/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonLeg
/-! # CLASSCOUNT over `𝒱_γ`: Leg 1 (the number of skeletons) from the code leg (packet L5c, item I)

L5c port of main `WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonLeg` (sha256 in COPIED-SHA256SUMS), the
`SkeletonLeg` part. Over `𝒱_γ` the units are coded by the `𝒱_γ` ingredient codes (`unitFamily` over `IngCodeG`,
`card_unitFamily_le : ≤ (2^105)^E n^r`, item H), so main's constants `2^57`, `2^80` become `2^118`, `2^141`;
`ρ̄` is `rbarOfG γ`. Main's family-free `arcLists`, `card_arcLists_le'`, `card_le_of_arc_lists`,
`exists_iso_arcs_of_count`, `pow_le_factorial_mul` are used by import. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton Finset
open WaveTurbulence.ClassCount (arcLists card_arcLists_le' card_le_of_arc_lists exists_iso_arcs_of_count
  pow_le_factorial_mul)

variable [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput]

/-- The structural code leg over `𝒱_γ` (main `SkeletonCodeLeg`): the molecule of a plain skeleton with a
prescription has an atom labelling whose arc multiset is realized by `arcLists` over the `𝒱_γ` unit family. -/
def SkeletonCodeLegG : Prop :=
  ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S), S.IsPlain →
    ∃ nsb : ℕ, nsb ≤ S.order ∧ ∃ ℓ : GBranch S.tree ≃ Fin S.order,
      ∃ L ∈ arcLists S.order (4 * rbarOfG γ S σ) (unitFamily S.order nsb (rbarOfG γ S σ) (S.order - nsb)),
        ∀ x : Fin S.order × Fin S.order,
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x

/-- All arc lists for `n` atoms and `ρ̄ = r` (over the `𝒱_γ` unit family). -/
noncomputable def allListsG (n r : ℕ) : Finset (List (Fin n × Fin n)) :=
  (Finset.range (n + 1)).biUnion (fun nsb => arcLists n (4 * r) (unitFamily n nsb r (n - nsb)))

theorem card_allListsG_le (n r : ℕ) : (allListsG n r).card ≤ 3 * (2 ^ 118) ^ n * (13 * r).factorial := by
  unfold allListsG
  refine Finset.card_biUnion_le.trans ?_
  have hterm : ∀ nsb ∈ Finset.range (n + 1),
      (arcLists n (4 * r) (unitFamily n nsb r (n - nsb))).card ≤
        3 ^ (5 * n) * 3 ^ (n + 1) * ((2 ^ 105) ^ n * n ^ r) * (12 * r).factorial := by
    intro nsb _
    refine (card_arcLists_le' n (4 * r) _).trans ?_
    have h1 : (unitFamily n nsb r (n - nsb)).card ≤ (2 ^ 105) ^ n * n ^ r :=
      (card_unitFamily_le n nsb r (n - nsb)).trans
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)) le_rfl)
    have : 3 * (4 * r) = 12 * r := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h3 : n ^ r ≤ r.factorial * 3 ^ n := pow_le_factorial_mul n r
  have h4 : r.factorial * (12 * r).factorial ≤ (13 * r).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add r (12 * r)
    have h5 : r + 12 * r = 13 * r := by ring
    rw [h5] at this
    exact Nat.le_of_dvd (Nat.factorial_pos _) this
  have h6 : 2 * 3 ^ 7 * 2 ^ 105 ≤ 2 ^ 118 := by norm_num
  calc (n + 1) * (3 ^ (5 * n) * 3 ^ (n + 1) * ((2 ^ 105) ^ n * n ^ r) * (12 * r).factorial)
      ≤ 2 ^ n * (3 ^ (5 * n) * 3 ^ (n + 1) * ((2 ^ 105) ^ n * (r.factorial * 3 ^ n)) * (12 * r).factorial) := by
        gcongr
    _ = 3 * (2 * 3 ^ 7 * 2 ^ 105) ^ n * (r.factorial * (12 * r).factorial) := by
        have : 2 ^ n * 3 ^ (7 * n) * (2 ^ 105) ^ n = (2 * 3 ^ 7 * 2 ^ 105) ^ n := by
          rw [pow_mul, ← mul_pow, ← mul_pow]
        rw [← this]
        ring
    _ ≤ 3 * (2 ^ 118) ^ n * (13 * r).factorial := by
        gcongr

/-- Skeletons of order exactly `n` with `ρ̄ = r` (main `card_skeletons_order_le`). -/
theorem card_skeletons_order_leG (hcode : SkeletonCodeLegG) (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} (n r : ℕ)
    (T : Finset (Garden (2 * R))) (h : ∀ S ∈ T, S.IsPlain ∧ S.order = n ∧ ∃ σ : Prescription S, rbarOfG γ S σ = r) :
    T.card ≤ 3 * (2 ^ 118) ^ n * (13 * r).factorial * ((20736 * R).factorial * 20736 ^ n) := by
  classical
  have hbd := card_le_of_arc_lists (R := R) (n := n) (allListsG n r) T (by
    intro S hS
    obtain ⟨hp, hord, σ, hr⟩ := h S hS
    refine ⟨hp, hord, ?_⟩
    obtain ⟨nsb, hnsb, ℓ, L, hL, hcount⟩ := hcode γ S σ hp
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

/-- **Leg 1 over `𝒱_γ`** from the code leg (main `skeletonLeg_of_codeLeg`). -/
theorem skeletonLegG_of_codeLeg (hcode : SkeletonCodeLegG) : SkeletonLegG := by
  classical
  refine ⟨2 ^ 141, by norm_num, ?_⟩
  intro γ hγ R N r hR hN T hT
  have : Fact (γ ≤ 1 / 2) := ⟨hγ⟩
  have hfib : ∀ n ∈ Finset.range (N + 1), (T.filter (fun S => S.order = n)).card ≤
      3 * (2 ^ 118) ^ N * (13 * r).factorial * ((20736 * R).factorial * 20736 ^ N) := by
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have := card_skeletons_order_leG hcode γ n r (T.filter (fun S => S.order = n)) (by
      intro S hS
      obtain ⟨hS1, hS2⟩ := Finset.mem_filter.mp hS
      obtain ⟨hp, -, σ, hr⟩ := hT S hS1
      exact ⟨hp, hS2, σ, hr⟩)
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

end WaveTurbulence.GammaLow.Famc.ClassCount
