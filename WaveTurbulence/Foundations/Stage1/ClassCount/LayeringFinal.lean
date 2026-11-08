/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.ClassCount.KeyedBound
public import WaveTurbulence.Foundations.Stage1.ClassCount.Assembly
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitListCount
import Mathlib.Tactic

/-!
# CLASSCOUNT: `LayeringLeg` (TARGET L2248-L2252)

The layered gardens decoded by `D` over `S` and carrying a Stage 1 piece of data `(g, r)` are counted by splitting
into the `≤ 2^n` classes of effective prescriptions (`unitBlocks S σ`), then by key (`keyed_bound`); the constants are
absorbed using `K^(P.D+1) ≤ P.C₂`.
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine

theorem final_numerics {K0 : ℝ} {Kn : ℕ} (hK0 : 2 ≤ K0) (hKn : K0 ≤ Kn) {p g r N : ℕ} (hN : 1 ≤ N) {C2 cardA : ℝ}
    (hC2 : (K0 ^ (p + 1)) ^ 25 ≤ C2)
    (hcard : cardA ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)))) :
    cardA ≤ (((2 ^ 5 * Kn ^ 4 : ℕ)) : ℝ) ^ N * C2 ^ (g + r) := by
  have hK1 : 1 ≤ K0 := by linarith
  have hK00 : 0 ≤ K0 := by linarith
  set X : ℝ := K0 ^ (p + 1) with hX
  have hX2 : 2 ≤ X := by
    calc (2 : ℝ) ≤ K0 := hK0
      _ ≤ K0 ^ (p + 1) := by
        calc K0 = K0 ^ 1 := (pow_one _).symm
          _ ≤ K0 ^ (p + 1) := pow_le_pow_right₀ hK1 (by omega)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h2pow : (2 : ℝ) ^ (2 * g + r) ≤ X ^ (2 * g + r) := pow_le_pow_left₀ (by norm_num) hX2 _
  have hK4 : K0 ^ (4 * N) ≤ ((Kn : ℝ) ^ 4) ^ N := by
    rw [← pow_mul]; exact pow_le_pow_left₀ hK00 hKn _ 
  have h2 : (2 : ℝ) ^ (4 * N + 1) ≤ (2 ^ 5) ^ N := by
    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hXC : X ^ (25 * (g + r)) ≤ C2 ^ (g + r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hC2 _
  have hC2nn : 0 ≤ C2 := le_trans (by positivity) hC2
  calc cardA ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) * (2 ^ N * K0 ^ (4 * N) * X ^ (24 * r + 15 * g))) := hcard
    _ = (2 : ℝ) ^ (4 * N + 1) * (2 : ℝ) ^ (2 * g + r) * K0 ^ (4 * N) * X ^ (24 * r + 15 * g) := by
        rw [show (2 * g + 1 + N + N + r) = (2 * g + r) + (N + N + 1) by ring, pow_add (2 : ℝ) (2 * g + r)]
        rw [show (4 * N + 1) = N + ((N + N + 1) + N) by ring, pow_add, pow_add]
        ring
    _ ≤ (2 ^ 5) ^ N * X ^ (2 * g + r) * ((Kn : ℝ) ^ 4) ^ N * X ^ (24 * r + 15 * g) := by
        gcongr
    _ = ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * X ^ (25 * r + 17 * g) := by
        rw [mul_pow, show 25 * r + 17 * g = (2 * g + r) + (24 * r + 15 * g) by ring, pow_add]
        ring
    _ ≤ ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * X ^ (25 * (g + r)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (by omega)) (by positivity)
    _ ≤ ((2 ^ 5 : ℝ) * (Kn : ℝ) ^ 4) ^ N * C2 ^ (g + r) :=
        mul_le_mul_of_nonneg_left hXC (by positivity)
    _ = _ := by push_cast; ring

open Classical in
/-- B1b (R156): `layeringLeg` with the truncation-free carrier `Stage1CarriesW`. -/
theorem layeringLegW : LayeringLegW := by
  obtain ⟨K0, hK0, hKB⟩ := keyed_bound
  set Kn : ℕ := ⌈K0⌉₊ with hKn_def
  have hKn : K0 ≤ (Kn : ℝ) := Nat.le_ceil K0
  have hKn2 : (2 : ℝ) ≤ Kn := le_trans hK0 hKn
  have hKn1 : 1 ≤ Kn := by exact_mod_cast (by linarith : (1 : ℝ) ≤ Kn)
  refine ⟨2 ^ 5 * Kn ^ 4, Kn ^ 25, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  intro P hK p hp R hR N hN g r S D A' hSpl hord hA'
  have hK' : ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) ≤ P.C₂ := by exact_mod_cast hK
  have hC2nn : 0 ≤ P.C₂ := le_trans (by positivity) hK'
  by_cases hAe : A' = ∅
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨LG1, hLG1⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  have hex : ∀ LG ∈ A', ∃ σ : Prescription S, ∃ hd : D.Decodes hSpl LG.garden,
      rbarOf S σ = r ∧ (stage1PieceOf P.d hSpl LG hd σ).gbar = g := by
    intro LG hLG
    obtain ⟨-, hS', hd, σ, hr, hg⟩ := hA' LG hLG
    exact ⟨σ, hd, hr, hg⟩
  haveI : Nonempty (Prescription S) := ⟨(hex LG1 hLG1).choose⟩
  choose! σf hdf hrf hgf using hex
  have hcan : ∀ LG ∈ A', IsCanonGC (p + 1) LG := fun LG h => (hA' LG h).1.1
  have hsize : D.size ≤ N := by
    have h1 := decodeSizeLeg S D hSpl LG1.garden (hdf LG1 hLG1)
    have h2 : LG1.garden.order = N := (hA' LG1 hLG1).1.2.1
    omega
  have hn : Fintype.card (GBranch S.tree) ≤ N := by
    rw [Mole.card_gbranch]; exact hord
  set X : ℝ := K0 ^ (p + 1) with hX
  have hXC : X ^ 25 ≤ P.C₂ := by
    have hK1 : 1 ≤ K0 := by linarith
    calc X ^ 25 = (K0 ^ 25) ^ (p + 1) := by rw [hX, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((Kn : ℝ) ^ 25) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by linarith) hKn _) _
      _ ≤ ((Kn : ℝ) ^ 25) ^ (P.D + 1) :=
          pow_le_pow_right₀ (one_le_pow₀ (by exact_mod_cast hKn1)) (by omega)
      _ = ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) := by push_cast; ring
      _ ≤ P.C₂ := hK'
  set cls : LayeredGarden (2 * R) → Finset (Finset (GBranch S.tree)) :=
    fun LG => (groupsFinset S).filter (fun T => σf LG T = Molecule.GapKind.SG) with hcls
  have hmaps : ∀ LG ∈ A', cls LG ∈ (groupsFinset S).powerset := fun LG _ =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hfib : A'.card = ∑ 𝒢 ∈ (groupsFinset S).powerset, (A'.filter (fun LG => cls LG = 𝒢)).card :=
    Finset.card_eq_sum_card_fiberwise (fun LG hLG => hmaps LG hLG)
  have hcl : ∀ 𝒢 ∈ (groupsFinset S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ) ≤
      (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by
    intro 𝒢 h𝒢
    set Ac := A'.filter (fun LG => cls LG = 𝒢) with hAc
    have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
    by_cases hemp : Ac = ∅
    · rw [hemp]; simpa using hpos0
    obtain ⟨LGs, hLGs⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    obtain ⟨hLGsA, hLGsc⟩ := Finset.mem_filter.1 hLGs
    have hAcl : ∀ LG ∈ Ac, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hSpl LG.garden,
        gbarRHS D hSpl LG (stSt S (σf LGs)) (Set.toFinite (unitIngredients S (σf LGs))).toFinset = g := by
      intro LG hLG
      obtain ⟨hLA, hc⟩ := Finset.mem_filter.1 hLG
      have heq : unitBlocks S (σf LG) = unitBlocks S (σf LGs) :=
        unitBlocks_eq_of_filter_eq S _ _ (hc.trans hLGsc.symm)
      refine ⟨hcan LG hLA, hdf LG hLA, ?_⟩
      rw [← gbar_eq_gbarRHS P.d hSpl LG (hdf LG hLA) (σf LGs)]
      exact (gbar_rbar_eq_of_unitBlocks_eq P.d hSpl LG (hdf LG hLA) (σf LG) (σf LGs) heq).1.symm.trans
        (hgf LG hLA)
    have hr' : (stSt S (σf LGs)).G.molecule.rho + (unitBlocks S (σf LGs)).length ≤ r :=
      (rho_add_length_le_rbarOf S (σf LGs)).trans (hrf LGs hLGsA).le
    exact hKB S hSpl D (σf LGs) p g r N Ac hAcl hr' hsize hn
  have hpow : (((groupsFinset S).powerset.card : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
    rw [Finset.card_powerset]
    have : 2 ^ (groupsFinset S).card ≤ 2 ^ N :=
      Nat.pow_le_pow_right (by norm_num) ((card_groupsFinset_le S).trans hn)
    exact_mod_cast this
  have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
  have htot : (A'.card : ℝ) ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
    rw [hfib, Nat.cast_sum]
    calc ∑ 𝒢 ∈ (groupsFinset S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ)
        ≤ ∑ 𝒢 ∈ (groupsFinset S).powerset, ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := Finset.sum_le_sum hcl
      _ = (((groupsFinset S).powerset.card : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow hpos0
  exact final_numerics hK0 hKn hN (hXC) htot

/-- B2d: the count of unit lists, `(r + 1) (N + 2)^{4r}`, is at most `(3^12)^N (5 r)!`. -/
theorem unitBlockLists_numerics (N r : ℕ) (hN : 1 ≤ N) :
    (r + 1) * (N + 2) ^ (4 * r) ≤ (3 ^ 12) ^ N * (5 * r).factorial := by
  have h1 : (N + 2) ^ r ≤ r.factorial * 3 ^ (N + 2) := pow_le_factorial_mul (N + 2) r
  have h2 : (N + 2) ^ (4 * r) ≤ r.factorial ^ 4 * 3 ^ (4 * N + 8) := by
    calc (N + 2) ^ (4 * r) = ((N + 2) ^ r) ^ 4 := by rw [← pow_mul, mul_comm]
      _ ≤ (r.factorial * 3 ^ (N + 2)) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = r.factorial ^ 4 * 3 ^ (4 * N + 8) := by rw [mul_pow, ← pow_mul]; ring_nf
  have hf : ∀ a : ℕ, a.factorial * r.factorial ≤ (a + r).factorial := fun a =>
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a r)
  have h3 : r.factorial ^ 4 ≤ (4 * r).factorial := by
    have e2 := hf r
    have e3 := hf (r + r)
    have e4 := hf (r + r + r)
    calc r.factorial ^ 4 = ((r.factorial * r.factorial) * r.factorial) * r.factorial := by ring
      _ ≤ (((r + r).factorial) * r.factorial) * r.factorial := by gcongr
      _ ≤ (r + r + r).factorial * r.factorial := by gcongr
      _ ≤ (r + r + r + r).factorial := e4
      _ = (4 * r).factorial := by ring_nf
  have h4 : (r + 1) * (4 * r).factorial ≤ (5 * r).factorial := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · calc (r + 1) * (4 * r).factorial ≤ (4 * r + 1) * (4 * r).factorial :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (4 * r + 1).factorial := (Nat.factorial_succ _).symm
        _ ≤ (5 * r).factorial := Nat.factorial_le (by omega)
  have h5 : 3 ^ (4 * N + 8) ≤ (3 ^ 12) ^ N := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (r + 1) * (N + 2) ^ (4 * r) ≤ (r + 1) * (r.factorial ^ 4 * 3 ^ (4 * N + 8)) := Nat.mul_le_mul_left _ h2
    _ = ((r + 1) * r.factorial ^ 4) * 3 ^ (4 * N + 8) := by ring
    _ ≤ ((r + 1) * (4 * r).factorial) * (3 ^ 12) ^ N := by gcongr
    _ ≤ (5 * r).factorial * (3 ^ 12) ^ N := Nat.mul_le_mul_right _ h4
    _ = (3 ^ 12) ^ N * (5 * r).factorial := by ring

open Classical in
/-- B2d: **`LayeringLegMk`**: the layering count for Stage 1′ pieces at any marked set.  The gardens are split by the
unit list `unitBlocks S σ Mk` of their piece (`card_unitBlockLists_le`: at most `(r + 1) (N + 2)^{4r}` lists, as
`#units ≤ ρ̄ = r`); in one class `(ḡ, ρ̄)` is computed from the common splice state (`gbar_rbar_eq_of_unitBlocks_eqMk`)
and `keyed_boundMk` applies. -/
theorem layeringLegMk : LayeringLegMk := by
  obtain ⟨K0, hK0, hKB⟩ := keyed_boundMk
  set Kn : ℕ := ⌈K0⌉₊ with hKn_def
  have hKn : K0 ≤ (Kn : ℝ) := Nat.le_ceil K0
  have hKn2 : (2 : ℝ) ≤ Kn := le_trans hK0 hKn
  have hKn1 : 1 ≤ Kn := by exact_mod_cast (by linarith : (1 : ℝ) ≤ Kn)
  have hKn2' : 2 ≤ Kn := by exact_mod_cast hKn2
  refine ⟨2 ^ 5 * Kn ^ 4 * 3 ^ 12, Kn ^ 25, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  intro P hK p hp R hR N hN g r S D A' hSpl hord hA'
  have hK' : ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) ≤ P.C₂ := by exact_mod_cast hK
  have hC2nn : 0 ≤ P.C₂ := le_trans (by positivity) hK'
  have hpos : (0 : ℝ) ≤ ((2 ^ 5 * Kn ^ 4 * 3 ^ 12 : ℕ) : ℝ) ^ N *
      ((((2 ^ 5 * Kn ^ 4 * 3 ^ 12) * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r) := by positivity
  by_cases hAe : A' = ∅
  · subst hAe
    simpa using hpos
  obtain ⟨LG1, hLG1⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  have hex : ∀ LG ∈ A', ∃ σ : Prescription S, ∃ Mk : Set (Stage1.CLVine S), ∃ hd : D.Decodes hSpl LG.garden,
      rbarOfMk S σ Mk = r ∧ (stage1PieceOf P.d hSpl LG hd σ Mk).gbar = g := by
    intro LG hLG
    obtain ⟨-, hS', hd, σ, Mk, hr, hg⟩ := hA' LG hLG
    exact ⟨σ, Mk, hd, hr, hg⟩
  have : Nonempty (Prescription S) := ⟨(hex LG1 hLG1).choose⟩
  choose! σf Mkf hdf hrf hgf using hex
  have hcan : ∀ LG ∈ A', IsCanonGC (p + 1) LG := fun LG h => (hA' LG h).1.1
  have hsize : D.size ≤ N := by
    have h1 := decodeSizeLeg S D hSpl LG1.garden (hdf LG1 hLG1)
    have h2 : LG1.garden.order = N := (hA' LG1 hLG1).1.2.1
    omega
  have hn : Fintype.card (GBranch S.tree) ≤ N := by
    rw [Mole.card_gbranch]; exact hord
  set X : ℝ := K0 ^ (p + 1) with hX
  have hXC : X ^ 25 ≤ P.C₂ := by
    have hK1 : 1 ≤ K0 := by linarith
    calc X ^ 25 = (K0 ^ 25) ^ (p + 1) := by rw [hX, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((Kn : ℝ) ^ 25) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by linarith) hKn _) _
      _ ≤ ((Kn : ℝ) ^ 25) ^ (P.D + 1) :=
          pow_le_pow_right₀ (one_le_pow₀ (by exact_mod_cast hKn1)) (by omega)
      _ = ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) := by push_cast; ring
      _ ≤ P.C₂ := hK'
  set U : LayeredGarden (2 * R) → List (CLBlock S) := fun LG => unitBlocks S (σf LG) (Mkf LG) with hU
  have hfib : A'.card = ∑ U0 ∈ A'.image U, (A'.filter (fun LG => U LG = U0)).card :=
    Finset.card_eq_sum_card_image U A'
  set B : ℝ := (2 : ℝ) ^ (2 * g + 1 + N + N + r) * (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))
    with hB
  have hB0 : 0 ≤ B := by positivity
  have hcl : ∀ U0 ∈ A'.image U, ((A'.filter (fun LG => U LG = U0)).card : ℝ) ≤ B := by
    intro U0 hU0
    set Ac := A'.filter (fun LG => U LG = U0) with hAc
    by_cases hemp : Ac = ∅
    · rw [hemp]; simpa using hB0
    obtain ⟨LGs, hLGs⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    obtain ⟨hLGsA, hLGsc⟩ := Finset.mem_filter.1 hLGs
    have hAcl : ∀ LG ∈ Ac, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hSpl LG.garden,
        gbarRHS D hSpl LG (stSt S (σf LGs) (Mkf LGs))
          (Set.toFinite (unitIngredients S (σf LGs) (Mkf LGs))).toFinset = g := by
      intro LG hLG
      obtain ⟨hLA, hc⟩ := Finset.mem_filter.1 hLG
      have heq : unitBlocks S (σf LG) (Mkf LG) = unitBlocks S (σf LGs) (Mkf LGs) := hc.trans hLGsc.symm
      refine ⟨hcan LG hLA, hdf LG hLA, ?_⟩
      rw [← gbar_eq_gbarRHSMk P.d hSpl LG (hdf LG hLA) (σf LGs) (Mkf LGs)]
      exact (gbar_rbar_eq_of_unitBlocks_eqMk P.d hSpl LG (hdf LG hLA) (σf LG) (σf LGs) (Mkf LG) (Mkf LGs)
        heq).1.symm.trans (hgf LG hLA)
    have hr' : (stSt S (σf LGs) (Mkf LGs)).G.molecule.rho + (unitBlocks S (σf LGs) (Mkf LGs)).length ≤ r :=
      (rho_add_length_le_rbarOfMk S (σf LGs) (Mkf LGs)).trans (hrf LGs hLGsA).le
    exact hKB S hSpl D (σf LGs) (Mkf LGs) p g r N Ac hAcl hr' hsize hn
  -- the number of unit lists
  have hnum : (A'.image U).card ≤ (3 ^ 12) ^ N * (5 * r).factorial := by
    refine (card_unitBlockLists_le S r (A'.image U) ?_).trans ?_
    · intro U0 hU0
      obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hU0
      refine ⟨⟨σf LG, Mkf LG, rfl⟩, ?_⟩
      have := rho_add_length_le_rbarOfMk S (σf LG) (Mkf LG)
      have := hrf LG hLG
      show (unitBlocks S (σf LG) (Mkf LG)).length ≤ r
      omega
    · refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : Fintype.card (GBranch S.tree) + 2 ≤ N + 2) _)) ?_
      exact unitBlockLists_numerics N r hN
  have htot : (A'.card : ℝ) ≤ (((3 ^ 12) ^ N * (5 * r).factorial : ℕ) : ℝ) * B := by
    rw [hfib, Nat.cast_sum]
    calc ∑ U0 ∈ A'.image U, ((A'.filter (fun LG => U LG = U0)).card : ℝ)
        ≤ ∑ U0 ∈ A'.image U, B := Finset.sum_le_sum hcl
      _ = (((A'.image U).card : ℕ) : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hnum) hB0
  -- the old numerics, applied to `2^N B`
  have hfin := final_numerics hK0 hKn hN hXC (le_refl ((2 : ℝ) ^ N * B))
  have hBle : B ≤ ((2 ^ 5 * Kn ^ 4 : ℕ) : ℝ) ^ N * P.C₂ ^ (g + r) := by
    refine le_trans ?_ hfin
    have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  have hfact : ((5 * r).factorial : ℝ) ≤ (((2 ^ 5 * Kn ^ 4 * 3 ^ 12) * r).factorial : ℝ) := by
    have : 5 ≤ 2 ^ 5 * Kn ^ 4 * 3 ^ 12 := by
      have : 1 ≤ Kn ^ 4 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_right _ this)
  calc (A'.card : ℝ) ≤ (((3 ^ 12) ^ N * (5 * r).factorial : ℕ) : ℝ) * B := htot
    _ ≤ (((3 ^ 12) ^ N * (5 * r).factorial : ℕ) : ℝ) * (((2 ^ 5 * Kn ^ 4 : ℕ) : ℝ) ^ N * P.C₂ ^ (g + r)) :=
        mul_le_mul_of_nonneg_left hBle (by positivity)
    _ = (((2 ^ 5 * Kn ^ 4 * 3 ^ 12 : ℕ) : ℝ)) ^ N * ((5 * r).factorial : ℝ) * P.C₂ ^ (g + r) := by
        push_cast; rw [mul_pow, mul_pow, mul_pow]; ring
    _ ≤ (((2 ^ 5 * Kn ^ 4 * 3 ^ 12 : ℕ) : ℝ)) ^ N * ((((2 ^ 5 * Kn ^ 4 * 3 ^ 12) * r).factorial : ℕ) : ℝ) *
          P.C₂ ^ (g + r) := by
        gcongr
  exact le_rfl

open Classical in
/-- **`LayeringLeg`** (TARGET L2248-L2252). -/
theorem layeringLeg : LayeringLeg := by
  obtain ⟨K0, hK0, hKB⟩ := keyed_bound
  set Kn : ℕ := ⌈K0⌉₊ with hKn_def
  have hKn : K0 ≤ (Kn : ℝ) := Nat.le_ceil K0
  have hKn2 : (2 : ℝ) ≤ Kn := le_trans hK0 hKn
  have hKn1 : 1 ≤ Kn := by exact_mod_cast (by linarith : (1 : ℝ) ≤ Kn)
  refine ⟨2 ^ 5 * Kn ^ 4, Kn ^ 25, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  intro P hK p hp R hR N hN g r S D A' hSpl hord hA'
  have hK' : ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) ≤ P.C₂ := by exact_mod_cast hK
  have hC2nn : 0 ≤ P.C₂ := le_trans (by positivity) hK'
  by_cases hAe : A' = ∅
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨LG1, hLG1⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  have hex : ∀ LG ∈ A', ∃ σ : Prescription S, ∃ hd : D.Decodes hSpl LG.garden,
      rbarOf S σ = r ∧ (stage1PieceOf P.d hSpl LG hd σ).gbar = g := by
    intro LG hLG
    obtain ⟨-, hS', hd, σ, hr, hg⟩ := hA' LG hLG
    exact ⟨σ, hd, hr, hg⟩
  haveI : Nonempty (Prescription S) := ⟨(hex LG1 hLG1).choose⟩
  choose! σf hdf hrf hgf using hex
  have hcan : ∀ LG ∈ A', IsCanonGC (p + 1) LG := fun LG h => (hA' LG h).1.1
  have hsize : D.size ≤ N := by
    have h1 := decodeSizeLeg S D hSpl LG1.garden (hdf LG1 hLG1)
    have h2 : LG1.garden.order = N := (hA' LG1 hLG1).1.2.2.1
    omega
  have hn : Fintype.card (GBranch S.tree) ≤ N := by
    rw [Mole.card_gbranch]; exact hord
  set X : ℝ := K0 ^ (p + 1) with hX
  have hXC : X ^ 25 ≤ P.C₂ := by
    have hK1 : 1 ≤ K0 := by linarith
    calc X ^ 25 = (K0 ^ 25) ^ (p + 1) := by rw [hX, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((Kn : ℝ) ^ 25) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by linarith) hKn _) _
      _ ≤ ((Kn : ℝ) ^ 25) ^ (P.D + 1) :=
          pow_le_pow_right₀ (one_le_pow₀ (by exact_mod_cast hKn1)) (by omega)
      _ = ((Kn ^ 25 : ℕ) : ℝ) ^ (P.D + 1) := by push_cast; ring
      _ ≤ P.C₂ := hK'
  set cls : LayeredGarden (2 * R) → Finset (Finset (GBranch S.tree)) :=
    fun LG => (groupsFinset S).filter (fun T => σf LG T = Molecule.GapKind.SG) with hcls
  have hmaps : ∀ LG ∈ A', cls LG ∈ (groupsFinset S).powerset := fun LG _ =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hfib : A'.card = ∑ 𝒢 ∈ (groupsFinset S).powerset, (A'.filter (fun LG => cls LG = 𝒢)).card :=
    Finset.card_eq_sum_card_fiberwise (fun LG hLG => hmaps LG hLG)
  have hcl : ∀ 𝒢 ∈ (groupsFinset S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ) ≤
      (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by
    intro 𝒢 h𝒢
    set Ac := A'.filter (fun LG => cls LG = 𝒢) with hAc
    have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
        (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
    by_cases hemp : Ac = ∅
    · rw [hemp]; simpa using hpos0
    obtain ⟨LGs, hLGs⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    obtain ⟨hLGsA, hLGsc⟩ := Finset.mem_filter.1 hLGs
    have hAcl : ∀ LG ∈ Ac, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hSpl LG.garden,
        gbarRHS D hSpl LG (stSt S (σf LGs)) (Set.toFinite (unitIngredients S (σf LGs))).toFinset = g := by
      intro LG hLG
      obtain ⟨hLA, hc⟩ := Finset.mem_filter.1 hLG
      have heq : unitBlocks S (σf LG) = unitBlocks S (σf LGs) :=
        unitBlocks_eq_of_filter_eq S _ _ (hc.trans hLGsc.symm)
      refine ⟨hcan LG hLA, hdf LG hLA, ?_⟩
      rw [← gbar_eq_gbarRHS P.d hSpl LG (hdf LG hLA) (σf LGs)]
      exact (gbar_rbar_eq_of_unitBlocks_eq P.d hSpl LG (hdf LG hLA) (σf LG) (σf LGs) heq).1.symm.trans
        (hgf LG hLA)
    have hr' : (stSt S (σf LGs)).G.molecule.rho + (unitBlocks S (σf LGs)).length ≤ r :=
      (rho_add_length_le_rbarOf S (σf LGs)).trans (hrf LGs hLGsA).le
    exact hKB S hSpl D (σf LGs) p g r N Ac hAcl hr' hsize hn
  have hpow : (((groupsFinset S).powerset.card : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
    rw [Finset.card_powerset]
    have : 2 ^ (groupsFinset S).card ≤ 2 ^ N :=
      Nat.pow_le_pow_right (by norm_num) ((card_groupsFinset_le S).trans hn)
    exact_mod_cast this
  have hpos0 : 0 ≤ (2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g)) := by positivity
  have htot : (A'.card : ℝ) ≤ 2 ^ N * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
      (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
    rw [hfib, Nat.cast_sum]
    calc ∑ 𝒢 ∈ (groupsFinset S).powerset, ((A'.filter (fun LG => cls LG = 𝒢)).card : ℝ)
        ≤ ∑ 𝒢 ∈ (groupsFinset S).powerset, ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := Finset.sum_le_sum hcl
      _ = (((groupsFinset S).powerset.card : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * g + 1 + N + N + r) *
          (2 ^ N * K0 ^ (4 * N) * (K0 ^ (p + 1)) ^ (24 * r + 15 * g))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow hpos0
  exact final_numerics hK0 hKn hN (hXC) htot

end WaveTurbulence.ClassCount
