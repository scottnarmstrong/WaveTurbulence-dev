/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L8-I-ORPHANS port of main `WaveTurbulence.Foundations.Stage1.ClassCount.LayeringFinal.layeringLegMk` and
-- `…Stage1.ClassCount.Assembly.LayeringLegMk` (sha256 in Tail/Orphans-COPIED-SHA256SUMS), over 𝒱_γ, on L5c's ports.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.LayeringFinal
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.Stage1.ClassCount.LayeringFinal
import Mathlib.Tactic
/-! # Item I orphans: Leg 2 of the class count at a marking over `𝒱_γ`

Main's `LayeringLegMk` (B2d: pieces `stage1PieceOf … σ Mk` at any marked set, truncation-free carrier) and its proof
`layeringLegMk` over `𝒱_γ`: L5c's `keyed_boundMk`, `gbar_eq_gbarRHSMk`, `gbar_rbar_eq_of_unitBlocks_eqMk`,
`rho_add_length_le_rbarOfMk`, `card_unitBlockLists_le`, `final_numerics` at the family `γF` (any `γF ≤ 1/2`,
independent of `P`, as L5c's bounds are); L3's ladder theorem supplies L5c's layervine instances. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount (decodeSizeLeg unitBlockLists_numerics)

variable {γF : ℝ} [Fact (γF ≤ 1 / 2)]

/-- **Leg 2 at a marking over `𝒱_γ`** (main `LayeringLegMk`, truncation-free carrier), for the family `𝒱_γF` (CONVENTIONS:
section family `γF`, as L8's `ClassCountStmtMkLow`; the parameters `P` are arbitrary, as in main). -/
def LayeringLegMkLow : Prop :=
  ∃ C₀ K : ℕ, 1 ≤ C₀ ∧ ∀ P : WTParams, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ (S : Garden (2 * R)) (D : ReconstructionData S),
    ∀ A' : Finset (LayeredGarden (2 * R)), S.IsPlain → S.order ≤ N →
    (∀ LG ∈ A', Stage1Mk.Stage1CarriesW P p N LG ∧
      ∃ (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (σ : Prescription S) (Mk : Set (Fama.CLVineG γF S)),
        rbarOfMkG γF S σ Mk = r ∧ (Fama.stage1PieceOf γF P.d hS LG hd σ Mk).gbar = g) →
    (A'.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)

open Classical in
/-- **Leg 2 at a marking over `𝒱_γ`** (main `layeringLegMk`). -/
theorem layeringLegMkLow : LayeringLegMkLow (γF := γF) := by
  have : Fact Famc.ClassCount.TVineStructInputs := ⟨Famc.tvineStructInputs_holds⟩
  have : Fact Famc.LayervineTVineImproved := ⟨Famc.layervineTVineImproved_holds⟩
  have : Fact Famc.LayervineTVineFirst := ⟨Famc.layervineTVineFirst_holds⟩
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
  have hex : ∀ LG ∈ A', ∃ σ : Prescription S, ∃ Mk : Set (Fama.CLVineG γF S), ∃ hd : D.Decodes hSpl LG.garden,
      rbarOfMkG γF S σ Mk = r ∧ (Fama.stage1PieceOf γF P.d hSpl LG hd σ Mk).gbar = g := by
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
  set U : LayeredGarden (2 * R) → List (CLBlock S) := fun LG => Fama.unitBlocks γF S (σf LG) (Mkf LG) with hU
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
        gbarRHS γF D hSpl LG (Fama.stSt γF S (σf LGs) (Mkf LGs))
          (Set.toFinite (Fama.unitIngredients γF S (σf LGs) (Mkf LGs))).toFinset = g := by
      intro LG hLG
      obtain ⟨hLA, hc⟩ := Finset.mem_filter.1 hLG
      have heq : Fama.unitBlocks γF S (σf LG) (Mkf LG) = Fama.unitBlocks γF S (σf LGs) (Mkf LGs) := hc.trans hLGsc.symm
      refine ⟨hcan LG hLA, hdf LG hLA, ?_⟩
      rw [← gbar_eq_gbarRHSMk (γ := γF) P.d hSpl LG (hdf LG hLA) (σf LGs) (Mkf LGs)]
      exact (gbar_rbar_eq_of_unitBlocks_eqMk (γ := γF) P.d hSpl LG (hdf LG hLA) (σf LG) (σf LGs) (Mkf LG) (Mkf LGs)
        heq).1.symm.trans (hgf LG hLA)
    have hr' : (Fama.stSt γF S (σf LGs) (Mkf LGs)).G.molecule.rho + (Fama.unitBlocks γF S (σf LGs) (Mkf LGs)).length ≤ r :=
      (rho_add_length_le_rbarOfMk (γ := γF) S (σf LGs) (Mkf LGs)).trans (hrf LGs hLGsA).le
    exact hKB γF S hSpl D (σf LGs) (Mkf LGs) p g r N Ac hAcl hr' hsize hn
  -- the number of unit lists
  have hnum : (A'.image U).card ≤ (3 ^ 12) ^ N * (5 * r).factorial := by
    refine (card_unitBlockLists_le (γ := γF) S r (A'.image U) ?_).trans ?_
    · intro U0 hU0
      obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hU0
      refine ⟨⟨σf LG, Mkf LG, rfl⟩, ?_⟩
      have := rho_add_length_le_rbarOfMk (γ := γF) S (σf LG) (Mkf LG)
      have := hrf LG hLG
      show (Fama.unitBlocks γF S (σf LG) (Mkf LG)).length ≤ r
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


end WaveTurbulence.GammaLow.Flower
