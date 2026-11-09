/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BadCount
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Prefix
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.WPF
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.BadCount
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.WPF` (sha256 0047375a4cd20641…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W3 (WP-F): the number of unrolled terms and the final constants

**The count** (`count_le`, `card_le_count`).  `P4.card_terms_le_wt` bounds the number of unrolled terms by `∏_{members} wtOf`,
`wtOf p i = 192 (N_i+1) (16·12⁹)^{N_i} 4^p` (`N_i = zpN` of the exceptional pair of the core vine `i`).  With `N + 1 ≤ 2^N`,
`#core vines ≤ b` (every core vine is bad: `card_core_le_bad`, R54) and `∑ N_i ≤ n₍₂₎` (`sum_zpN_le`):

  `∏ wtOf ≤ (192·4^𝔇)^b · (32·12⁹)^{n₍₂₎}`.

The factor `(192·4^𝔇)^b` is the `C₂^b` of R54 (`C₂` is chosen after `δ, 𝔇`), the factor `(32·12⁹)^{n₍₂₎}` is absorbed by `C₁`
through the exceptional rows' `(C₁√δ)` factors (they are part of `n₍₂₎`, TARGET L1919-L1922 `C₀^{n(𝒬)+n(𝒯)}`).

**The constants** (`wpF_absorb`, `wpF_top`): from the finite-Minkowski bound of the unrolled class sum
`‖·‖ ≤ (cc + 1) (#terms · β)` (`P4.top_boundR`) and a uniform term bound in the RHS form at an engine-level constant `Nₛ`,
`β ≤ Λ (Nₛ√δ)^{n₍₂₎} L^{…} leaf` (`Λ ≥ 0` arbitrary: R58's `⟨λ⟩^{cη⁶}` loss, `1` for `λ = 0`), the final bound
`Λ (C₁√δ)^{n₍₂₎} L^{…} leaf C₂^b` follows as soon as `C₁ ≥ (ccη+1) · 32·12⁹ · Nₛ` and `C₂ ≥ 192·4^𝔇`.  The cutoff constant of the
cube `q` of the box is the `q`-independent `ccη η` (`Eng.cc_translate`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 VineParamContract WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

theorem wtOf_leΓ (p : ℕ) (i : (assemblySourceFamilyΓ B).CoreIndex) :
    wtOfΓ B RD hG layer hLayer p i ≤ (192 * 4 ^ p) * countKc ^ zpN (startStateΓ B RD hG layer hLayer) i := by
  unfold wtOfΓ countKc
  set N := zpN (startStateΓ B RD hG layer hLayer) i
  have h1 := succ_le_two_pow N
  calc 192 * (N + 1) * ((16 * 12 ^ 9) ^ N * 4 ^ p) ≤ 192 * 2 ^ N * ((16 * 12 ^ 9) ^ N * 4 ^ p) := by gcongr
    _ = 192 * 4 ^ p * (32 * 12 ^ 9) ^ N := by
        rw [show (32 : ℕ) * 12 ^ 9 = 2 * (16 * 12 ^ 9) by norm_num, mul_pow 2 (16 * 12 ^ 9) N]
        generalize (16 : ℕ) * 12 ^ 9 = K
        ring

/-- The product over the members of a level is at most the product over all core vines. -/
theorem prod_lvl_leΓ (lv : LvlΓ B) (f : (assemblySourceFamilyΓ B).CoreIndex → ℕ) (hf : ∀ i, 1 ≤ f i) :
    ∏ j : lv.ι, f (lv.e j) ≤ ∏ i, f i := by
  classical
  rw [← Finset.prod_image (f := f) (s := Finset.univ) (g := lv.e) (fun x _ y _ h => lv.he h)]
  exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _) fun i _ _ => hf i

theorem prod_wtOf_leΓ (p : ℕ) :
    ∏ i, wtOfΓ B RD hG layer hLayer p i ≤
      (192 * 4 ^ p) ^ Fintype.card (assemblySourceFamilyΓ B).CoreIndex *
        countKc ^ (∑ i, zpN (startStateΓ B RD hG layer hLayer) i) := by
  calc ∏ i, wtOfΓ B RD hG layer hLayer p i ≤ ∏ i, ((192 * 4 ^ p) * countKc ^ zpN (startStateΓ B RD hG layer hLayer) i) :=
        Finset.prod_le_prod' fun i _ => wtOf_leΓ B RD hG layer hLayer p i
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum]

/-- **The count**: `∏_{core} wtOf ≤ (192·4^𝔇)^b · (32·12⁹)^{n₍₂₎}` for `p ≤ 𝔇`. -/
theorem count_leΓ (hM9 : NormalChartSupply γF) {p D : ℕ} (hpD : p ≤ D) :
    ∏ i, wtOfΓ B RD hG layer hLayer p i ≤
      countKp D ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card *
        countKc ^ clLocalOrder2 RD hG R := by
  refine (prod_wtOf_leΓ B RD hG layer hLayer p).trans (Nat.mul_le_mul ?_ ?_)
  · calc (192 * 4 ^ p) ^ Fintype.card (assemblySourceFamilyΓ B).CoreIndex
        ≤ countKp D ^ Fintype.card (assemblySourceFamilyΓ B).CoreIndex := by
          unfold countKp; gcongr
      _ ≤ _ := Nat.pow_le_pow_right (one_le_countKp D) (card_core_le_badΓ B hM9)
  · refine Nat.pow_le_pow_right one_le_countKc ?_
    have h := sum_zpN_leΓ B RD hG layer hLayer hM9
    have h2 : ∑ i, zpN (startStateΓ B RD hG layer hLayer) i ≤ ∑ i, 2 * zpN (startStateΓ B RD hG layer hLayer) i :=
      Finset.sum_le_sum fun i _ => by omega
    omega

/-- **The number of unrolled terms** at any level (P4 `card_terms_le_wt` form) is at most `(192·4^𝔇)^b (32·12⁹)^{n₍₂₎}`. -/
theorem card_le_countΓ (hM9 : NormalChartSupply γF) {p D : ℕ} (hpD : p ≤ D) (lv : LvlΓ B) {Nt : ℕ}
    (hNt : Nt ≤ ∏ j : lv.ι, wtOfΓ B RD hG layer hLayer p (lv.e j)) :
    Nt ≤ countKp D ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card *
        countKc ^ clLocalOrder2 RD hG R :=
  hNt.trans ((prod_lvl_leΓ B lv _ (one_le_wtOfΓ B RD hG layer hLayer p)).trans (count_leΓ B RD hG layer hLayer hM9 hpD))

include B in
/-- `1 ≤ n₍₂₎`. -/
theorem one_le_order2Γ (hM9 : NormalChartSupply γF) : 1 ≤ clLocalOrder2 RD hG R := by
  rw [order2_eqΓ hM9 B RD hG]
  exact (M_posΓ hM9 B).trans (Nat.le_add_right _ _)

/-- **WP-F at the top level** (the W3 export).  From P4's `top_boundR` (finite Minkowski over the unrolled terms, cube `q`,
`θ = 2η⁸`), the term count `#terms ≤ ∏_{members} wtOf` (P4 `card_terms_le_wt`, or the expanded multiset of BOT-DECOMP in the
same form, R60) and a uniform term bound `β ≤ Λ (Nₛ √δ)^{n₍₂₎} Lp lf` (W2), the class sum obeys
`Λ (C₁√δ)^{n₍₂₎} Lp lf C₂^b` for `C₁ ≥ (ccη+1)·32·12⁹·Nₛ`, `C₂ ≥ 192·4^𝔇`, `p ≤ 𝔇`. -/
theorem wpF_topΓ (hM9 : NormalChartSupply γF) {η : ℝ} (q : Fin 3 → ℝ) {p D : ℕ} (hpD : p ≤ D) (lv : LvlΓ B) {Nt : ℕ}
    (hNt : Nt ≤ ∏ j : lv.ι, wtOfΓ B RD hG layer hLayer p (lv.e j)) {β X : ℝ≥0∞} {Λ Ns δ Lp lf C₁ C₂ : ℝ}
    (hX : X ≤ (WaveTurbulence.Fourier.cutoffMultiplierConstant (2 * η ^ 8) (FS.cutQ q) + 1) * ((Nt : ℝ≥0∞) * β))
    (hβ : β ≤ ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    X ≤ ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
      C₂ ^ (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false).card)) := by
  rw [Eng.cc_translate] at hX
  exact wpF_absorb (ccη_lt_top η).ne hX (card_le_countΓ B RD hG layer hLayer hM9 hpD lv hNt) hβ hΛ hNs
    (Real.sqrt_nonneg _) hLp hlf (one_le_order2Γ B RD hG hM9) hC₁ hC₂

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
