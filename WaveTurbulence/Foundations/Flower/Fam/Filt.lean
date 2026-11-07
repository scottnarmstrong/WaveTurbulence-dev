/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Numeric
public import WaveTurbulence.Foundations.Flower.Cases.Shell
public import WaveTurbulence.Foundations.Flower.Fam.Graded3
public import WaveTurbulence.Foundations.Flower.Typed.Weighted
/-! # FL-FAM: the filtered family at a fixed parameter set, from the core. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set WaveTurbulence.Flower.Typed WaveTurbulence.Flower.Cases WaveTurbulence.Flower.FamilyW

/-- The `L`-slack left by a strict `hBc`. -/
def epsBc (Bc : ℕ → ℝ) (d : ℕ) : ℝ := (100 * (d : ℝ)) ^ 3 - Bc d - 80 * d - 3

/-- The `N`-independent constant of the graded external decay. -/
def Kconst (P : WTParams) (Pm p : ℕ) : ℝ :=
  (hiB P p / loB P) ^ (2 * (P.Lambda (p + 1) * (2 * Pm))) *
    Polar.rootPolarE P.d (P.Lambda (p + 1)) Pm

theorem Kconst_nonneg (P : WTParams) (hd : 1 ≤ P.d) (Pm p : ℕ) : 0 ≤ Kconst P Pm p := by
  unfold Kconst Polar.rootPolarE
  have h1 := one_le_loB P hd
  have h2 := loB_le_hiB P p
  have h3 : 0 ≤ hiB P p / loB P := div_nonneg (by linarith) (by linarith)
  exact mul_nonneg (pow_nonneg h3 _) (by positivity)

/-- The final exponent bookkeeping: the budget exponent dominates `Bc * Pm + eps * Pm`. -/
theorem exponent_le (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) (pat : Fin (2 * Pm) → FixPat) :
    Bc P.d * Pm + epsBc Bc P.d * Pm ≤
      FC23.flowerLExponent Pm P pat - ((40 * P.d) * (2 * Pm) : ℕ) - ((2 * Pm : ℕ) : ℝ) - (Pm : ℝ) := by
  unfold FC23.flowerLExponent epsBc
  have h0 : 0 ≤ (100 * (P.d : ℝ)) ^ 3 * Pm := by positivity
  have h1 : (100 * (P.d : ℝ)) ^ 3 * Pm ≤
      (if ∀ j, pat j = .plain then (1 : ℝ) else 2) * (100 * (P.d : ℝ)) ^ 3 * Pm := by
    split_ifs
    · linarith
    · nlinarith
  push_cast
  nlinarith

/-- **The filtered family at a fixed parameter set.** -/
theorem filt_fixed (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) (hd : 3 ≤ P.d)
    (hsol : ContinuousOn P.φ (Icc 0 P.τstar)) (htime : P.τstar = (P.D : ℝ) * P.δ)
    (hδ : 0 < P.δ) (hL4 : 4 ≤ P.L)
    (hsmall : 6 * loB P * P.δ ^ (2 * P.ν) ≤ 1)
    (hNL : ∀ p < P.D, ∀ N ≤ P.N (p + 1) ^ 4, 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L)
    (hMg : ∀ p < P.D, Mgen P.d (40 * P.d) ≤ P.L ∧ Mgen P.d (Wt P p) ≤ P.L)
    (hconst : ∀ p < P.D, Kconst P Pm p ≤ P.L ^ (epsBc Bc P.d * Pm))
    (H : FlowerCoreFiltAt Bc Pm P) : FlowerFiltFamilyAt Cfam Ufam Pm P := by
  intro hγ p hpd R hR t ht s hs n n' ζ N hN kind pat dagger j σ hσ tail small z hz
  have hd1 : 1 ≤ P.d := by omega
  have hL1 : 1 ≤ P.L := by linarith
  have hδ0 : 0 ≤ P.δ := hδ.le
  set M : ℝ := 2 ^ j * P.L with hMdef
  set A : ℝ := M / (4 * ((2 * N + 1 : ℕ) : ℝ)) with hAdef
  have hLM : P.L ≤ M := by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hM0 : 0 < M := by linarith
  have hNL' := hNL p hpd N hN
  have hN1 : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hA1 : 1 ≤ A := by
    rw [hAdef, one_le_div (by positivity)]
    linarith
  obtain ⟨hMg1, hMg2⟩ := hMg p hpd
  have hz' : ∀ i, z i ∈ Set.Icc (0 : ℝ)
      (FC23.extractionRadius (40 * P.d) N (Cfam P.d) (Ufam P p) M) := hz
  have hlo := one_le_loB P hd1
  have hlh := loB_le_hiB P p
  set lo := loB P with hlodef
  set hi := hiB P p with hhidef
  set m := P.Lambda (p + 1) with hmdef
  -- the typed form of the family weight
  have e1 := flowerWeighted_typed P (inputsF P R) p N kind pat dagger
    (fun LG k => stemFilter LG P.L σ k) M A tail small z ζ t s n n'
  rw [e1]
  set Rfam : Fin (2 * Pm) → Option ℝ := fun j => some (rad tail small M j) with hRfam
  have eW : (fun LG k => stemFilter LG P.L σ k *
        frontierW LG p (fun j => some (if tail j && small j then M / 2 else M)) k *
        leafProd LG (familyProfile (inputsF P R) p M A tail z) k) =
      fun LG k => (frontierW LG p Rfam k * stemFilter LG P.L σ k) *
        leafProd LG (familyProfile (inputsF P R) p M A tail z) k := by
    funext LG k
    simp only [hRfam, rad]
    ring
  rw [eW]
  set h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ := familyProfile (inputsF P R) p M A tail z
    with hh
  have hlow : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal lo :=
    profile_low P hd hL1 hδ0 htime hsol hpd R hR N M A tail z (hMg1.trans hLM) hAdef hA1 hz'
  have hhigh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d + 4 * m) (h q j j') ≤ ENNReal.ofReal hi :=
    profile_high P hd hL1 hδ0 htime hsol hpd R hR N M A tail z (hMg2.trans hLM) hAdef hA1 hz'
  have hW : ∀ (LG : LayeredGarden (2 * Pm)) (k : GNode LG.garden.tree → Mom P.d), |frontierW LG p Rfam k * stemFilter LG P.L σ k| ≤ 1 := by
    intro LG k
    rw [abs_mul]
    exact mul_le_one₀ (abs_frontierW_le LG p Rfam k) (abs_nonneg _) (stemFilter_abs_le_one LG P.L σ k)
  have hsupp : SuppAt p (rad tail small M) h := fun j j' x hx =>
    profile_support_rad (inputsF P R) p M A tail small z hM0 j j' x hx
  have hrad : ∀ j, rad tail small M j ≤ M := by
    intro j; unfold rad; split_ifs <;> linarith
  have hrad0 : ∀ j, M / 2 ≤ rad tail small M j := by
    intro j; unfold rad; split_ifs <;> linarith
  have key := root_decay_graded (P := P) (p := p) (N := N) (Pm := Pm) hd1 hL1 kind pat dagger ζ t s n n' m
    (fun LG (k : GNode LG.garden.tree → Mom P.d) => frontierW LG p Rfam k * stemFilter LG P.L σ k) hW h lo hi
    (X := P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N) (by linarith) hlh
    (SuppAt p (rad tail small M)) hsupp
    (fun g hg j i μ => hg.perturb _ j i μ) hlow hhigh (by
      intro h' hg hb
      refine H hγ p hpd t ht s hs n n' ζ N hN kind pat dagger h' (2 * lo) (by linarith) hb Rfam σ ?_ ?_
      · intro j r hr
        have hr' : rad tail small M j = r := Option.some.inj hr
        rw [← hr']
        have := hrad0 j
        linarith
      · intro hex j
        refine ⟨rad tail small M j, rfl, fun j' x hx => hg j j' x hx, ?_⟩
        have h10 := hσ hex
        have h0 : 0 ≤ rad tail small M j := by have := hrad0 j; linarith
        exact (pow_le_pow_left₀ h0 (hrad j) 10).trans h10)
  -- assemble
  have hJ0 : 0 < jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') := Polar.jbr_pos_p _
  set J := jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') with hJ
  have hcost : Polar.rootPolarCost P.d m Pm N ≤ Polar.rootPolarE P.d m Pm * 3 ^ N := by
    have := Polar.rootPolarCost_le P.d m Pm N
    simpa [Polar.rootPolarK] using this
  have hκ0 : 0 ≤ (hi / lo) ^ (2 * (m * (2 * Pm))) := pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hX0 : 0 ≤ P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N := by positivity
  have hq : (hi / lo) ^ (2 * (m * (2 * Pm))) *
      (Polar.rootPolarCost P.d m Pm N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N)) ≤
      Kconst P Pm p * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * 3 ^ N) := by
    have h1 : Polar.rootPolarCost P.d m Pm N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N) ≤
        Polar.rootPolarE P.d m Pm * 3 ^ N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N) :=
      mul_le_mul_of_nonneg_right hcost hX0
    calc _ ≤ (hi / lo) ^ (2 * (m * (2 * Pm))) *
          (Polar.rootPolarE P.d m Pm * 3 ^ N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N)) :=
          mul_le_mul_of_nonneg_left h1 hκ0
      _ = _ := by unfold Kconst; ring
  have hab := numeric_absorb (N := N) (Bexp := Bc P.d * Pm) (e := epsBc Bc P.d * Pm) hL1 hδ (by linarith)
    (Kconst_nonneg P hd1 Pm p) hsmall (hconst p hpd)
  have hexp := Real.rpow_le_rpow_of_exponent_le hL1 (exponent_le Bc Pm P pat)
  have hY : (hi / lo) ^ (2 * (m * (2 * Pm))) *
      (Polar.rootPolarCost P.d m Pm N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N)) ≤
      P.L ^ (FC23.flowerLExponent Pm P pat - ((40 * P.d) * (2 * Pm) : ℕ) - ((2 * Pm : ℕ) : ℝ) - (Pm : ℝ)) *
        P.δ ^ (4 * P.ν * N) :=
    hq.trans (hab.trans (mul_le_mul_of_nonneg_right hexp (by positivity)))
  have hn : (((2 * m * (2 * Pm) : ℕ)) : ℝ) = 4 * (m : ℝ) * Pm := by push_cast; ring
  have hrb : FC23.flowerRootBudget Pm P p ζ n n' = (J ^ (2 * m * (2 * Pm)))⁻¹ := by
    unfold FC23.flowerRootBudget
    rw [← hJ, show (-(4 * (P.Lambda (p + 1) : ℝ) * Pm)) = -(((2 * m * (2 * Pm) : ℕ)) : ℝ) by rw [hn],
      Real.rpow_neg hJ0.le, Real.rpow_natCast]
  have hJn : 0 < J ^ (2 * m * (2 * Pm)) := pow_pos hJ0 _
  unfold familyBudget
  rw [hrb]
  have key' := key.trans hY
  set Φ := ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
    (fun LG k => (frontierW LG p Rfam k * stemFilter LG P.L σ k) *
      leafProd LG h k) ζ t s n n'‖ with hΦ
  have key'' : J ^ (2 * m * (2 * Pm)) * Φ ≤ _ := key'
  rw [mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hJn, mul_comm]
  exact key''
