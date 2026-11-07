/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Filt
/-! # FL-FAM: the gain family at a fixed parameter set, from the core. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set WaveTurbulence.Flower.Typed WaveTurbulence.Flower.Cases WaveTurbulence.Flower.FamilyW

/-- **The gain family at a fixed parameter set.** -/
theorem gain_fixed (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) (hd : 3 ≤ P.d)
    (hsol : ContinuousOn P.φ (Icc 0 P.τstar)) (htime : P.τstar = (P.D : ℝ) * P.δ)
    (hδ : 0 < P.δ) (hL4 : 4 ≤ P.L)
    (hsmall : 6 * loB P * P.δ ^ (2 * P.ν) ≤ 1)
    (hNL : ∀ p < P.D, ∀ N ≤ P.N (p + 1) ^ 4, 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L)
    (hMg : ∀ p < P.D, Mgen P.d (40 * P.d) ≤ P.L ∧ Mgen P.d (Wt P p) ≤ P.L)
    (hconst : ∀ p < P.D, Kconst P Pm p ≤ P.L ^ (epsBc Bc P.d * Pm))
    (H : FlowerCoreGainAt Bc Pm P) : FlowerGainFamilyAt Cfam Ufam Pm P := by
  intro hγ p hpd R hR t ht s hs n n' ζ N hN kind dagger j j₂ hj₂ hσ tail small z hz
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
  set G : ℝ := ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have e1 := flowerWeighted_typed P (inputsF P R) p N kind (fun _ => FixPat.plain) dagger
    (fun LG k => LG.cutWeight2P P.L j₂ k) M A tail small z ζ t s n n'
  rw [e1]
  set Rfam : Fin (2 * Pm) → ℝ := fun j => rad tail small M j with hRfam
  have eW : (fun LG k => LG.cutWeight2P P.L j₂ k *
        frontierW LG p (fun j => some (if tail j && small j then M / 2 else M)) k *
        leafProd LG (familyProfile (inputsF P R) p M A tail z) k) =
      fun LG k => (frontierW LG p (fun j => some (Rfam j)) k * LG.cutWeight2P P.L j₂ k) *
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
  have hW : ∀ (LG : LayeredGarden (2 * Pm)) (k : GNode LG.garden.tree → Mom P.d),
      |frontierW LG p (fun j => some (Rfam j)) k * LG.cutWeight2P P.L j₂ k| ≤ 1 := by
    intro LG k
    rw [abs_mul]
    exact mul_le_one₀ (abs_frontierW_le LG p _ k) (abs_nonneg _) (cutWeight2P_abs_le_one LG P.L j₂ k)
  have hsupp : SuppAt p (rad tail small M) h := fun j j' x hx =>
    profile_support_rad (inputsF P R) p M A tail small z hM0 j j' x hx
  have hrad : ∀ j, rad tail small M j ≤ M := by
    intro j; unfold rad; split_ifs <;> linarith
  have hrad0 : ∀ j, M / 2 ≤ rad tail small M j := by
    intro j; unfold rad; split_ifs <;> linarith
  have key := root_decay_graded (P := P) (p := p) (N := N) (Pm := Pm) hd1 hL1 kind (fun _ => FixPat.plain)
    dagger ζ t s n n' m
    (fun LG (k : GNode LG.garden.tree → Mom P.d) =>
      frontierW LG p (fun j => some (Rfam j)) k * LG.cutWeight2P P.L j₂ k) hW h lo hi
    (X := P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G) (by linarith) hlh
    (SuppAt p (rad tail small M)) hsupp
    (fun g hg j i μ => hg.perturb _ j i μ) hlow hhigh (by
      intro h' hg hb
      refine H hγ p hpd t ht s hs n n' ζ N hN kind dagger h' (2 * lo) (by linarith) hb Rfam j₂ hj₂ ?_ ?_
      · intro j
        have := hrad0 j
        simp only [hRfam]
        linarith
      · intro j
        refine ⟨fun j' x hx => hg j j' x hx, ?_⟩
        have h0 : 0 ≤ rad tail small M j := by have := hrad0 j; linarith
        exact (pow_le_pow_left₀ h0 (hrad j) 10).trans hσ)
  have hJ0 : 0 < jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') := Polar.jbr_pos_p _
  set J := jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') with hJ
  have hcost : Polar.rootPolarCost P.d m Pm N ≤ Polar.rootPolarE P.d m Pm * 3 ^ N := by
    have := Polar.rootPolarCost_le P.d m Pm N
    simpa [Polar.rootPolarK] using this
  have hκ0 : 0 ≤ (hi / lo) ^ (2 * (m * (2 * Pm))) := pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hX0 : 0 ≤ P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G := by positivity
  have hq : (hi / lo) ^ (2 * (m * (2 * Pm))) *
      (Polar.rootPolarCost P.d m Pm N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G)) ≤
      (Kconst P Pm p * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * 3 ^ N)) * G := by
    have h1 : Polar.rootPolarCost P.d m Pm N *
        (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G) ≤
        Polar.rootPolarE P.d m Pm * 3 ^ N *
          (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G) :=
      mul_le_mul_of_nonneg_right hcost hX0
    calc _ ≤ (hi / lo) ^ (2 * (m * (2 * Pm))) *
          (Polar.rootPolarE P.d m Pm * 3 ^ N *
            (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G)) :=
          mul_le_mul_of_nonneg_left h1 hκ0
      _ = _ := by unfold Kconst; ring
  have hab := numeric_absorb (N := N) (Bexp := Bc P.d * Pm) (e := epsBc Bc P.d * Pm) hL1 hδ (by linarith)
    (Kconst_nonneg P hd1 Pm p) hsmall (hconst p hpd)
  have hexp0 := Real.rpow_le_rpow_of_exponent_le hL1 (exponent_le Bc Pm P (fun _ => FixPat.plain))
  have hexp := Real.rpow_le_rpow_of_exponent_le hL1
    (show Bc P.d * Pm + epsBc Bc P.d * Pm ≤
      FC23.flowerLExponent Pm P (fun _ => FixPat.plain) - ((40 * P.d) * (2 * Pm) : ℕ) -
        ((2 * Pm : ℕ) : ℝ) - (0 : ℝ) by
      have := exponent_le Bc Pm P (fun _ => FixPat.plain)
      linarith [(Nat.cast_nonneg Pm : (0 : ℝ) ≤ Pm)])
  have hY : (hi / lo) ^ (2 * (m * (2 * Pm))) *
      (Polar.rootPolarCost P.d m Pm N * (P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * (2 * lo) ^ N * G)) ≤
      (P.L ^ (FC23.flowerLExponent Pm P (fun _ => FixPat.plain) - ((40 * P.d) * (2 * Pm) : ℕ) -
        ((2 * Pm : ℕ) : ℝ) - (0 : ℝ)) * P.δ ^ (4 * P.ν * N)) * G :=
    hq.trans (mul_le_mul_of_nonneg_right (hab.trans (mul_le_mul_of_nonneg_right hexp (by positivity))) hG0)
  have hn : (((2 * m * (2 * Pm) : ℕ)) : ℝ) = 4 * (m : ℝ) * Pm := by push_cast; ring
  have hrb : FC23.flowerRootBudget Pm P p ζ n n' = (J ^ (2 * m * (2 * Pm)))⁻¹ := by
    unfold FC23.flowerRootBudget
    rw [← hJ, show (-(4 * (P.Lambda (p + 1) : ℝ) * Pm)) = -(((2 * m * (2 * Pm) : ℕ)) : ℝ) by rw [hn],
      Real.rpow_neg hJ0.le, Real.rpow_natCast]
  have hJn : 0 < J ^ (2 * m * (2 * Pm)) := pow_pos hJ0 _
  unfold familyBudget
  rw [hrb]
  have key' := key.trans hY
  set Φ := ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => FixPat.plain) dagger
    (fun LG k => (frontierW LG p (fun j => some (Rfam j)) k * LG.cutWeight2P P.L j₂ k) *
      leafProd LG h k) ζ t s n n'‖ with hΦ
  have key'' : J ^ (2 * m * (2 * Pm)) * Φ ≤ _ := key'
  have hfin : Φ ≤ (J ^ (2 * m * (2 * Pm)))⁻¹ *
      ((P.L ^ (FC23.flowerLExponent Pm P (fun _ => FixPat.plain) - ((40 * P.d) * (2 * Pm) : ℕ) -
        ((2 * Pm : ℕ) : ℝ) - (0 : ℝ)) * P.δ ^ (4 * P.ν * N)) * G) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hJn, mul_comm]
    exact key''
  refine hfin.trans (le_of_eq ?_)
  push_cast
  ring_nf

end WaveTurbulence.Flower.Fam
