/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Clauses2
/-! # The positive cut2 clauses at a fixed parameter set: plain patterns (gain family) and
non-plain patterns (shell expansion over the filtered family). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem cut2pos_plain_of_gain (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hG : FlowerGainFamilyAt C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCasePatAt CaseCut2Pos PatPlain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  obtain ⟨j₂, rfl, hj₂⟩ := hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut j₂ rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hpat' : pat = fun _ => FixPat.plain := funext hpat
  subst hpat'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := gain_cut1 C U hC hU hG hn hγ hp R hR t ht s hs n n' ζ hN kind dagger j₁ j₂ hj₂ hj₁
  have key : flowerSumP P (inputsF P R) p N kind (fun _ => .plain) dagger (some j₁) (some j₂) ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind (fun _ => .plain) dagger
        (fun LG k => LG.cutWeight2P P.L j₂ k * LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind _ dagger ζ t s n n' fun LG k => by
      simp only [Option.elim]
      ring
  unfold FlowerBoundAt
  rw [key]
  have hpl : ∀ j : Fin (2 * Pm), ((fun _ => FixPat.plain : Fin (2 * Pm) → FixPat) j = .plain) :=
    fun _ => rfl
  simp only [Option.elim, hpl, implies_true, ite_true]
  rw [Sw_eq] at hb
  unfold flowerRootBudget flowerLExponent at hb
  simp only [hpl, implies_true, ite_true] at hb
  refine hb.trans (le_of_eq ?_)
  ring

theorem two_pow_mul_rpow_le (L : ℝ) (hL : 4 ≤ L) (a : ℝ) (Pm : ℕ) :
    (2 : ℝ) ^ (2 * Pm) * L ^ (a - (Pm : ℝ)) ≤ L ^ a := by
  have hL0 : 0 < L := by linarith
  rw [Real.rpow_sub hL0, Real.rpow_natCast]
  have h4 : (2 : ℝ) ^ (2 * Pm) ≤ L ^ Pm := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) Pm
  have hpos : 0 < L ^ Pm := by positivity
  have h1 : (2 : ℝ) ^ (2 * Pm) / L ^ Pm ≤ 1 := (div_le_one hpos).mpr h4
  calc (2 : ℝ) ^ (2 * Pm) * (L ^ a / L ^ Pm) = L ^ a * ((2 : ℝ) ^ (2 * Pm) / L ^ Pm) := by ring
    _ ≤ L ^ a * 1 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hL0.le _)
    _ = L ^ a := mul_one _

theorem sum_norm_bound {ι : Type*} [Fintype ι] (c f : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) (B : ℝ)
    (h : ∀ i, ‖f i‖ ≤ B) : ‖∑ i, c i * f i‖ ≤ (Fintype.card ι : ℝ) * B := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖c i * f i‖ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, hc i, one_mul]
        exact h i
    _ = (Fintype.card ι : ℝ) * B := by simp [Finset.sum_const, Finset.card_univ]

theorem cut2pos_nonplain_of_filt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAt C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCasePatAt CaseCut2Pos PatNonplain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  obtain ⟨j₂, rfl, hj₂⟩ := hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut j₂ rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL4 : 4 ≤ P.L := hn.2.2.2.2.1
  have hL1 : 1 ≤ P.L := by linarith
  have hd : 1 ≤ P.d := hn.1
  have hsum := summable_clipped_inputs P R p hp.le hd hL1 hR
  have hterm : ∀ ε : Fin (2 * Pm) → Bool,
      ‖flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k *
          LG.cutWeight1P p P.L j₁ k) ζ t s n n'‖ ≤
      flowerRootBudget Pm P p ζ n n' * P.L ^ (flowerLExponent Pm P pat - (Pm : ℝ)) *
        P.δ ^ (2 * P.ν * N) * (2 ^ j₁ * P.L) ^ (-((((40 * P.d) * (2 * Pm) : ℕ) : ℝ))) := fun ε => by
    rw [flowerWeighted_clip]
    exact filt_cut1 C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j₁
      (fun i => some (if ε i then j₂ - 1 else j₂)) (fun _ => hj₁)
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j₁) (some j₂) ζ t s n n' =
      ∑ ε : Fin (2 * Pm) → Bool, ((∏ i, if ε i then (-1 : ℝ) else 1 : ℝ) : ℂ) *
        flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
          (fun LG k => stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k *
            LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    have hlin := flowerWeighted_finset_sum P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n'
      (Finset.univ : Finset (Fin (2 * Pm) → Bool))
      (fun ε : Fin (2 * Pm) → Bool => ∏ i, if ε i then (-1 : ℝ) else 1)
      (fun (ε : Fin (2 * Pm) → Bool) LG k =>
        stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k * LG.cutWeight1P p P.L j₁ k)
      (fun ε LG k => by
        rw [abs_mul]
        exact mul_le_one₀ (stemFilter_abs_le_one _ _ _ _) (abs_nonneg _) (cutWeight1P_abs_le_one _ _ _ _ _))
      hsum
    rw [← hlin, flowerWeighted_clip, flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp only [Option.elim]
      rw [cutWeight2P_expand LG P.L j₂ k hj₂, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ε _ => by ring
  have hc1 : ∀ ε : Fin (2 * Pm) → Bool, ‖((∏ i, if ε i then (-1 : ℝ) else 1 : ℝ) : ℂ)‖ = 1 := by
    intro ε
    rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp
  unfold FlowerBoundAt
  rw [key]
  have hpl : ¬ ∀ j, pat j = .plain := hpat
  simp only [Option.elim, if_neg hpl, mul_one]
  rw [Sw_eq] at hterm
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hterm
  unfold flowerRootBudget at hroot
  simp only [if_neg hpl] at hterm
  have hD : 0 ≤ P.δ ^ (2 * P.ν * N) := Real.rpow_nonneg hδ.le _
  have hM : 0 ≤ ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) := Real.rpow_nonneg (by positivity) _
  refine (sum_norm_bound _ _ hc1 _ hterm).trans ?_
  have hcard : ((Fintype.card (Fin (2 * Pm) → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * Pm) := by simp
  rw [hcard]
  rw [show ∀ r B D M : ℝ, (2 : ℝ) ^ (2 * Pm) * (r * B * D * M) = r * ((2 : ℝ) ^ (2 * Pm) * B) * D * M from
    fun _ _ _ _ => by ring]
  exact mul4_le hroot (two_pow_mul_rpow_le P.L hL4 _ Pm) hD hM

end WaveTurbulence.Flower.Cases
