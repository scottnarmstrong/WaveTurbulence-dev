/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppCell
public import WaveTurbulence.Foundations.ApproxNT.CellOps
public import WaveTurbulence.Foundations.ApproxNT.DeltaCell
public import WaveTurbulence.Foundations.ApproxNT.CoreBound

/-!
# The approximation `I_app` on one product of cells (packet NT6)

For one product of cells the decoupled integral with the truncated profile is
`multiInt = (∏_{j∈J} μ⁻¹ pvTrunc_μ(Pⱼ)) · B`, `B = ∫ Ψ̂₁(b) ∏_{i∉J} cellIntᵢ(μ bᵢ) db`
(`AppSplit`, `AppTools.jfactor_eq`), and the limiting value is
`μ^{-n} (∫Ψ₁) ∏_{j∈J} p.v.(Pⱼ) ∏_{i∉J} δ(Pᵢ)` (`cellOp`). Their difference is
`≤ (K_a/μ)^n (D₀ + 4πH) n (1 + Σ|ξⱼ|+|ζⱼ|) (μ⁻¹ + μ^{-θ})`
by DH21 Lemma 6.3 (`exists_pvCell`) for the `J`-factors and the Hölder bound
(`norm_B_sub_Delta_le`) for the `J^c`-factors: DH21 Prop 6.1, L1648–L1657.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- The limiting factor of one cell: `p.v. ∫∫ P/⟨x,y⟩` for `j ∈ J`, `∫∫ δ(⟨x,y⟩) P` otherwise. -/
@[expose] def cellOp {ι : Type*} [DecidableEq ι] (J : Finset ι) (j : ι) (p q ξ η : Mom d) : ℂ :=
  if j ∈ J then pvOp (cellFn p q ξ η) else NTSP.deltaInner (cellFn p q ξ η)

theorem norm_deltaInner_cellFn_le (hd : 3 ≤ d) (p q ξ η : Mom d) :
    ‖NTSP.deltaInner (cellFn p q ξ η)‖ ≤ cellCa d := by
  rw [deltaInner_cellFn hd]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h := lintegral_cellInt_le (by omega) p q ξ η
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_cellInt (by omega) p q ξ η)] at h
  have hK : 0 ≤ cellK0 d * NTSP.sInt d := by
    have := cellK0_nonneg d
    have : 0 ≤ NTSP.sInt d := by
      unfold NTSP.sInt; exact integral_nonneg fun _ => by positivity
    positivity
  exact ((ENNReal.ofReal_le_ofReal_iff hK).1 h).trans (le_max_left _ _)

theorem integral_cellInt_scale {μ : ℝ} (hμ : 0 < μ) (p q ξ η : Mom d) :
    ∫ t, cellInt p q ξ η (μ * t) = (μ⁻¹ : ℂ) * ∫ s, cellInt p q ξ η s := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.2 hμ), Complex.real_smul,
    Complex.ofReal_inv]

theorem fourier_zero_eq_integral {κ : Type} [Fintype κ] (f : EuclideanSpace ℝ κ → ℂ) :
    𝓕 f 0 = ∫ Ω, f Ω := by
  rw [Real.fourier_eq]
  simp

theorem norm_prod_sub_prod_le_of {ι : Type*} [DecidableEq ι] (s : Finset ι) {a b : ι → ℂ}
    {r : ℝ} {f : ι → ℝ} (hr : 0 ≤ r) (hf : ∀ i ∈ s, 0 ≤ f i) (ha : ∀ i ∈ s, ‖a i‖ ≤ r)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ r) (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ r * f i) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (2 * r) ^ s.card * ∑ i ∈ s, f i := by
  refine (norm_prod_sub_prod_le s a b).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun l hl => ?_
  have h1 : ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) ≤ (2 * r) ^ (s.card - 1) := by
    rw [← card_erase_of_mem hl]
    calc ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) ≤ ∏ _i ∈ s.erase l, (2 * r) :=
          prod_le_prod₀ (fun i _ => by positivity) (fun i hi => by
            have := ha i (mem_of_mem_erase hi); have := hb i (mem_of_mem_erase hi); linarith)
      _ = _ := prod_const _
  have hc : (2 * r) ^ s.card = 2 * r * (2 * r) ^ (s.card - 1) := by
    rw [← pow_succ']; congr 1; have := card_pos.2 ⟨l, hl⟩; omega
  have hp : 0 ≤ (2 * r) ^ (s.card - 1) := by positivity
  have hfl := hf l hl
  calc ‖a l - b l‖ * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) ≤ (r * f l) * (2 * r) ^ (s.card - 1) :=
        mul_le_mul (hab l hl) h1 (prod_nonneg fun _ _ => by positivity) (mul_nonneg hr hfl)
    _ ≤ (2 * r) ^ s.card * f l := by
        rw [hc]
        have : 0 ≤ r * f l * (2 * r) ^ (s.card - 1) := by positivity
        nlinarith

/-- **One product of cells**: the decoupled integral with the truncated profile against the
limiting value `μ^{-n} (∫Ψ₁) ∏ⱼ cellOpⱼ` (DH21 Prop 6.1, L1648–L1657). The constant `K_a` depends
only on `d`. -/
theorem exists_app_cell_bound (hd : 3 ≤ d) : ∃ Ka : ℝ, 1 ≤ Ka ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) (Kj : ι → ℕ)
      (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ D → (∀ k, 0 ≤ D k) → ∀ D0 : ℝ, ∫ Ω, ‖Ψ₁ Ω‖ ≤ D0 →
      ∀ θ H : ℝ, 0 < θ → θ ≤ 1 → 0 ≤ H →
      ∫⁻ Ω, ENNReal.ofReal (wmax θ (fun i => Ω i)) * ‖Ψ₁ Ω‖ₑ ≤ ENNReal.ofReal H →
      ∀ μ : ℝ, 1 < μ → ∀ c : CellData d ι,
      (∀ j, μ * ((‖c.p j‖ + Real.sqrt d) * (‖c.q j‖ + Real.sqrt d)) ≤ 2 ^ Kj j) →
      ‖multiInt μ (truncProfile J Kj Ψ₁) c.p c.q c.ξ c.ζ -
          (μ⁻¹ : ℂ) ^ Fintype.card ι * (∫ Ω, Ψ₁ Ω) *
            ∏ j, cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j)‖ ≤
        (Ka / μ) ^ Fintype.card ι * ((D0 + 4 * Real.pi * H) * Fintype.card ι *
          (1 + ∑ j, (‖c.ξ j‖ + ‖c.ζ j‖)) * (μ⁻¹ + μ ^ (-θ))) ∧
      ‖(μ⁻¹ : ℂ) ^ Fintype.card ι * (∫ Ω, Ψ₁ Ω) *
          ∏ j, cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j)‖ ≤ (Ka / μ) ^ Fintype.card ι * D0 := by
  obtain ⟨M, hM0, hM⟩ := exists_pvCell hd
  set Mx := max M (cellCa d) with hMx
  have hCa := one_le_cellCa d
  have hMxC : cellCa d ≤ Mx := le_max_right _ _
  have hMxM : M ≤ Mx := le_max_left _ _
  refine ⟨2 * Mx, by linarith, ?_⟩
  intro ι _ _ J Kj Ψ₁ D hΨ hD hD0 D0 hD0' θ H hθ0 hθ1 hH0 hH μ hμ c hK
  have hμ0 : 0 < μ := by linarith
  have hμi : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ0.le
  have hD00 : 0 ≤ D0 := le_trans (integral_nonneg fun _ => norm_nonneg _) hD0'
  set n := Fintype.card ι with hn
  set g : ι → ℝ → ℂ := fun i t => cellInt (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ * t) with hg_def
  set P : ι → ℂ := fun j => pvOp (cellFn (c.p j) (c.q j) (c.ξ j) (c.ζ j)) with hP_def
  set Pt : ι → ℂ := fun j => pvTrunc μ (cellFn (c.p j) (c.q j) (c.ξ j) (c.ζ j)) with hPt_def
  set Δ : ι → ℂ := fun j => NTSP.deltaInner (cellFn (c.p j) (c.q j) (c.ξ j) (c.ζ j)) with hΔ_def
  set B := ∫ b : {j // j ∉ J} → ℝ, 𝓕 Ψ₁ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i) with hB_def
  set B' := 𝓕 Ψ₁ 0 * ∏ i : {j // j ∉ J}, ∫ t, g i t with hB'_def
  have hfi := integrable_of_wordDerivL1 hΨ hD
  -- the decoupled integral
  have hrep := isFourierRep_truncProfile (d := d) (by omega) J Kj hΨ hD hD0
  have hmain : multiInt μ (truncProfile J Kj Ψ₁) c.p c.q c.ξ c.ζ =
      (∏ j ∈ J, ((μ⁻¹ : ℂ) * Pt j)) * B := by
    rw [multiInt_eq μ hrep, integral_truncProfileHat_split J Kj Ψ₁ g]
    congr 1
    exact prod_congr rfl fun j _ => jfactor_eq hμ0 (hK j) _ _
  -- the limiting value
  have hcell : ∏ j, cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j) = (∏ j ∈ J, P j) * ∏ i : {j // j ∉ J}, Δ i := by
    rw [← prod_mul_prod_compl J]
    congr 1
    · exact prod_congr rfl fun j hj => ite_eq_left_of_eq_true _ _ (eq_true hj)
    · rw [prod_subtype Jᶜ (p := (· ∉ J)) (fun x => by simp)]
      exact prod_congr rfl fun i _ => ite_eq_right_iff.2 fun h => absurd h i.2
  have hgΔ : ∀ i, ∫ t, g i t = (μ⁻¹ : ℂ) * Δ i := fun i => by
    simp only [hg_def, hΔ_def]
    rw [deltaInner_cellFn hd, integral_cellInt_scale hμ0]
  have hcardK : Fintype.card {j // j ∉ J} + J.card = n := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have := card_le_univ J
    simp only [hn]
    omega
  have htarget : (μ⁻¹ : ℂ) ^ n * (∫ Ω, Ψ₁ Ω) * ∏ j, cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j) =
      (∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * B' := by
    rw [hcell, hB'_def, fourier_zero_eq_integral]
    simp only [hgΔ, prod_mul_distrib, prod_const, card_univ]
    rw [← hcardK, pow_add]
    ring
  -- bounds on the factors
  have hP : ∀ j, ‖P j‖ ≤ M := fun j => (hM _ _ _ _).2.2.1
  have hPt : ∀ j, ‖Pt j‖ ≤ M := fun j => (hM _ _ _ _).1 μ hμ
  have hPPt : ∀ j, ‖Pt j - P j‖ ≤ M * μ⁻¹ * (1 + ‖c.ξ j‖ + ‖c.ζ j‖) := fun j => by
    rw [norm_sub_rev]; exact (hM _ _ _ _).2.2.2 μ hμ
  have hΔb : ∀ i, ‖Δ i‖ ≤ cellCa d := fun i => norm_deltaInner_cellFn_le hd _ _ _ _
  have hB : ‖B‖ ≤ D0 * (μ⁻¹ * cellCa d) ^ Fintype.card {j // j ∉ J} :=
    norm_B_le hd hμ0 hD0' (fun i : {j // j ∉ J} => c.p i) (fun i : {j // j ∉ J} => c.q i) (fun i : {j // j ∉ J} => c.ξ i)
      (fun i : {j // j ∉ J} => c.ζ i)
  have hBB : ‖B - B'‖ ≤ 4 * Real.pi * H * Fintype.card {j // j ∉ J} * μ ^ (-θ) *
      (μ⁻¹ * cellCa d) ^ Fintype.card {j // j ∉ J} :=
    norm_B_sub_Delta_le hd hμ0 hθ0 hθ1 hfi hH0 hH (fun i : {j // j ∉ J} => c.p i) (fun i : {j // j ∉ J} => c.q i)
      (fun i : {j // j ∉ J} => c.ξ i) (fun i : {j // j ∉ J} => c.ζ i)
  set S := ∑ j, (‖c.ξ j‖ + ‖c.ζ j‖) with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  have hSj : ∀ j, ‖c.ξ j‖ + ‖c.ζ j‖ ≤ S := fun j =>
    single_le_sum (f := fun j => ‖c.ξ j‖ + ‖c.ζ j‖) (fun _ _ => by positivity) (mem_univ j)
  set r := 2 * Mx / μ with hr
  have hr0 : 0 ≤ r := by positivity
  have hrC : μ⁻¹ * cellCa d ≤ r := by
    rw [hr, div_eq_mul_inv, mul_comm (2 * Mx)]
    exact mul_le_mul_of_nonneg_left (by linarith) hμi
  have hrM : μ⁻¹ * Mx ≤ r := by
    rw [hr, div_eq_mul_inv, mul_comm (2 * Mx)]
    exact mul_le_mul_of_nonneg_left (by linarith) hμi
  have hrn : r ^ J.card * r ^ Fintype.card {j // j ∉ J} = r ^ n := by rw [← pow_add, add_comm, hcardK]
  have hKn : (Fintype.card {j // j ∉ J} : ℝ) ≤ n := by exact_mod_cast (by omega : Fintype.card {j // j ∉ J} ≤ n)
  -- the `J`-products
  have hprod1 : ‖∏ j ∈ J, ((μ⁻¹ : ℂ) * Pt j) - ∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)‖ ≤
      r ^ J.card * (n * (1 + S) * μ⁻¹) := by
    have h := norm_prod_sub_prod_le_of J (a := fun j => (μ⁻¹ : ℂ) * Pt j)
      (b := fun j => (μ⁻¹ : ℂ) * P j) (r := μ⁻¹ * Mx)
      (f := fun j => μ⁻¹ * (1 + ‖c.ξ j‖ + ‖c.ζ j‖)) (by positivity) (fun i _ => by positivity)
      (fun i _ => by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
        exact mul_le_mul_of_nonneg_left ((hPt i).trans hMxM) hμi)
      (fun i _ => by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
        exact mul_le_mul_of_nonneg_left ((hP i).trans hMxM) hμi)
      (fun i _ => by
        rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
        calc μ⁻¹ * ‖Pt i - P i‖ ≤ μ⁻¹ * (M * μ⁻¹ * (1 + ‖c.ξ i‖ + ‖c.ζ i‖)) :=
              mul_le_mul_of_nonneg_left (hPPt i) hμi
          _ ≤ μ⁻¹ * (Mx * μ⁻¹ * (1 + ‖c.ξ i‖ + ‖c.ζ i‖)) := by gcongr
          _ = _ := by ring)
    refine h.trans ?_
    have h2 : 2 * (μ⁻¹ * Mx) = r := by rw [hr]; field_simp
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ i ∈ J, μ⁻¹ * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) ≤ ∑ _i ∈ J, μ⁻¹ * (1 + S) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hSj i]) hμi
      _ = J.card * (μ⁻¹ * (1 + S)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * (μ⁻¹ * (1 + S)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_le_univ J
      _ = _ := by ring
  have hprod2 : ‖∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)‖ ≤ r ^ J.card := by
    rw [norm_prod]
    calc ∏ j ∈ J, ‖(μ⁻¹ : ℂ) * P j‖ ≤ ∏ _j ∈ J, r :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
            rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
            exact (mul_le_mul_of_nonneg_left ((hP j).trans hMxM) hμi).trans hrM
      _ = _ := prod_const _
  have hBr : ‖B‖ ≤ D0 * r ^ Fintype.card {j // j ∉ J} :=
    hB.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrC _) hD00)
  have hBBr : ‖B - B'‖ ≤ 4 * Real.pi * H * n * μ ^ (-θ) * r ^ Fintype.card {j // j ∉ J} := by
    refine hBB.trans ?_
    have hμθ := Real.rpow_nonneg hμ0.le (-θ)
    gcongr
  refine ⟨?_, ?_⟩
  · rw [hmain, htarget]
    have heq : (∏ j ∈ J, ((μ⁻¹ : ℂ) * Pt j)) * B - (∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * B' =
        (∏ j ∈ J, ((μ⁻¹ : ℂ) * Pt j) - ∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * B +
          (∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * (B - B') := by ring
    rw [heq]
    have hμθ := Real.rpow_nonneg hμ0.le (-θ)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc ‖(∏ j ∈ J, ((μ⁻¹ : ℂ) * Pt j) - ∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * B +
          (∏ j ∈ J, ((μ⁻¹ : ℂ) * P j)) * (B - B')‖
        ≤ r ^ J.card * (n * (1 + S) * μ⁻¹) * (D0 * r ^ Fintype.card {j // j ∉ J}) +
            r ^ J.card * (4 * Real.pi * H * n * μ ^ (-θ) * r ^ Fintype.card {j // j ∉ J}) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul hprod1 hBr (norm_nonneg _) (by positivity)
          · exact mul_le_mul hprod2 hBBr (norm_nonneg _) (by positivity)
      _ = r ^ n * (n * (D0 * (1 + S) * μ⁻¹ + 4 * Real.pi * H * μ ^ (-θ))) := by
          rw [← hrn]; ring
      _ ≤ r ^ n * ((D0 + 4 * Real.pi * H) * n * (1 + S) * (μ⁻¹ + μ ^ (-θ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h4 : 0 ≤ 4 * Real.pi * H := by positivity
          have h1 : 0 ≤ D0 * (1 + S) * μ ^ (-θ) := by positivity
          have h2 : 0 ≤ 4 * Real.pi * H * μ⁻¹ := by positivity
          have h3 : 0 ≤ 4 * Real.pi * H * μ ^ (-θ) * S := by positivity
          have h5 : 0 ≤ n * (D0 * (1 + S) * μ ^ (-θ) + 4 * Real.pi * H * μ⁻¹ * (1 + S) +
              4 * Real.pi * H * μ ^ (-θ) * S) := by positivity
          nlinarith
      _ = _ := by rw [hr]
  · rw [norm_mul, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ0.le,
      norm_prod]
    have h1 : ‖∫ Ω, Ψ₁ Ω‖ ≤ D0 := (norm_integral_le_integral_norm _).trans hD0'
    have h2 : ∏ j, ‖cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j)‖ ≤ Mx ^ n := by
      calc ∏ j, ‖cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j)‖ ≤ ∏ _j : ι, Mx :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
              unfold cellOp
              split_ifs
              · exact (hM _ _ _ _).2.2.1.trans hMxM
              · exact (norm_deltaInner_cellFn_le hd _ _ _ _).trans hMxC
        _ = _ := by rw [prod_const, card_univ]
    have hMx0 : 0 ≤ Mx := by linarith
    calc μ⁻¹ ^ n * ‖∫ Ω, Ψ₁ Ω‖ * ∏ j, ‖cellOp J j (c.p j) (c.q j) (c.ξ j) (c.ζ j)‖
        ≤ μ⁻¹ ^ n * D0 * Mx ^ n := by gcongr
      _ = (μ⁻¹ * Mx) ^ n * D0 := by ring
      _ ≤ r ^ n * D0 := by gcongr
      _ = _ := by rw [hr]

end WaveTurbulence.ApproxNT
