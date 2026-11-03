/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkFlowLink

/-!
# Local theory of the `a`-system in weighted `ℓ¹` (packet NLS goal 5)

The scale is the weighted Wiener norm `‖c‖_w = ∑ₙ (1 + ‖n‖)^{d+1} |cₙ|` (an algebra for the cubic
nonlinearity), in place of `H^s`, `s > d/2`.

* `exists_isAkSolution_of_mul_le`: **local existence** with time depending on the norm: if
  `𝔇 κ (‖c‖_w + 1)³ ≤ 1`, `κ = |δ / (2 L^{d-γ})|`, a classed solution exists on `[0, 𝔇]`;
* `exists_norm_eq_of_not_exists`: **blow-up alternative**: if no classed solution exists on
  `[0, 𝔇]`, then for every `R > ‖c‖_w` there are `τ ∈ (0, 𝔇)` and a classed solution on `[0, τ]`
  with `‖a(τ)‖_w = R`, i.e. the norm becomes unbounded before `𝔇`.

Uniqueness is `IsAkSolution.eq_of_eq`; persistence of all higher norms is
`IsAkSolution.tsum_weight_le` / `IsAkSolution.exists_uniform_decay`.
-/

public section

noncomputable section

open Complex Set Filter Topology Metric

namespace WaveTurbulence.NLS

variable {d : ℕ} {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ}

theorem norm_ofFun_weightUp (hc : Summable fun n => ‖weightUp c n‖) :
    ‖(L1.ofFun (weightUp c) : L1 d)‖ = ∑' n, ‖weightUp c n‖ := by
  rw [L1.norm_eq, L1.coe_ofFun hc]

/-- **Local existence** in the weighted `ℓ¹` scale, with existence time depending only on the
norm `‖c‖_w = ∑ₙ (1 + ‖n‖)^{d+1} |cₙ|` of the data. -/
theorem exists_isAkSolution_of_mul_le (hL : 0 < L) (hc : Summable fun n => ‖weightUp c n‖)
    (hsmall : 𝔇 * |δ / (2 * L ^ ((d : ℝ) - γ))| * (∑' n, ‖weightUp c n‖ + 1) ^ 3 ≤ 1) :
    ∃ a, IsAkSolution L γ δ 𝔇 c a := by
  set x : L1 d := L1.ofFun (weightUp c)
  set A := ∑' n, ‖weightUp c n‖
  have hA : ‖x‖ = A := norm_ofFun_weightUp hc
  have hA0 : 0 ≤ A := tsum_nonneg fun n => norm_nonneg _
  have hR : (0 : ℝ) ≤ A + 1 := by linarith
  have hball : ∀ t ∈ Icc 0 𝔇, ‖truncFlow L γ δ (A + 1) 𝔇 x t‖ ≤ A + 1 := fun t ht => by
    have h1 := norm_truncFlow_sub_le (L := L) (γ := γ) (δ := δ) hR x ht
    have h2 : |δ / (2 * L ^ ((d : ℝ) - γ))| * (A + 1) ^ 3 * t ≤ 1 := by
      calc |δ / (2 * L ^ ((d : ℝ) - γ))| * (A + 1) ^ 3 * t
          ≤ |δ / (2 * L ^ ((d : ℝ) - γ))| * (A + 1) ^ 3 * 𝔇 := by gcongr; exact ht.2
        _ = 𝔇 * |δ / (2 * L ^ ((d : ℝ) - γ))| * (A + 1) ^ 3 := by ring
        _ ≤ 1 := hsmall
    calc ‖truncFlow L γ δ (A + 1) 𝔇 x t‖ ≤ ‖x‖ + ‖truncFlow L γ δ (A + 1) 𝔇 x t - x‖ := by
          have := norm_sub_norm_le (truncFlow L γ δ (A + 1) 𝔇 x t) x
          linarith
      _ ≤ A + 1 := by rw [hA]; linarith
  have h := isAkSolution_unweight_truncFlow hL hR x hball
  rw [unweight_ofFun_weightUp hc] at h
  exact ⟨_, h⟩

/-- **Blow-up alternative**: if data of finite weighted norm have no classed solution on
`[0, 𝔇]`, then for every `R` above the norm of the data there are `τ ∈ (0, 𝔇)` and a classed
solution on `[0, τ]` whose weighted norm at time `τ` equals `R`. -/
theorem exists_norm_eq_of_not_exists (hL : 0 < L) (hc : Summable fun n => ‖weightUp c n‖)
    (hno : ¬ ∃ a, IsAkSolution L γ δ 𝔇 c a) {R : ℝ} (hR : ∑' n, ‖weightUp c n‖ < R) :
    ∃ τ ∈ Ioo 0 𝔇, ∃ a, IsAkSolution L γ δ τ c a ∧ ∑' n, ‖weightUp (a τ) n‖ = R := by
  set x : L1 d := L1.ofFun (weightUp c)
  have hxR : ‖x‖ < R := by rw [norm_ofFun_weightUp hc]; exact hR
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hxR.le
  have hxc : unweight (x : (Fin d → ℤ) → ℂ) = c := unweight_ofFun_weightUp hc
  set z := truncFlow L γ δ R 𝔇 x
  have hzc : ContinuousOn z (Icc 0 𝔇) := continuousOn_truncFlow hR0 x
  -- the flow leaves the open ball before `𝔇`
  have hexit : ∃ t ∈ Icc 0 𝔇, R ≤ ‖z t‖ := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have h := isAkSolution_unweight_truncFlow hL hR0 x fun t ht => (hcon t ht).le
    rw [hxc] at h
    exact hno ⟨_, h⟩
  set S := Icc 0 𝔇 ∩ (fun t => ‖z t‖) ⁻¹' Ici R
  have hSc : IsClosed S :=
    hzc.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, htR⟩ := hexit
    exact ⟨t, ht, htR⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf S
  have hτS : τ ∈ S := hSc.csInf_mem hSne hSb
  have hτ0 : 0 < τ := by
    refine lt_of_le_of_ne hτS.1.1 fun h0 => ?_
    have h := hτS.2
    rw [← h0] at h
    simp only [mem_preimage, mem_Ici, z, truncFlow_zero] at h
    linarith
  have hbefore : ∀ t ∈ Ico 0 τ, ‖z t‖ ≤ R := fun t ht => by
    by_contra hcon
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hτS.1.2⟩, (not_le.1 hcon).le⟩
    exact absurd (csInf_le hSb htS) (not_le.2 ht.2)
  have hsub : Icc 0 τ ⊆ Icc 0 𝔇 := Icc_subset_Icc le_rfl hτS.1.2
  have hupto : ∀ t ∈ Icc 0 τ, ‖z t‖ ≤ R := by
    have hK : IsClosed (Icc 0 τ ∩ (fun t => ‖z t‖) ⁻¹' Iic R) :=
      (hzc.mono hsub).norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have h1 : Ico 0 τ ⊆ Icc 0 τ ∩ (fun t => ‖z t‖) ⁻¹' Iic R := fun t ht =>
      ⟨Ico_subset_Icc_self ht, hbefore t ht⟩
    have h2 := hK.closure_subset_iff.2 h1
    rw [closure_Ico hτ0.ne] at h2
    exact fun t ht => (h2 ht).2
  have hτR : ‖z τ‖ = R := le_antisymm (hupto τ ⟨hτ0.le, le_rfl⟩) hτS.2
  have hτ𝔇 : τ < 𝔇 := by
    refine lt_of_le_of_ne hτS.1.2 fun hτ => ?_
    have h := isAkSolution_unweight_truncFlow hL hR0 x fun t ht => hupto t (hτ ▸ ht)
    rw [hxc] at h
    exact hno ⟨_, h⟩
  have hsol := isAkSolution_unweight_of_hasDerivWithinAt (L := L) (γ := γ) (δ := δ) (R := R)
    (𝔇 := τ) hL (z := z) (truncFlow_zero L γ δ R 𝔇 x)
    (fun t ht => (hasDerivWithinAt_truncFlow hR0 x (hsub ht)).mono hsub) hupto
  rw [hxc] at hsol
  refine ⟨τ, ⟨hτ0, hτ𝔇⟩, _, hsol, ?_⟩
  rw [weightUp_unweight, ← L1.norm_eq, hτR]

end WaveTurbulence.NLS
