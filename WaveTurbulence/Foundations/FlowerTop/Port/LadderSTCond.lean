/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTBox
/-! # FLOWER-P5: the class condition with stubs (copy-and-thread of `class_cond`, `Final3f`)

The only changes: the integral is over the free frequencies (`class_fourierST`) and the exponent `card FrB`
is bounded by `G.order` (all bases are at least `1`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

theorem Rmono (X : ℝ) (hX : 0 ≤ X) {n N : ℕ} (m : ℕ) (hnN : n ≤ N) (c : ℝ) (hc : 1 ≤ c) :
    X * Real.pi ^ n * c ^ (n - m) ≤ X * Real.pi ^ N * c ^ (N - m) := by
  have hπ : (1 : ℝ) ≤ Real.pi := by have := Real.pi_gt_three; linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hπ hnN) hX)
    (pow_le_pow_right₀ hc (by omega)) (by positivity) (by positivity)

theorem class_condST (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelDataST G d)
    (hamp : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hpend : ∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ D.stubs, b ∉ S) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (D.layer v : ℝ) + 2 ≤ Dt)
    (hs : ∀ v : FrB G D.fix, floorB D v.1 → D.stubTime ≤ (D.layer v.1 : ℝ) + 1)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 128 * (180 * d * Real.log L) ≤ Lam)
    (hC : 128 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (A : Finset (FrB G D.fix)) :
    ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) *
        ∫⁻ α in Wnb (clsPFfree D scales L γ η δ base roots π0),
          ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ ≤
      ENNReal.ofReal (C1 * ((C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * Lam ^ G.molecule.rho *
        ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S)) := by
  by_cases hne : (clsPFfree D scales L γ η δ base roots π0).Nonempty
  swap
  · have : Wnb (clsPFfree D scales L γ η δ base roots π0) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      ext α; simp [Wnb, hne]
    rw [this]; simp
  obtain ⟨αf0, α0, hα0, -⟩ := hne
  have hP0 : ∀ S : LQ G, 0 ≤ scales S.1 := fun S => scale_nonneg hL.le hα0 S
  have hP1 : ∀ S : LQ G, scales S.1 ≤ 1 := fun S => scale_le_one hα0 S
  obtain ⟨cd⟩ := exists_CD G D.toSplicedKernelData L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)
  have hcl := class_fourierST hp hL D hamp hpend scales γ η δ hδ.le base roots π0 cd (smallP scales L γ δ)
    (fun S hS => hS.1) Dt hDt0 hDt hs A
  have hKc0 : 0 ≤ 2 * Real.arsinh (Mv d L) + 1 := by
    have : 0 ≤ Real.arsinh (Mv d L) := Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
    linarith
  have hE := class_E_eq (cd.Kn (smallP scales L γ δ)) (fun S : LQ G => rhoS d L γ δ (scales S.1))
    (fun S => by unfold rhoS; positivity) Dt (2 * Real.arsinh (Mv d L) + 1) hDt0 hKc0
    (Fintype.card (FrB G D.fix))
  have hbound := hcl.trans (le_of_eq hE)
  have hcardJ' : Fintype.card (Σ S : LQ G, Fin (cd.Kn (smallP scales L γ δ) S)) =
      ∑ S, cd.Kn (smallP scales L γ δ) S := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
  rw [hcardJ'] at hbound
  have hcardle : Fintype.card (FrB G D.fix) ≤ G.order := by
    rw [← card_branch_eq G]; exact Fintype.card_subtype_le _
  have hbound' := hbound.trans (ENNReal.ofReal_le_ofReal (Rmono _ (Finset.prod_nonneg fun S _ => by
      have : 0 ≤ rhoS d L γ δ (scales S.1) := by unfold rhoS; positivity
      positivity) _ hcardle _ (by nlinarith [Real.arsinh_nonneg_iff.mpr (show 0 ≤ Mv d L by linarith [one_le_Mv d hL.le])])))
  have hreal := class_real_ineq hL D.toSplicedKernelData hp scales γ η δ hδ hδ1 ν hν base roots Dt Lam C1 hDt0 hΛ hbig hY
    hexp hΛLam hfree hC hC1 hd1 π0 hP0 hP1 cd
  have hcardE : ((Sigs G).card : ℝ≥0∞) = ENNReal.ofReal ((Sigs G).card : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have h8 : (2 : ℝ≥0∞) ^ (3 * G.order) = ENNReal.ofReal (8 ^ G.order) := by
    rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]; norm_num
  calc ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) *
        ∫⁻ α in Wnb (clsPFfree D scales L γ η δ base roots π0),
          ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ
      ≤ ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) * ENNReal.ofReal
          ((∏ S : LQ G, (8 * rhoS d L γ δ (scales S.1) * Dt) ^ (cd.Kn (smallP scales L γ δ) S) /
              (Nat.factorial (cd.Kn (smallP scales L γ δ) S) : ℝ)) * Real.pi ^ G.order *
            (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^ (G.order - ∑ S, cd.Kn (smallP scales L γ δ) S)) :=
        mul_le_mul' le_rfl hbound'
    _ = ENNReal.ofReal (((Sigs G).card : ℝ) * 8 ^ G.order *
          ((∏ S : LQ G, (8 * rhoS d L γ δ (scales S.1) * Dt) ^ (cd.Kn (smallP scales L γ δ) S) /
              (Nat.factorial (cd.Kn (smallP scales L γ δ) S) : ℝ)) * Real.pi ^ G.order *
            (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^ (G.order - ∑ S, cd.Kn (smallP scales L γ δ) S))) := by
        rw [hcardE, h8, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end WaveTurbulence.FlowerP5
