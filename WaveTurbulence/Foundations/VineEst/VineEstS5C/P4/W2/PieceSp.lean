/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRep

/-! # P4-W2 (b1): the spatial weights and the point identities of the pieces

All spatial factors of a piece sit on the `𝒦` row (momentum `k` of the retained pair), shifted by `0` or `ε r` (`FlagXY`: the retained leaf has momentum `k`, the lower
joint `k + ε r`, `x = k + ex r`, `y = k + ey r` with `(ex, ey) = (ε, 0)` or `(0, ε)` according to the sign `νA` of the start state).  The weight is
`spS c F G e₁ e₂ = c · G_r(k + e₂ r) F_r(k + e₁ r)` (`P4.W2.spG`; `F` carries the decay: the couple factor, `G` the tree factor).  For the ten non-remainder shapes of
`bundlePt` (A1, A2, KQ, TQ, KT, TT, and the case M shapes `MKQ`, `MTQ`, `MKT`, `MTT`; `A1`/`A2` of case M are the shapes `A2`/`A1` of case A with a sign):
`sp_ident_*` is the identity `shape = (𝒦 time factor) · (spatial weight) · (ℒ time factor)` (times `‖r‖` for the kind-1 shapes, times `|·|^{1-3η}` for the kind-2 shapes with
the joint row `|c₀-c₁|^{-(1-3η)}(J(c₀,c₂) - J(c₁,c₂))`).  `spS_bound` gives the `sup_r 𝔖` bound of the weights from `snorm_spG_le`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.LGSpine WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS3.Eng
open scoped ENNReal ComplexConjugate
variable {d : ℕ}


/-- The momentum shifts of a piece: the lower joint is at `k + ε r`, the retained leaf at `k`; `x = k + ex r`, `y = k + ey r`. -/
def FlagXY (ε ex ey : ℝ) : Prop := |ε| = 1 ∧ ((ex = 0 ∧ ey = ε) ∨ (ey = 0 ∧ ex = ε))

theorem FlagXY.abs_ex_le {ε ex ey : ℝ} (h : FlagXY ε ex ey) : |ex| ≤ 1 := by
  rcases h with ⟨h1, ⟨h2, _⟩ | ⟨_, h2⟩⟩ <;> simp [h2, h1]
theorem FlagXY.abs_ey_le {ε ex ey : ℝ} (h : FlagXY ε ex ey) : |ey| ≤ 1 := by
  rcases h with ⟨h1, ⟨_, h2⟩ | ⟨h2, _⟩⟩ <;> simp [h2, h1]

/-- The sign `s` with `M(y) - M(x) = s ‖r‖ δ_{εr} M (k)`. -/
noncomputable def flagSign (ex : ℝ) : ℝ := if ex = 0 then 1 else -1

theorem diff_shift {ε ex ey : ℝ} (h : FlagXY ε ex ey) (M : Mom d → ℝ) (r k : Mom d) :
    ((M (k + ey • r) : ℝ) : ℂ) - ((M (k + ex • r) : ℝ) : ℂ) =
      ((flagSign ex : ℝ) : ℂ) * ((‖r‖ : ℝ) : ℂ) * diffQuot (ε • r) (cm M) k := by
  have hn : ‖ε • r‖ = ‖r‖ := by rw [norm_smul, Real.norm_eq_abs, h.1, one_mul]
  have key := shift_sub_eq_norm_mul_diffQuot (cm M) (ε • r) k
  rw [hn] at key
  have hε0 : ε ≠ 0 := by intro h0; rw [h0] at hn; have := h.1; rw [h0] at this; simp at this
  rcases h with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
  · simp only [flagSign, h2, h3, ite_true, zero_smul, add_zero, Complex.ofReal_one, one_mul]
    simpa [cm] using key
  · simp only [flagSign, h3, hε0, h2, if_false, zero_smul, add_zero, Complex.ofReal_neg, Complex.ofReal_one, neg_mul,
      one_mul]
    simp only [cm] at key
    linear_combination (-1 : ℂ) * key

/-- The spatial `𝒦` weight of a piece: `c · G_r(k + e₂ r) F_r(k + e₁ r)` (cut off to `‖r‖ ≤ 1`). -/
noncomputable def spS (c : ℝ) (F G : Mom d → Mom d → ℂ) (e1 e2 : ℝ) : Mom d → Mom d → ℂ :=
  spG c F G (fun r => e1 • r) (fun r => e2 • r)

/-- The plain spatial factor. -/
noncomputable def plainF (M : Mom d → ℝ) : Mom d → Mom d → ℂ := fun _ => cm M
/-- The difference-quotient spatial factor in the direction `ε r`. -/
noncomputable def diffF (ε : ℝ) (M : Mom d → ℝ) : Mom d → Mom d → ℂ := fun r => diffQuot (ε • r) (cm M)

theorem spS_apply {c : ℝ} {F G : Mom d → Mom d → ℂ} {e1 e2 : ℝ} {r : Mom d} (hr : ‖r‖ ≤ 1) (k : Mom d) :
    spS c F G e1 e2 r k = (c : ℂ) * (G r (k + e2 • r) * F r (k + e1 • r)) := by
  unfold spS spG; exact cutW_of_le hr k

theorem spS_bound {A W : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (c : ℝ) (F G : Mom d → Mom d → ℂ) {e1 e2 : ℝ} (he1 : |e1| ≤ 1)
    (he2 : |e2| ≤ 1) {βF βG : ℝ} (hF0 : 0 ≤ βF) (hG0 : 0 ≤ βG)
    (hF : ∀ r, ‖r‖ ≤ 1 → SNorm A W (F r) ≤ ENNReal.ofReal βF)
    (hG : ∀ r, ‖r‖ ≤ 1 → SNorm A 0 (G r) ≤ ENNReal.ofReal βG) :
    ⨆ r : Mom d, SNorm A W (spS c F G e1 e2 r) ≤
      ENNReal.ofReal (|c| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * ((2 : ℝ) ^ 0 * (d : ℝ) ^ A * βG) * ((2 : ℝ) ^ W * (d : ℝ) ^ A * βF))) :=
  snorm_spG_le hd hA c F G _ _ (fun r hr => norm_smul_unit he1 hr) (fun r hr => norm_smul_unit he2 hr) hF0 hG0 hF hG

theorem plainF_snorm {A W : ℕ} {M : Mom d → ℝ} {β : ℝ} (h : SNorm A W (cm M) ≤ ENNReal.ofReal β) :
    ∀ r : Mom d, ‖r‖ ≤ 1 → SNorm A W (plainF M r) ≤ ENNReal.ofReal β := fun _ _ => h

theorem diffF_snorm {A W : ℕ} {M : Mom d → ℝ} {β : ℝ} (hβ : 0 ≤ β) {ε : ℝ} (hε : |ε| = 1)
    (h : SNorm (A + 1) W (cm M) ≤ ENNReal.ofReal β) :
    ∀ r : Mom d, ‖r‖ ≤ 1 → SNorm A W (diffF ε M r) ≤ ENNReal.ofReal ((2 : ℝ) ^ W * (d : ℝ) ^ (A + 1) * β) :=
  fun r hr => SNorm_diffQuot_le hβ h (ε • r) (norm_smul_unit hε.le hr)

section Shapes
variable {cq ct : ℝ} {Jq Jt : (Fin 2 → ℝ) → ℂ} {Mq Mt : Mom d → ℝ} {s1 t0 t1 : ℝ} {r k : Mom d}

theorem sp_ident_A1 {ε ex ey : ℝ} (hr : ‖r‖ ≤ 1) :
    conj (sepTerm cq Jq Mq s1 t0 (k + ey • r)) * sepTerm ct Jt Mt t1 t0 (k + ex • r) =
      cJ Jq ![s1, t0] * spS (cq * ct) (plainF Mq) (plainF Mt) ey ex r k * Jt ![t1, t0] := by
  rw [spS_apply hr, conj_sepTerm]; simp only [sepTerm, plainF, cm]; push_cast; ring

theorem sp_ident_A2 (hr : ‖r‖ ≤ 1) (ex ey : ℝ) :
    sepTerm cq Jq Mq t1 t0 (k + ex • r) * conj (sepTerm ct Jt Mt s1 t0 (k + ey • r)) =
      Jq ![t1, t0] * spS (cq * ct) (plainF Mq) (plainF Mt) ex ey r k * cJ Jt ![s1, t0] := by
  rw [spS_apply hr, conj_sepTerm]; simp only [sepTerm, plainF, cm]; push_cast; ring

theorem sp_ident_KQ {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hr : ‖r‖ ≤ 1) :
    conj (sepTerm cq Jq Mq s1 t0 (k + ey • r) - sepTerm cq Jq Mq s1 t0 (k + ex • r)) * sepTerm ct Jt Mt t1 t0 (k + ex • r) =
      ((‖r‖ : ℝ) : ℂ) * (cJ Jq ![s1, t0] * spS (cq * ct * flagSign ex) (diffF ε Mq) (plainF Mt) 0 ex r k * Jt ![t1, t0]) := by
  have hd := diff_shift h Mq r k
  rw [spS_apply hr]
  simp only [sepTerm, plainF, diffF, cJ, zero_smul, add_zero]
  have e : conj ((cq : ℂ) * Jq ![s1, t0] * ((Mq (k + ey • r) : ℝ) : ℂ) - (cq : ℂ) * Jq ![s1, t0] * ((Mq (k + ex • r) : ℝ) : ℂ)) =
      (cq : ℂ) * conj (Jq ![s1, t0]) * (((Mq (k + ey • r) : ℝ) : ℂ) - ((Mq (k + ex • r) : ℝ) : ℂ)) := by
    rw [← mul_sub]; simp [map_mul]
  rw [e, hd]; simp only [cm]; push_cast; ring


theorem k2_cancel_diff (η : ℝ) (J : (Fin 2 → ℝ) → ℂ) (c0 c1 c2 : ℝ) :
    ((|c0 - c1| ^ (1 - 3 * η) : ℝ) : ℂ) * ((((|c0 - c1| ^ (-(1 - 3 * η)) : ℝ) : ℂ)) * (J ![c0, c2] - J ![c1, c2])) =
      J ![c0, c2] - J ![c1, c2] := by
  by_cases h : c0 = c1
  · subst h; simp
  · exact kind2_cancel η (c0 - c1) (sub_ne_zero.mpr h) _

theorem sp_ident_TQ (hr : ‖r‖ ≤ 1) (ex : ℝ) (η : ℝ) :
    conj (sepTerm cq Jq Mq s1 t0 (k + ex • r) - sepTerm cq Jq Mq t1 t0 (k + ex • r)) * sepTerm ct Jt Mt t1 t0 (k + ex • r) =
      ((|s1 - t1| ^ (1 - 3 * η) : ℝ) : ℂ) *
        ((((|s1 - t1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (cJ Jq ![s1, t0] - cJ Jq ![t1, t0])) *
          spS (cq * ct) (plainF Mq) (plainF Mt) ex ex r k * Jt ![t1, t0]) := by
  have hk := k2_cancel_diff η (cJ Jq) s1 t1 t0
  rw [spS_apply hr]
  simp only [sepTerm, plainF, cm]
  have e : conj ((cq : ℂ) * Jq ![s1, t0] * ((Mq (k + ex • r) : ℝ) : ℂ) - (cq : ℂ) * Jq ![t1, t0] * ((Mq (k + ex • r) : ℝ) : ℂ)) =
      (cJ Jq ![s1, t0] - cJ Jq ![t1, t0]) * ((cq : ℂ) * ((Mq (k + ex • r) : ℝ) : ℂ)) := by
    simp [cJ, ← sub_mul, map_mul]; ring
  rw [e]
  push_cast
  linear_combination ((cq : ℂ) * ((Mq (k + ex • r) : ℝ) : ℂ) * ((ct : ℂ) * ((Mt (k + ex • r) : ℝ) : ℂ)) * Jt ![t1, t0]) * (-hk)

theorem sp_ident_KT {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hr : ‖r‖ ≤ 1) :
    sepTerm cq Jq Mq t1 t0 (k + ex • r) * conj (sepTerm ct Jt Mt s1 t0 (k + ex • r) - sepTerm ct Jt Mt s1 t0 (k + ey • r)) =
      ((‖r‖ : ℝ) : ℂ) * (Jq ![t1, t0] * spS (cq * ct * -flagSign ex) (plainF Mq) (diffF ε Mt) ex 0 r k * cJ Jt ![s1, t0]) := by
  have hd := diff_shift h Mt r k
  rw [spS_apply hr]
  simp only [sepTerm, plainF, diffF, cJ, zero_smul, add_zero]
  have e : conj ((ct : ℂ) * Jt ![s1, t0] * ((Mt (k + ex • r) : ℝ) : ℂ) - (ct : ℂ) * Jt ![s1, t0] * ((Mt (k + ey • r) : ℝ) : ℂ)) =
      (ct : ℂ) * conj (Jt ![s1, t0]) * (((Mt (k + ex • r) : ℝ) : ℂ) - ((Mt (k + ey • r) : ℝ) : ℂ)) := by
    rw [← mul_sub]; simp [map_mul]
  rw [e]
  have hd' : ((Mt (k + ex • r) : ℝ) : ℂ) - ((Mt (k + ey • r) : ℝ) : ℂ) =
      -((flagSign ex : ℝ) : ℂ) * ((‖r‖ : ℝ) : ℂ) * diffQuot (ε • r) (cm Mt) k := by
    rw [neg_mul, ← neg_sub, hd]; ring
  rw [hd']; simp only [cm]; push_cast; ring

theorem sp_ident_TT (hr : ‖r‖ ≤ 1) (ex : ℝ) (η : ℝ) :
    sepTerm cq Jq Mq t1 t0 (k + ex • r) * conj (sepTerm ct Jt Mt t1 t0 (k + ex • r) - sepTerm ct Jt Mt s1 t0 (k + ex • r)) =
      ((|t1 - s1| ^ (1 - 3 * η) : ℝ) : ℂ) *
        ((((|t1 - s1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (cJ Jt ![t1, t0] - cJ Jt ![s1, t0])) *
          spS (cq * ct) (plainF Mq) (plainF Mt) ex ex r k * Jq ![t1, t0]) := by
  have hk := k2_cancel_diff η (cJ Jt) t1 s1 t0
  rw [spS_apply hr]
  simp only [sepTerm, plainF, cm]
  have e : conj ((ct : ℂ) * Jt ![t1, t0] * ((Mt (k + ex • r) : ℝ) : ℂ) - (ct : ℂ) * Jt ![s1, t0] * ((Mt (k + ex • r) : ℝ) : ℂ)) =
      (cJ Jt ![t1, t0] - cJ Jt ![s1, t0]) * ((ct : ℂ) * ((Mt (k + ex • r) : ℝ) : ℂ)) := by
    simp [cJ, ← sub_mul, map_mul]; ring
  rw [e]
  push_cast
  linear_combination ((cq : ℂ) * ((Mq (k + ex • r) : ℝ) : ℂ) * ((ct : ℂ) * ((Mt (k + ex • r) : ℝ) : ℂ)) * Jq ![t1, t0]) * (-hk)

theorem sp_ident_MKQ {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hr : ‖r‖ ≤ 1) :
    -((sepTerm cq Jq Mq t1 t0 (k + ex • r) - sepTerm cq Jq Mq t1 t0 (k + ey • r)) * conj (sepTerm ct Jt Mt s1 t0 (k + ey • r))) =
      ((‖r‖ : ℝ) : ℂ) * (Jq ![t1, t0] * spS (cq * ct * flagSign ex) (diffF ε Mq) (plainF Mt) 0 ey r k * cJ Jt ![s1, t0]) := by
  have hd := diff_shift h Mq r k
  rw [spS_apply hr]
  simp only [sepTerm, plainF, diffF, cJ, zero_smul, add_zero]
  have e : (cq : ℂ) * Jq ![t1, t0] * ((Mq (k + ex • r) : ℝ) : ℂ) - (cq : ℂ) * Jq ![t1, t0] * ((Mq (k + ey • r) : ℝ) : ℂ) =
      (cq : ℂ) * Jq ![t1, t0] * (((Mq (k + ex • r) : ℝ) : ℂ) - ((Mq (k + ey • r) : ℝ) : ℂ)) := by ring
  have hd' : ((Mq (k + ex • r) : ℝ) : ℂ) - ((Mq (k + ey • r) : ℝ) : ℂ) =
      -((flagSign ex : ℝ) : ℂ) * ((‖r‖ : ℝ) : ℂ) * diffQuot (ε • r) (cm Mq) k := by
    rw [neg_mul, ← neg_sub, hd]; ring
  rw [e, hd']; simp only [cm]; push_cast; simp [map_mul]; ring

theorem sp_ident_MTQ (hr : ‖r‖ ≤ 1) (ey : ℝ) (η : ℝ) :
    -((sepTerm cq Jq Mq t1 t0 (k + ey • r) - sepTerm cq Jq Mq s1 t0 (k + ey • r)) * conj (sepTerm ct Jt Mt s1 t0 (k + ey • r))) =
      ((|t1 - s1| ^ (1 - 3 * η) : ℝ) : ℂ) *
        ((((|t1 - s1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (Jq ![t1, t0] - Jq ![s1, t0])) *
          spS (cq * ct * -1) (plainF Mq) (plainF Mt) ey ey r k * cJ Jt ![s1, t0]) := by
  have hk := k2_cancel_diff η Jq t1 s1 t0
  rw [spS_apply hr]
  simp only [sepTerm, plainF, cm, cJ]
  push_cast
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (((cq : ℂ) * ((Mq (k + ey • r) : ℝ) : ℂ) * ((ct : ℂ) * ((Mt (k + ey • r) : ℝ) : ℂ)) * conj (Jt ![s1, t0]))) * hk

theorem sp_ident_MKT {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hr : ‖r‖ ≤ 1) :
    -(conj (sepTerm cq Jq Mq s1 t0 (k + ey • r)) * (sepTerm ct Jt Mt t1 t0 (k + ey • r) - sepTerm ct Jt Mt t1 t0 (k + ex • r))) =
      ((‖r‖ : ℝ) : ℂ) * (cJ Jq ![s1, t0] * spS (cq * ct * -flagSign ex) (plainF Mq) (diffF ε Mt) ey 0 r k * Jt ![t1, t0]) := by
  have hd := diff_shift h Mt r k
  rw [spS_apply hr]
  simp only [sepTerm, plainF, diffF, cJ, zero_smul, add_zero]
  have e : conj ((cq : ℂ) * Jq ![s1, t0] * ((Mq (k + ey • r) : ℝ) : ℂ)) = (cq : ℂ) * conj (Jq ![s1, t0]) * ((Mq (k + ey • r) : ℝ) : ℂ) := by
    simp [map_mul]
  have e2 : (ct : ℂ) * Jt ![t1, t0] * ((Mt (k + ey • r) : ℝ) : ℂ) - (ct : ℂ) * Jt ![t1, t0] * ((Mt (k + ex • r) : ℝ) : ℂ) =
      (ct : ℂ) * Jt ![t1, t0] * (((Mt (k + ey • r) : ℝ) : ℂ) - ((Mt (k + ex • r) : ℝ) : ℂ)) := by ring
  rw [e, e2, hd]; simp only [cm]; push_cast; ring

theorem sp_ident_MTT (hr : ‖r‖ ≤ 1) (ey : ℝ) (η : ℝ) :
    -(conj (sepTerm cq Jq Mq s1 t0 (k + ey • r)) * (sepTerm ct Jt Mt s1 t0 (k + ey • r) - sepTerm ct Jt Mt t1 t0 (k + ey • r))) =
      ((|s1 - t1| ^ (1 - 3 * η) : ℝ) : ℂ) *
        ((((|s1 - t1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (Jt ![s1, t0] - Jt ![t1, t0])) *
          spS (cq * ct * -1) (plainF Mq) (plainF Mt) ey ey r k * cJ Jq ![s1, t0]) := by
  have hk := k2_cancel_diff η Jt s1 t1 t0
  rw [spS_apply hr]
  simp only [sepTerm, plainF, cm, cJ]
  push_cast
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (((cq : ℂ) * ((Mq (k + ey • r) : ℝ) : ℂ) * ((ct : ℂ) * ((Mt (k + ey • r) : ℝ) : ℂ)) * conj (Jq ![s1, t0]))) * hk

end Shapes

end WaveTurbulence.VineEstS5C.P4.W2
