/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FactorMain
public import WaveTurbulence.Foundations.Spine.IndGood
/-! # Unit-ball support forces the inserted cutoffs to be one (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums Finset

variable {w d : ℕ} {G : Garden w}

/-- The chain code of slot `s` of the `u` atom of interior rung `i`. -/
def ucode {n : ℕ} (i : Fin n) : Fin 4 → LadderDarts.Ctx.Code n
  | 0 => .inl (i, 0)
  | 1 => .inl (i, 1)
  | 2 => .inr (.inl i.castSucc)
  | 3 => .inr (.inl i.succ)

lemma uSlot_eq_labOf {n : ℕ} (L : ChainLab n (Fin d → ℤ)) (i : Fin n) (s : Fin 4) :
    L.uSlot i s = LadderDarts.Ctx.labOf L (ucode i s) := by
  fin_cases s <;> rfl

/-- The centres of the rung pair `(x, y)`. -/
noncomputable def pairCentres {n : ℕ} (S : ChainSigns n) (ctr : LadderDarts.Ctx.Code n → Mom d)
    (i : Fin n) : (Fin d → ℝ) × (Fin d → ℝ) :=
  (fun j => (ctr (ucode i (S.σ i 0)) - ctr (ucode i (S.σ i 2))) j,
   fun j => (ctr (ucode i (S.σ i 0)) - ctr (ucode i (S.σ i 3))) j)

lemma pair_cutW_eq_one {n : ℕ} (S : ChainSigns n) (ctr : LadderDarts.Ctx.Code n → Mom d)
    {L : ℝ} (hL : 0 < L) (base : Mom d) (a0 b0 : Fin d → ℤ) (P : Fin n → Pt d)
    (hball : ∀ c, ‖base + latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) c) - ctr c‖ ≤ 1)
    (k : Fin n) :
    cutW L (pairCentres S ctr k).1 (pairCentres S ctr k).2 (P k) = 1 := by
  have hx : (P k).1 = (S.inv a0 b0 P).uSlot k (S.σ k 0) - (S.inv a0 b0 P).uSlot k (S.σ k 2) := by
    rw [S.inv_uSlot, S.inv_uSlot, ChainSigns.tau_perm, ChainSigns.tau_perm]
    simp [tvec]
  have hy : (P k).2 = (S.inv a0 b0 P).uSlot k (S.σ k 0) - (S.inv a0 b0 P).uSlot k (S.σ k 3) := by
    rw [S.inv_uSlot, S.inv_uSlot, ChainSigns.tau_perm, ChainSigns.tau_perm]
    simp [tvec]
  have key : ∀ s s' : Fin 4, ∀ j : Fin d,
      |(((S.inv a0 b0 P).uSlot k s - (S.inv a0 b0 P).uSlot k s') j : ℝ) / L -
        (ctr (ucode k s) - ctr (ucode k s')) j| ≤ 2 := by
    intro s s' j
    rw [uSlot_eq_labOf, uSlot_eq_labOf]
    have h1 := hball (ucode k s)
    have h2 := hball (ucode k s')
    have h3 : ‖(latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) -
        latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s'))) -
        (ctr (ucode k s) - ctr (ucode k s'))‖ ≤ 2 := by
      have : (latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) -
        latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s'))) -
        (ctr (ucode k s) - ctr (ucode k s')) =
        (base + latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) - ctr (ucode k s)) -
        (base + latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s')) - ctr (ucode k s')) := by
        abel
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have h4 := PiLp.norm_apply_le ((latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) -
        latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s'))) -
        (ctr (ucode k s) - ctr (ucode k s'))) j
    rw [Real.norm_eq_abs] at h4
    have e : ((((LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) -
        (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s'))) j : ℤ) : ℝ) / L -
        (ctr (ucode k s) - ctr (ucode k s')) j =
        ((latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s)) -
        latticePoint L (LadderDarts.Ctx.labOf (S.inv a0 b0 P) (ucode k s'))) -
        (ctr (ucode k s) - ctr (ucode k s'))).ofLp j := by
      simp [latticePoint, sub_div]
    rw [e]
    exact h4.trans h3
  apply cutW_eq_one hL
  · intro j; rw [hx]; exact key _ _ j
  · intro j; rw [hy]; exact key _ _ j

end WaveTurbulence.LadderDecay
