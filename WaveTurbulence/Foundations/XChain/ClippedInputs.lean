/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInputFunctionBound
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum
public import WaveTurbulence.Foundations.XChain.SysDraft.Kernel
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! Values of the remainder beyond the current stage can be set to zero without affecting any kernel. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def clipRemainder {d : ℕ} (p : ℕ) (R : ℕ → Mom d → ℝ) : ℕ → Mom d → ℝ :=
  fun q k => if q ≤ p then R q k else 0

theorem clipRemainder_eq {d p q : ℕ} (R : ℕ → Mom d → ℝ) (hq : q ≤ p) :
    clipRemainder p R q = R q := by
  funext k
  exact ite_eq_left hq

theorem inputsF_clip_eq (P : WTParams) (R : ℕ → Mom P.d → ℝ) {p q : ℕ} (hq : q ≤ p) :
    inputsF P (clipRemainder p R) q = inputsF P R q := by
  funext k
  exact congrArg (fun z : ℝ => P.φ (P.δ * q) k + z) (congrFun (clipRemainder_eq R hq) k)

theorem KG_clip_inputs (P : WTParams) (R : ℕ → Mom P.d → ℝ) {w p : ℕ}
    (LG : LayeredGarden w) (hl : ∀ a : GNode LG.garden.tree, LG.layer a ≤ p)
    (t : ℝ) (n : Fin w → (Fin P.d → ℤ)) :
    KG P.L P.γ P.δ (inputsF P (clipRemainder p R)) LG t n =
      KG P.L P.γ P.δ (inputsF P R) LG t n :=
  SysAPI.KG_congr_inputs P.L P.γ P.δ LG t n (fun a => inputsF_clip_eq P R (hl a))

theorem lambda_ge_dimension (P : WTParams) (hd : 1 ≤ P.d) {q : ℕ} (hq : q ≤ P.D) :
    (P.d : ℝ) + 1 ≤ (P.Lambda q : ℝ) := by
  have hb : 0 < 40 * P.d := by omega
  have he : 1 ≤ P.D + 1 - q := by omega
  have hp : 40 * P.d ≤ P.Lambda q := by
    simpa only [WTParams.Lambda, pow_one] using Nat.pow_le_pow_right hb he
  have hpr : (40 : ℝ) * P.d ≤ P.Lambda q := by exact_mod_cast hp
  have hdr : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  linarith

theorem summable_schwartz_lattice {d : ℕ} (L : ℝ) (hL : 1 ≤ L) (f : SchwartzMap (Mom d) ℝ) :
    Summable (fun n : Fin d → ℤ => |f (latticePoint L n)|) := by
  obtain ⟨C, _, hC⟩ := schwartz_exists_bracket_bound f (d + 1)
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => hC _)
  exact (summable_lattice_bracket_weight L ((d + 1 : ℕ) : ℝ) hL (by push_cast; rfl)).mul_left C

theorem summable_clipped_inputs (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ)
    (hp : p ≤ P.D) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hR : RemainderBound P R p) :
    ∀ q, Summable (fun n : Fin P.d → ℤ => |inputsF P (clipRemainder p R) q (latticePoint P.L n)|) := by
  intro q
  have hφ := summable_schwartz_lattice P.L hL (P.φ (P.δ * q))
  by_cases hq : q ≤ p
  · have hRq : Summable (fun n : Fin P.d → ℤ => |R q (latticePoint P.L n)|) := by
      apply Summable.of_nonneg_of_le (fun n => abs_nonneg _)
        (fun n => SNormR_pointwise (R q) (P.L ^ (-P.theta q))
          (Real.rpow_nonneg (zero_le_one.trans hL) _) (hR q hq) _)
      exact (summable_lattice_bracket_weight P.L (P.Lambda q) hL
        (lambda_ge_dimension P hd (hq.trans hp))).mul_left _
    rw [inputsF_clip_eq P R hq]
    exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_add_le _ _) (hφ.add hRq)
  · simpa only [inputsF, clipRemainder, ite_eq_right hq, add_zero] using hφ

end WaveTurbulence.Induct
