/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Trace
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # PROT-OPS slots: `FixedSlotBound` and `DiagonalBound` (o104 Lemma 7.1 (3), (4)), continuous in time -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsSlot

open WaveTurbulence.Flower.ProtOps

theorem timePairing_snoc (m : ℕ) (y : Fin m → ℝ) (a : ℝ) (l : Fin (m + 1) → ℝ) :
    timePairing (m + 1) (Fin.snoc y a) l = timePairing m y (Fin.init l) + a * l (Fin.last m) := by
  simp [timePairing, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem timeBracket_init_le {m : ℕ} (l : Fin (m + 1) → ℝ) :
    timeBracket (Fin.init l) ≤ 2 * timeBracket l := by
  have h1 := one_le_timeBracket l
  refine timeBracket_le (by linarith) fun j => ?_
  exact (bracket_le_timeBracket l j.castSucc).trans (by linarith)

theorem fourierChar_coe_add (a b : ℝ) :
    (Real.fourierChar (a + b) : ℂ) = (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) := by
  rw [AddChar.map_add_eq_mul]; simp

theorem cont_fourierChar_coe {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous fun x => (Real.fourierChar (f x) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp hf)

theorem fixedSlotBound : ProtDefs.FixedSlotBound := by
  intro d r θ hθ
  obtain ⟨C, hC0, hC⟩ := xnormRestr_le_of_ext (d := d) hθ (r + 1) r
  refine ⟨C, hC0, fun q a G K hcont => ?_⟩
  have hν : Continuous (Fin.init : (Fin (r + 1) → ℝ) → Fin r → ℝ) :=
    continuous_pi fun i => continuous_apply _
  have hc : Continuous fun l : Fin (r + 1) → ℝ => (Real.fourierChar (a * l (Fin.last r)) : ℂ) :=
    cont_fourierChar_coe (continuous_const.mul (continuous_apply _))
  refine hC q _ (fun y hy i => by simpa using hy i (Set.mem_univ i)) K _ G Fin.init hν
    timeBracket_init_le _ hc (fun l => by simp) ?_
  intro hG
  have key : ∀ y k, synth (linAtom (cutK r q) Fin.init
      (fun l : Fin (r + 1) → ℝ => (Real.fourierChar (a * l (Fin.last r)) : ℂ))) G y k =
      cutK r q y * G (Fin.snoc y a) k := fun y k =>
    synth_eq_trace hθ hG hcont (fun y => Fin.snoc y a) (fun y l => by
      rw [timePairing_snoc, fourierChar_coe_add, mul_comm]) y k
  refine ⟨_, fun y hy k _ => ?_, fun k => Filter.EventuallyEq.rfl⟩
  rw [key, cutK_one (fun i => by simpa using hy i (Set.mem_univ i)), one_mul]

end WaveTurbulence.Flower.ProtOpsSlot
