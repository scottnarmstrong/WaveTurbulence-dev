/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseA
import Mathlib.Tactic

/-! # Core case B: a bridge of `𝕄 ∖ ℓ`

DH23 L1963: "If … `M′∖{ℓ′}` has a bridge, then by … removing this bridge we can divide … `M′∖{ℓ′}` into two
molecules with `E = 2V − 1` and no triple bonds, so the result for … `𝔄(M′∖{ℓ′})` follows from Proposition 10.2".
A side `S` with one crossing dart in `𝕄 ∖ ℓ` contains exactly one end of `ℓ` (parity), so both sides have `E = 2V − 1`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In `𝕄 ∖ ℓ` (connected), every proper part has a crossing dart. -/
theorem IsCore.eraseBond_one_le_cross {M : Molecule V D} (hM : IsCore M) (e : D) :
    ∀ T ⊆ (MoleProp.eraseBond M e).atoms, ∀ a ∈ T, ∀ b ∈ (MoleProp.eraseBond M e).atoms, b ∉ T →
      1 ≤ (crossDarts (MoleProp.eraseBond M e) T).card :=
  fun _ hT _ ha _ hb hbT => card_pos.mpr (crossDarts_nonempty _ (hM.eraseBond_conn e) ha (hT ha) hb hbT)

/-- A side with an odd number of crossing darts in `𝕄 ∖ ℓ` has `2E = 4|S| − |∂S| − 1`. -/
theorem IsCore.eraseBond_piece_bonds_odd {M : Molecule V D} (hM : IsCore M) (e : D) {S : Finset V}
    (hS : S ⊆ M.atoms) (h1 : (crossDarts (MoleProp.eraseBond M e) S).card = 1) :
    ((piece (MoleProp.eraseBond M e) S).bonds.card : ℤ) = 2 * S.card - 1 := by
  have h := two_mul_piece_bonds (MoleProp.eraseBond M e) (Y := S) hS
  have hs := hM.eraseBond_sum_deg e hS
  rw [h1] at h
  split_ifs at hs <;> omega

/-- **Case B: a bridge of `𝕄 ∖ ℓ`** — the second alternative, by the bridge input and Prop 10.2 on both sides. -/
theorem case_bridge {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 0 < L) (hbr : BridgeSplitAt.{u, v} d L γ δ η C1 K B)
    {m : ℕ} (h102 : Prop102At.{u, v} d L γ δ η C1 m) {M : Molecule V D}
    (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) (hM : IsCore M) (e : D) {S : Finset V}
    (hS : S ⊆ M.atoms) (h1 : (crossDarts (MoleProp.eraseBond M e) S).card = 1) (ε₁ : ℝ) :
    SplitBound M e d L γ δ η C1 ε₁
      (K * Real.log L ^ B * (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ))))) := by
  classical
  set N := MoleProp.eraseBond M e with hN
  have hNa : N.atoms = M.atoms := rfl
  have hk := hM.eraseBond_one_le_cross e
  have hT : M.atoms \ S ⊆ M.atoms := sdiff_subset
  have h1c : (crossDarts N (N.atoms \ S)).card = 1 := by rw [card_crossDarts_compl, h1]
  have hconn1 := piece_connected_of_cross N hk (hNa ▸ hS) (by omega : (crossDarts N S).card < 2 * 1)
  have hconn2 := piece_connected_of_cross N hk (sdiff_subset) (by omega : (crossDarts N (N.atoms \ S)).card < 2 * 1)
  have hE1 := hM.eraseBond_piece_bonds_odd e hS h1
  have hE2 := hM.eraseBond_piece_bonds_odd e hT h1c
  obtain ⟨x₁, hx₁⟩ : (crossDarts N S).Nonempty := card_pos.mp (by omega)
  obtain ⟨x₂, hx₂⟩ : (crossDarts N (N.atoms \ S)).Nonempty := card_pos.mp (by omega)
  have hz1 := piece_deg_lt N hx₁
  have hz2 := piece_deg_lt N hx₂
  have hd1 : N.deg (N.atom x₁) ≤ 4 := hM.eraseBond_deg_le e (M.atom_mem x₁.val)
  have hd2 : N.deg (N.atom x₂) ≤ 4 := hM.eraseBond_deg_le e (M.atom_mem x₂.val)
  have hcapN := caps_eraseBond M e hM.cap
  have hle2N : ∀ a b, N.bondsBetween a b ≤ 2 := fun a b => (bondsBetween_eraseBond_le' M e a b).trans (hM.le2 a b)
  have hA1 := afreeSup_piece_le h102 N hsz hS hcapN hle2N hconn1 (mem_crossDarts.mp hx₁).1
    (by omega) hE1
  have hA2 := afreeSup_piece_le h102 N hsz hT hcapN hle2N hconn2 (mem_crossDarts.mp hx₂).1
    (by change (piece N (N.atoms \ S)).deg (N.atom x₂) ≠ 4; omega) hE2
  refine splitBound_of_second M e fun P hP => ?_
  have hmain := hbr N hcapN (hM.eraseBond_loop e) S hS h1 (hM.eraseBond_conn e) hconn1 hconn2 P hP
  refine hmain.trans ((mul_le_mul' (mul_le_mul' le_rfl hA1) hA2).trans ?_)
  have hpos : 0 ≤ L ^ (-(3 / 5 * min γ (1 - γ))) := Real.rpow_nonneg hL.le _
  rw [mul_assoc, ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul' (mul_nonneg hpos hpos)]

end WaveTurbulence.MoleProp4
