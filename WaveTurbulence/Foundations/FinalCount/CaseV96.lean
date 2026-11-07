/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EvenCase96
import Mathlib.Tactic

/-! # Prop 9.6, the degenerate case `V_α = 0, V_β = 1` (DH23 L1884: "the only `β`-atom will have gap `r = 0` which is not possible")

Summing the conservation law over all atoms gives `c_b = 0` at the unique `β`-atom `b` (all other atoms have degree `4`, hence
`c_v = 0` in `countE`); so its gap is `0`, contradicting (N1). Hence no decoration is admissible and `𝔄₀ = 0`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

theorem caseV (d : ℕ) (γ η : ℝ) : EvenCaseAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 1) := by
  classical
  refine ⟨1, le_rfl, fun m C1 hC1 δ hδ => ⟨1, le_rfl, fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA _ hnodd hnc hab => ?_⟩⟩
  obtain ⟨ha, hb⟩ := hab
  have hE : M.countE L γ δ (0 : Mom d) Adm = 0 := by
    unfold Molecule.countE
    refine le_antisymm (iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_) bot_le
    suffices hz : {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}.encard = 0 by
      rw [hz]
    rw [Set.encard_eq_zero]
    ext κ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, _, hκ⟩
    obtain ⟨b, hbmem⟩ := card_pos.mp (by omega : 0 < (betaAtoms M.atoms cls).card)
    obtain ⟨hbA, hbB⟩ := mem_filter.mp hbmem
    have hbn : ¬ (cls b).IsEps := beta_not_eps hbB
    have hdb : M.deg b = 2 := by
      have := (hS.classes b hbA).mpr hbn
      rcases hS.evenDeg hnodd b hbA with h | h <;> omega
    -- every other atom is an ε-atom of degree four
    have hother : ∀ a ∈ M.atoms, a ≠ b → M.deg a = 4 := by
      intro a haA hab'
      by_cases hae : (cls a).IsEps
      · have : ¬ M.deg a ≤ 2 := fun h => (hS.classes a haA).mp h hae
        rcases hS.evenDeg hnodd a haA with h | h <;> omega
      · exfalso
        rcases cls_cases hae with hα | hβ
        · have : a ∈ alphaAtoms M.atoms cls := mem_filter.mpr ⟨haA, hα⟩
          rw [card_eq_zero.mp ha] at this; simp at this
        · have : a ∈ betaAtoms M.atoms cls := mem_filter.mpr ⟨haA, hβ⟩
          obtain ⟨x, hx⟩ := card_eq_one.mp hb
          rw [hx] at this hbmem
          simp at this hbmem
          exact hab' (this.trans hbmem.symm)
    -- total charge is zero
    have hsum := sum_charges_eq_cross hdec (Y := M.atoms) subset_rfl
    have hcross : crossDarts M M.atoms = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      exact (mem_crossDarts.mp hx).2 (M.atom_mem _)
    rw [hcross, sum_empty] at hsum
    have hcb : c b = 0 := by
      rw [← Finset.sum_erase_add _ _ hbA] at hsum
      have : ∑ v ∈ M.atoms.erase b, c v = 0 :=
        sum_eq_zero fun v hv => hc v (mem_erase.mp hv |>.2) (hother v (mem_erase.mp hv).2 (mem_erase.mp hv).1)
      rw [this, zero_add] at hsum
      exact hsum
    obtain ⟨hout, hin⟩ := hS.dir2 b hbA hdb
    obtain ⟨w, w', hw, hw', hwv, hw'v, hdart⟩ := chain_darts M hout hin
    have hgap := chain_conservation M hw hw' hdart (hdec.2 b hbA)
    have hne : w ≠ w' := by rintro rfl; rw [hw] at hw'; exact absurd hw' (by simp)
    exact hF.betaGap κ hκ b hbA hbB w w' hwv hw'v hne (by rw [Molecule.gapAt]; rw [hgap, hcb])
  unfold Molecule.countA
  rw [hE]; simp

end WaveTurbulence.FinalCountG8
