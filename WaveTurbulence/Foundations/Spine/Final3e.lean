/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3d
import Mathlib.Tactic
/-! The class bound as a real inequality (application of `arith_total`). -/
@[expose] public section
open WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

def smallP (scales : Finset (GBranch G.tree) → ℝ) (L γ δ : ℝ) : LQ G → Prop :=
  fun S => scales S.1 < 1 ∧ 1 + δ * L ^ (2 * γ) * scales S.1 ≤ Real.log L ^ 2

theorem class_real_ineq {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d) (hp : G.IsPlain)
    (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 128 * (180 * d * Real.log L) ≤ Lam)
    (hC : 128 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (hP0 : ∀ S : LQ G, 0 ≤ scales S.1) (hP1 : ∀ S : LQ G, scales S.1 ≤ 1)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)) :
    ((Sigs G).card : ℝ) * 8 ^ G.order *
        ((∏ S : LQ G, (8 * rhoS d L γ δ (scales S.1) * Dt) ^
            (cd.Kn (smallP scales L γ δ) S) /
          (Nat.factorial (cd.Kn (fun S : LQ G => scales S.1 < 1 ∧
            1 + δ * L ^ (2 * γ) * scales S.1 ≤ Real.log L ^ 2) S) : ℝ)) * Real.pi ^ G.order *
          (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^ (G.order - ∑ S : LQ G, cd.Kn (smallP scales L γ δ) S)) ≤
      C1 * ((C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * Lam ^ G.molecule.rho *
        ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) := by
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ.le (Real.rpow_nonneg hL.le _)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have ha1 : 1 ≤ 1 + d * (2 : ℝ) ^ (d - 1) := by
    have : (0 : ℝ) ≤ d * (2 : ℝ) ^ (d - 1) := by positivity
    linarith
  have harsinh : 0 ≤ Real.arsinh (Mv d L) :=
    Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
  have hY1 : 1 ≤ 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) := by linarith
  have hn' : G.order = G.molecule.numFree + ∑ S : LQ G, (2 * π0.m S + 2) := by
    rw [card_atoms_decomp G]
    congr 1
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have := ladderAtoms_card (π0.ladder S).2.1
    rw [π0.atoms S] at this; omega
  have harith := arith_total (fun S : LQ G => π0.m S) (cd.Kn (smallP scales L γ δ)) (smallP scales L γ δ)
    (fun S => Molecule.ladderWeight L γ δ (scales S.1)) (fun S => rhoS d L γ δ (scales S.1))
    G.molecule.numFree G.order d (δ := δ) (ν := ν) (Dt := Dt)
    (Y := 3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) (Λ := Real.log L) (a := 1 + d * (2 : ℝ) ^ (d - 1))
    (dR := (d : ℝ)) (Lam := Lam) (C1 := C1)
    hn' (fun S => cd.Kn_le _ S) (fun S hS => cd.m_le_Kn _ S hS) (fun S hS => cd.Kn_zero _ S hS)
    (fun S hS => by
      rw [lw_small hS.2]
      have := mul_nonneg hc (hP0 S)
      linarith)
    (fun S => by unfold rhoS; positivity)
    (fun S hS => by
      rw [lw_small hS.2]
      exact rhoS_le rfl hc (hP0 S) ha1)
    (fun S hS => lw_large (hP1 S) (hP0 S) hbig hc hS)
    hΛ hδ hδ1 hν hDt0 hY1 hY ha1 rfl hdR hexp hΛLam hfree hC hC1
  have hrho : Fintype.card (LQ G) + G.molecule.numFree = G.molecule.rho := by
    unfold Molecule.rho Molecule.numLadders; simp
  have hprod : ∏ S : LQ G, Molecule.ladderWeight L γ δ (scales S.1) ^ (π0.m S) =
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    rw [← Finset.prod_coe_sort G.molecule.maximalLadders]
    refine Finset.prod_congr rfl (fun S _ => ?_)
    rw [π0.m_eq_ladderLength S]
  rw [hrho, hprod] at harith
  have hLam0 : 0 ≤ Lam := le_trans (by positivity) hexp
  have hDl1 := one_le_Dl hδ hδ1 hν
  have hw : 0 ≤ ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    apply Finset.prod_nonneg
    intro S hS
    apply pow_nonneg
    unfold Molecule.ladderWeight
    apply le_min (sq_nonneg _)
    have := mul_nonneg hc (hP0 ⟨S, hS⟩)
    linarith
  have hC0 : 0 ≤ C1 := by linarith
  refine combine_real (by exact_mod_cast Sigs_card_le G) (by positivity)
    (Finset.prod_nonneg (fun S _ => by
      have : 0 ≤ rhoS d L γ δ (scales S.1) := by unfold rhoS; positivity
      positivity)) (by linarith) harith hC1 (by positivity)

end WaveTurbulence.Ladder
