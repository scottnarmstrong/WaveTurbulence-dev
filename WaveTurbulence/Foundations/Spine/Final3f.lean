/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3e
import Mathlib.Tactic
/-! The class condition in `ℝ≥0∞`. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem card_branch_eq (G : Garden w) : Fintype.card (GBranch G.tree) = G.order := by
  have := WaveTurbulence.Mole.garden_card_atoms G
  rw [← this]
  exact Finset.card_univ.symm

theorem class_cond (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (D.layer v : ℝ) + 1 ≤ Dt)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 128 * (180 * d * Real.log L) ≤ Lam)
    (hC : 128 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (A : Finset (GBranch G.tree)) :
    ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) *
        ∫⁻ α in Wnb (clsPF G D scales L γ η δ base roots π0),
          ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ ≤
      ENNReal.ofReal (C1 * ((C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * Lam ^ G.molecule.rho *
        ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S)) := by
  by_cases hne : (clsPF G D scales L γ η δ base roots π0).Nonempty
  swap
  · have : Wnb (clsPF G D scales L γ η δ base roots π0) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      ext α; simp [Wnb, hne]
    rw [this]; simp
  obtain ⟨α0, hα0⟩ := hne
  have hP0 : ∀ S : LQ G, 0 ≤ scales S.1 := fun S => scale_nonneg hL.le hα0 S
  have hP1 : ∀ S : LQ G, scales S.1 ≤ 1 := fun S => scale_le_one hα0 S
  obtain ⟨cd⟩ := exists_CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)
  have hcl := class_fourier hp hL D hamp scales γ η δ hδ.le base roots π0 cd (smallP scales L γ δ)
    (fun S hS => hS.1) Dt hDt0 hDt A
  have hKc0 : 0 ≤ 2 * Real.arsinh (Mv d L) + 1 := by
    have : 0 ≤ Real.arsinh (Mv d L) := Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
    linarith
  have hE := class_E_eq (cd.Kn (smallP scales L γ δ)) (fun S : LQ G => rhoS d L γ δ (scales S.1))
    (fun S => by unfold rhoS; positivity) Dt (2 * Real.arsinh (Mv d L) + 1) hDt0 hKc0
    (Fintype.card (GBranch G.tree))
  have hbound := hcl.trans (le_of_eq hE)
  have hcardJ' : Fintype.card (Σ S : LQ G, Fin (cd.Kn (smallP scales L γ δ) S)) =
      ∑ S, cd.Kn (smallP scales L γ δ) S := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
  rw [card_branch_eq G, hcardJ'] at hbound
  have hreal := class_real_ineq hL D hp scales γ η δ hδ hδ1 ν hν base roots Dt Lam C1 hDt0 hΛ hbig hY
    hexp hΛLam hfree hC hC1 hd1 π0 hP0 hP1 cd
  have hcardE : ((Sigs G).card : ℝ≥0∞) = ENNReal.ofReal ((Sigs G).card : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have h8 : (2 : ℝ≥0∞) ^ (3 * G.order) = ENNReal.ofReal (8 ^ G.order) := by
    rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]; norm_num
  calc ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) *
        ∫⁻ α in Wnb (clsPF G D scales L γ η δ base roots π0),
          ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ
      ≤ ((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order) * ENNReal.ofReal
          ((∏ S : LQ G, (8 * rhoS d L γ δ (scales S.1) * Dt) ^ (cd.Kn (smallP scales L γ δ) S) /
              (Nat.factorial (cd.Kn (smallP scales L γ δ) S) : ℝ)) * Real.pi ^ G.order *
            (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^ (G.order - ∑ S, cd.Kn (smallP scales L γ δ) S)) :=
        mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal (((Sigs G).card : ℝ) * 8 ^ G.order *
          ((∏ S : LQ G, (8 * rhoS d L γ δ (scales S.1) * Dt) ^ (cd.Kn (smallP scales L γ δ) S) /
              (Nat.factorial (cd.Kn (smallP scales L γ δ) S) : ℝ)) * Real.pi ^ G.order *
            (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^ (G.order - ∑ S, cd.Kn (smallP scales L γ δ) S))) := by
        rw [hcardE, h8, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end WaveTurbulence.Ladder
