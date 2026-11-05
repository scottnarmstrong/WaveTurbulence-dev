/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Count
public import WaveTurbulence.Foundations.Spine.LocAlg
public import WaveTurbulence.Foundations.Spine.GenClass4
import Mathlib.Tactic
/-! The rung-sum relation of TARGET L2013–L2018 for decorations of the spectrum:
`α_{u_j} + α_{v_j} = ⟨ψ, Y⁰_j⟩ + C_j + E_j` with `ψ = δ L^{2γ} · flux`, `‖E_j‖ ≤ 4 δ L^{2γ} ‖r‖`. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint

/-- The fixed vector `Y⁰_j`, from the centers of the rail darts. -/
noncomputable def Y0rung {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d) (uR vR : ℕ → GardenDart G)
    (j : ℕ) : Mom d :=
  (D.center (uR (j - 1)) + D.center (vR (j - 1))) - (D.center (uR j) + D.center (vR j))

/-- The fixed constant `C_j`. -/
noncomputable def Crung {w d : ℕ} (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d)
    (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (a b : GBranch G.tree) : ℝ :=
  δ * L ^ (2 * γ) * (Mole.gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) a +
    Mole.gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) b) +
    D.frequency a + D.frequency b

theorem rung_sum_relation {w d : ℕ} (G : Garden w) (hp : G.IsPlain) {L : ℝ} (hL : 0 < L)
    (D : SplicedKernelData G d) (hamp : SplicedAmplitudeBounds G D) (γ δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hb : ∀ x ∈ G.molecule.bonds, ‖base + latticePoint L (bondIndex G z.1 x) - D.center x‖ ≤ 1)
    {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree} (hLad : G.molecule.IsLadder u v)
    (uR vR : ℕ → GardenDart G)
    (huR : ∀ j < m, neighborDarts G.molecule (rowN u j) (rowN u (j + 1)) = {uR j} ∧
      neighborDarts G.molecule (rowN v j) (rowN v (j + 1)) = {vR j})
    (hm : 1 ≤ m) {r : Mom d} (hr : G.molecule.IsLadderGap L base (bondIndex G z.1) u v hm r)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) :
    ∃ E : ℝ, |E| ≤ 4 * (δ * L ^ (2 * γ)) * ‖r‖ ∧
      splicedFrequency G D L γ δ base z.1 (rowN u j) + splicedFrequency G D L γ δ base z.1 (rowN v j) =
        inner ℝ ((δ * L ^ (2 * γ)) • flux G.molecule L base (bondIndex G z.1) uR vR 0) (Y0rung G D uR vR j) +
          Crung G hp D L γ δ base roots (rowN u j) (rowN v j) + E := by
  classical
  set M := G.molecule with hMdef
  set κ := bondIndex G z.1 with hκdef
  have hL0 : L ≠ 0 := hL.ne'
  have hM : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x _ => WaveTurbulence.Mole.garden_molecule_deg_le_four G x
  have hdec := spliced_molecule_decoration G hp hL0 base roots z
  have hκ : ∀ x, κ (M.mate x) = κ x := hdec.1
  -- degree four at interior atoms
  have hdeg : ∀ i, 1 ≤ i → i < m → M.deg (rowN u i) = 4 ∧ M.deg (rowN v i) = 4 := by
    intro i hi1 him
    have hjle : i ≤ m := him.le
    have hd1 : i - 1 ≤ m := by omega
    have hd2 : i + 1 ≤ m := by omega
    have hl := ladderN_rail M hLad (show i - 1 < m by omega)
    rw [show i - 1 + 1 = i by omega] at hl
    have hr' := ladderN_rail M hLad him
    have hl1 : M.bondsBetween (rowN u i) (rowN u (i - 1)) = 1 := by
      rw [LadderDisjoint.bondsBetween_comm]; exact hl.1
    have hl2 : M.bondsBetween (rowN v i) (rowN v (i - 1)) = 1 := by
      rw [LadderDisjoint.bondsBetween_comm]; exact hl.2.1
    have hrung := ladderN_rung M hLad hjle
    have hrung' : M.bondsBetween (rowN v i) (rowN u i) = 2 := by
      rw [LadderDisjoint.bondsBetween_comm]; exact hrung
    refine ⟨?_, ?_⟩
    · exact deg_interior M (ladderN_uv M hLad hjle hjle) (ladderN_uu M hLad hjle hd1 (by omega))
        (ladderN_uu M hLad hjle hd2 (by omega)) (Ne.symm (ladderN_uv M hLad hd1 hjle))
        (Ne.symm (ladderN_uv M hLad hd2 hjle)) (ladderN_uu M hLad hd1 hd2 (by omega))
        hrung hl1 hr'.1 (hM _ (by rw [rowN_of_le u hjle]; exact Finset.mem_univ _))
    · exact deg_interior M (Ne.symm (ladderN_uv M hLad hjle hjle)) (ladderN_vv M hLad hjle hd1 (by omega))
        (ladderN_vv M hLad hjle hd2 (by omega)) (ladderN_uv M hLad hjle hd1) (ladderN_uv M hLad hjle hd2)
        (ladderN_vv M hLad hd1 hd2 (by omega)) hrung' hl2 hr'.2.1
        (hM _ (by rw [rowN_of_le v hjle]; exact Finset.mem_univ _))
  have hca : ∀ i, 1 ≤ i → i < m →
      ∑ x ∈ M.dartsAt (rowN u i), M.dartSign x • Molecule.kvec L base κ x = 0 ∧
      ∑ x ∈ M.dartsAt (rowN v i), M.dartSign x • Molecule.kvec L base κ x = 0 := fun i hi1 him =>
    ⟨conservation_deg_four G hp hL0 base roots z _ (hdeg i hi1 him).1,
      conservation_deg_four G hp hL0 base roots z _ (hdeg i hi1 him).2⟩
  have hfc := flux_const M hM hLad L base κ hκ uR vR huR hca
  have hgam := (ladder_gamma_rung M hM hLad L base κ hκ uR vR huR hj1 hjm (hca j hj1 hjm).1
    (hca j hj1 hjm).2).1
  rw [hfc (j - 1) (by omega)] at hgam
  obtain ⟨s, hs, hflux0⟩ := flux_zero_eq_gap M hLad L base κ uR vR huR hm hr
  have hnorm : ‖flux M L base κ uR vR 0‖ = ‖r‖ := by
    rw [hflux0, norm_smul]; rcases hs with rfl | rfl <;> simp
  have hnear : ∀ x : GardenDart G, ‖Molecule.kvec L base κ x - D.center x‖ ≤ 1 :=
    fun x => dart_near_center G D hamp L base κ hκ hb x
  refine ⟨inner ℝ ((δ * L ^ (2 * γ)) • flux M L base κ uR vR 0)
    (Yrung L base κ uR vR j - Y0rung G D uR vR j), ?_, ?_⟩
  · have hYb : ‖Yrung L base κ uR vR j - Y0rung G D uR vR j‖ ≤ 4 := by
      have : Yrung L base κ uR vR j - Y0rung G D uR vR j =
          ((Molecule.kvec L base κ (uR (j - 1)) - D.center (uR (j - 1))) +
            (Molecule.kvec L base κ (vR (j - 1)) - D.center (vR (j - 1)))) -
          ((Molecule.kvec L base κ (uR j) - D.center (uR j)) +
            (Molecule.kvec L base κ (vR j) - D.center (vR j))) := by
        unfold Yrung Y0rung; abel
      rw [this]
      calc _ ≤ ‖(Molecule.kvec L base κ (uR (j - 1)) - D.center (uR (j - 1))) +
            (Molecule.kvec L base κ (vR (j - 1)) - D.center (vR (j - 1)))‖ +
          ‖(Molecule.kvec L base κ (uR j) - D.center (uR j)) +
            (Molecule.kvec L base κ (vR j) - D.center (vR j))‖ := norm_sub_le _ _
        _ ≤ (1 + 1) + (1 + 1) := add_le_add ((norm_add_le _ _).trans (add_le_add (hnear _) (hnear _)))
            ((norm_add_le _ _).trans (add_le_add (hnear _) (hnear _)))
        _ = 4 := by norm_num
    have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ (Real.rpow_nonneg hL.le _)
    calc |inner ℝ ((δ * L ^ (2 * γ)) • flux M L base κ uR vR 0)
          (Yrung L base κ uR vR j - Y0rung G D uR vR j)|
        ≤ ‖(δ * L ^ (2 * γ)) • flux M L base κ uR vR 0‖ * ‖Yrung L base κ uR vR j - Y0rung G D uR vR j‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ((δ * L ^ (2 * γ)) * ‖r‖) * 4 := by
          rw [norm_smul, Real.norm_of_nonneg hc, hnorm]
          exact mul_le_mul_of_nonneg_left hYb (by positivity)
      _ = _ := by ring
  · have h2 : M.Gamma L base κ (rowN u j) + M.Gamma L base κ (rowN v j) =
        - inner ℝ (flux M L base κ uR vR 0) (Yrung L base κ uR vR j) := by
      rw [hgam, inner_neg_left]
    have hS : splicedFrequency G D L γ δ base z.1 (rowN u j) + splicedFrequency G D L γ δ base z.1 (rowN v j) =
        inner ℝ ((δ * L ^ (2 * γ)) • flux M L base κ uR vR 0) (Yrung L base κ uR vR j) +
          Crung G hp D L γ δ base roots (rowN u j) (rowN v j) := by
      rw [splicedFrequency_eq G hp hL0 D γ δ base roots z, splicedFrequency_eq G hp hL0 D γ δ base roots z]
      unfold Crung
      rw [real_inner_smul_left]
      linear_combination (-(δ * L ^ (2 * γ))) * h2
    rw [hS, inner_sub_right]
    ring

end WaveTurbulence.Ladder
