/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpCChain
public import WaveTurbulence.Foundations.FinalCount.BiBridgeCount
import Mathlib.Tactic

/-! # Operation (c): the counting inequality (DH23 L1861, Lemma A.3(1))

`Y` is a connected chain of atoms with `in = out = 1`, attached to the rest by two darts. One atom `b₀ ∈ Y` has a nonzero
gap `c_{b₀}`. All labels on darts at `Y` are determined by the label `k_w` of the outgoing dart at `b₀` (`chain_agree`),
and `k_w` lies in a slab of the unit ball with normal `c_{b₀}` (energy window at `b₀`): `DotStrip`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem countEFree_le_chain_rho (M : Molecule V D) {Y : Finset V} (hYM : Y ⊆ M.atoms)
    (hch : ∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hconn : ∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b) {d : ℕ} (hd : 0 < d) {L γ δ : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (ρ : ℝ) (hρ : 0 < ρ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) :
    ∃ n : ℕ, (n : ℝ) ≤ min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1)) ∧
      MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤ (n : ℕ∞) *
        MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility M Y Adm) := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set B := min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * τ * L / ρ + 1)) with hB
  have hB0 : 0 ≤ B := le_min (by positivity) (by positivity)
  refine ⟨⌊B⌋₊, Nat.floor_le hB0, ?_⟩
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | M.IsDecoration L 0 c κ ∧ M.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ} with hA
  have hAfin : A.Finite := (Mole.finite_restricted M hLp γ δ 0 β k0).subset fun _ h => h.2.1
  have hmain := MoleProp.encard_le_deletedImage_mul_post M Y hLp γ δ 0 Adm c β k0 hk0
  refine hmain.trans (mul_le_mul' ?_ le_rfl)
  rcases A.eq_empty_or_nonempty with hA0 | ⟨κ₀, hκ₀⟩
  · show ((MoleProp.deletedLabels M Y '' A).ncard : ℕ∞) ≤ _
    rw [hA0, Set.image_empty, Set.ncard_empty, Nat.cast_zero]
    exact bot_le
  -- the atom with a nonzero gap
  obtain ⟨y₀, y₀', hy₀Y, hy₀a, hy₀ne, hy₀κ⟩ := hAdm κ₀ hκ₀.2.2
  set b0 := M.atom y₀ with hb0
  have hb0Y : b0 ∈ Y := hy₀Y
  obtain ⟨w, w', hw, hw', hwv, hw'v, hdart⟩ := chain_darts M (hch b0 hb0Y).1 (hch b0 hb0Y).2
  have hy₀m : y₀ ∈ M.dartsAt b0 := by simp [Molecule.dartsAt, hb0]
  have hy₀'m : y₀' ∈ M.dartsAt b0 := by simp [Molecule.dartsAt, hy₀a]
  rw [hdart] at hy₀m hy₀'m
  simp only [mem_insert, mem_singleton] at hy₀m hy₀'m
  have hyy : y₀ ≠ y₀' := hy₀ne
  have hρ' : ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ₀ w - Molecule.kvec L (0 : Mom d) κ₀ w'‖ := by
    rcases hy₀m with rfl | rfl <;> rcases hy₀'m with rfl | rfl
    · exact absurd rfl hy₀ne
    · exact hy₀κ
    · rw [norm_sub_rev]; exact hy₀κ
    · exact absurd rfl hy₀ne
  have hww : κ₀ w ≠ κ₀ w' := by
    intro h
    have : ‖Molecule.kvec L (0 : Mom d) κ₀ w - Molecule.kvec L (0 : Mom d) κ₀ w'‖ = 0 := by
      simp [Molecule.kvec, h]
    linarith
  -- the gap
  set r : Mom d := c b0 with hr
  have hrgap : ∀ κ ∈ A, Molecule.kvec L 0 κ w - Molecule.kvec L 0 κ w' = r := fun κ hκ =>
    chain_conservation M hw hw' hdart (hκ.1.2 b0 (hYM hb0Y))
  have hrnorm : ρ ≤ ‖r‖ := by
    rw [← hrgap κ₀ hκ₀]
    exact hρ'
  set β' : ℝ := (‖r‖ ^ 2 + β b0) / 2 with hβ'
  set K1 : Finset (Fin d → ℤ) := hAfin.toFinset.image (fun κ => κ w) with hK1
  have hK1mem : ∀ k ∈ K1, ∃ κ ∈ A, κ w = k := by
    intro k hk
    obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hk
    exact ⟨κ, hAfin.mem_toFinset.mp hκ, rfl⟩
  have hK1strip : ∀ n ∈ K1, |inner ℝ r (latticePoint L n) - β'| ≤ τ / 2 := by
    intro n hn
    obtain ⟨κ, hκ, rfl⟩ := hK1mem n hn
    have hkw : Molecule.kvec L 0 κ w = latticePoint L (κ w) := by simp [Molecule.kvec]
    have hkw' : Molecule.kvec L 0 κ w' = Molecule.kvec L 0 κ w - r := by rw [← hrgap κ hκ]; abel
    have hΓ := chain_gamma M hw hw' hdart L κ
    have hnorm : ‖Molecule.kvec L 0 κ w‖ ^ 2 - ‖Molecule.kvec L 0 κ w'‖ ^ 2 =
        2 * inner ℝ r (Molecule.kvec L 0 κ w) - ‖r‖ ^ 2 := by
      rw [hkw', norm_sub_sq_real, real_inner_comm]; ring
    have hwin := hκ.2.1.1 b0 (hYM hb0Y)
    rw [hΓ, hnorm] at hwin
    rw [hkw] at hwin
    have : inner ℝ r (latticePoint L (κ w)) - β' =
        (2 * inner ℝ r (latticePoint L (κ w)) - ‖r‖ ^ 2 - β b0) / 2 := by rw [hβ']; ring
    rw [this, abs_div, abs_two]
    have hwin' : |2 * inner ℝ r (latticePoint L (κ w)) - ‖r‖ ^ 2 - β b0| ≤ τ := hwin
    linarith
  have hK1ball : ∀ n ∈ K1, ‖latticePoint L n - k0 w‖ ≤ 1 := by
    intro n hn
    obtain ⟨κ, hκ, rfl⟩ := hK1mem n hn
    have := hκ.2.1.2 w
    simpa [Molecule.kvec] using this
  have hK1card : (K1.card : ℝ) ≤ B := by
    have h := CountLemmas.card_dot_strip_ball_norm_le hd K1 hLp zero_le_one (by positivity : (0 : ℝ) ≤ τ / 2) hρ
      (k0 w) r β' hrnorm hK1ball hK1strip
    have hcap : (K1.card : ℝ) ≤ (2 * L + 1) ^ d := by
      have h2 := Counting.card_le_of_coordinate_bounds K1 (fun i => L * k0 w i) (L := L * 1) (by positivity)
        (fun n hn i => CountLemmas.coordinate_bound_of_ball hLp (k0 w) n (hK1ball n hn) i)
      simpa using h2
    refine le_min hcap ?_
    refine (by simpa using h : (K1.card : ℝ) ≤ _).trans (le_of_eq ?_)
    congr 2
    ring
  have hK1nat : K1.card ≤ ⌊B⌋₊ := Nat.le_floor hK1card
  -- labels on deleted darts are determined by `κ w`
  let refk : (Fin d → ℤ) → (D → (Fin d → ℤ)) := fun k =>
    if h : ∃ κ ∈ A, κ w = k then h.choose else κ₀
  have hrefk : ∀ k ∈ K1, refk k ∈ A ∧ refk k w = k := by
    intro k hk
    have h := hK1mem k hk
    simp only [refk, dif_pos h]
    exact h.choose_spec
  have himg : MoleProp.deletedLabels M Y '' A ⊆ (fun k => MoleProp.deletedLabels M Y (refk k)) '' (K1 : Set _) := by
    rintro _ ⟨κ, hκ, rfl⟩
    have hk : κ w ∈ K1 := mem_image.mpr ⟨κ, hAfin.mem_toFinset.mpr hκ, rfl⟩
    obtain ⟨hrA, hrx⟩ := hrefk _ hk
    refine ⟨κ w, hk, ?_⟩
    have hag := chain_agree M hYM hch hconn hLp.ne' hrA.1 hκ.1 (z0 := w) (by rw [hwv]; exact hb0Y) hrx
    funext ⟨z, hz⟩
    simp only [MoleProp.deletedLabels]
    by_cases h1 : M.atom z ∈ Y
    · exact hag z h1
    · have h2 : M.atom (M.mate z) ∈ Y := by
        by_contra h2; exact hz ⟨h1, h2⟩
      have := hag (M.mate z) h2
      rwa [hrA.1.1, hκ.1.1] at this
  calc ((MoleProp.deletedLabels M Y '' A).ncard : ℕ∞)
      ≤ (((fun k => MoleProp.deletedLabels M Y (refk k)) '' (K1 : Set _)).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_le_ncard himg ((K1.finite_toSet).image _)
    _ ≤ (K1.card : ℕ∞) := by
        have h := (Set.ncard_image_le (f := fun k => MoleProp.deletedLabels M Y (refk k)) K1.finite_toSet).trans
          (le_of_eq (Set.ncard_coe_finset K1))
        exact Nat.cast_le.mpr h
    _ ≤ (⌊B⌋₊ : ℕ∞) := by exact_mod_cast hK1nat

end WaveTurbulence.FinalCountG8
