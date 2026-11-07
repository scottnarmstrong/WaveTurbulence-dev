/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.CycleA
public import WaveTurbulence.Foundations.FinalCount.Arith96
import Mathlib.Tactic

/-! # Prop 9.6, cycles (DH23 L1854-L1862): double bond, triangle, `s`-cycle -/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section aux
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cls_cases {c : Cls} (h : ¬ c.IsEps) : c.IsAlpha ∨ c.IsBeta := by
  cases c <;> simp_all [Cls.IsEps, Cls.IsAlpha, Cls.IsBeta]

open Classical in
theorem card_alpha_add_beta (M : Molecule V D) (cls : V → Cls) (h : ∀ a ∈ M.atoms, ¬ (cls a).IsEps) :
    (alphaAtoms M.atoms cls).card + (betaAtoms M.atoms cls).card = M.atoms.card := by
  have hdisj : Disjoint (alphaAtoms M.atoms cls) (betaAtoms M.atoms cls) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (mem_filter.mp ha).2
    have h2 := (mem_filter.mp hb).2
    cases hc : cls a <;> simp_all [Cls.IsAlpha, Cls.IsBeta]
  have hU : alphaAtoms M.atoms cls ∪ betaAtoms M.atoms cls = M.atoms := by
    ext a
    unfold alphaAtoms betaAtoms
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    · intro ha
      rcases cls_cases (h a ha) with h1 | h1
      · exact Or.inl ⟨ha, h1⟩
      · exact Or.inr ⟨ha, h1⟩
  rw [← card_union_of_disjoint hdisj, hU]

theorem maxLadders_empty_of_deg_le_two (M : Molecule V D) (h : ∀ a ∈ M.atoms, M.deg a ≤ 2) :
    M.maximalLadders = ∅ := by
  classical
  refine eq_empty_of_forall_notMem fun S hS => ?_
  obtain ⟨hS1, hS2, _⟩ := (mem_filter.mp hS)
  obtain ⟨m, u, w, hL, rfl⟩ := hS2
  obtain ⟨hm, hinj, hat, hdbl, hrail⟩ := hL
  let j : Fin m := ⟨0, by omega⟩
  have h0 := hrail j
  have hne1 : u j.castSucc ≠ w j.castSucc := fun e => by
    have := hinj (a₁ := Sum.inl j.castSucc) (a₂ := Sum.inr j.castSucc) (by simpa using e); simp at this
  have hne2 : u j.castSucc ≠ u j.succ := fun e => by
    have := hinj (a₁ := Sum.inl j.castSucc) (a₂ := Sum.inl j.succ) (by simpa using e)
    exact (Fin.castSucc_lt_succ (i := j)).ne (by simpa using this)
  have hne3 : w j.castSucc ≠ u j.succ := fun e => by
    have := hinj (a₁ := Sum.inr j.castSucc) (a₂ := Sum.inl j.succ) (by simpa using e)
    simp at this
  have := three_le_deg_of_double M hne1 hne2 hne3 (ge_of_eq (hdbl j.castSucc)) (by
    have := h0.1; omega)
  have := h (u j.castSucc) (hat j.castSucc).1
  omega

theorem rho_le_card_of_deg_le_two (M : Molecule V D) (h : ∀ a ∈ M.atoms, M.deg a ≤ 2) :
    M.rho ≤ M.atoms.card := by
  classical
  unfold Molecule.rho Molecule.numLadders Molecule.numFree
  rw [maxLadders_empty_of_deg_le_two M h]
  rw [Finset.card_empty, zero_add]
  exact card_filter_le _ _

theorem exists_two_darts (M : Molecule V D) {a : V} (h : M.deg a = 2) :
    ∃ x y, M.atom x = a ∧ M.atom y = a ∧ x ≠ y := by
  classical
  unfold Molecule.deg at h
  obtain ⟨x, y, hxy, hs⟩ := card_eq_two.mp h
  refine ⟨x, y, ?_, ?_, hxy⟩
  · have : x ∈ M.dartsAt a := by rw [hs]; simp
    simpa [Molecule.dartsAt] using this
  · have : y ∈ M.dartsAt a := by rw [hs]; simp
    simpa [Molecule.dartsAt] using this

end aux


/-- The slab-count arithmetic: `n L^{-(d-γ)} b ≤ 3^d (d δ⁻¹ ρ⁻¹ L^{-γ} + L^{γ-1})` for `0 ≤ b ≤ 1`. -/
theorem slab_real {d : ℕ} (hd : 0 < d) {L γ δ ρ b n : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hρ : 0 < ρ) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hn0 : 0 ≤ n) (hn : n ≤ (2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1)) :
    n * (L ^ (-((d : ℝ) - γ)) * b) ≤ 3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) := by
  have hLp : 0 < L := by linarith
  have h3 : (2 * L + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * L ^ (d - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hpow : L ^ (d - 1) * L ^ (-((d : ℝ) - γ)) = L ^ (γ - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLp]
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; congr 1; ring
  have hpow2 : L ^ (γ - 1) * (L ^ (-2 * γ) * L) = L ^ (-γ) := by
    rw [← Real.rpow_add_one hLp.ne', ← Real.rpow_add hLp]
    congr 1; ring
  have hKnn : 0 ≤ (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1 := by positivity
  have h3d : (3 : ℝ) ^ (d - 1) ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hA0 : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hLp.le _
  calc n * (L ^ (-((d : ℝ) - γ)) * b) ≤ n * (L ^ (-((d : ℝ) - γ)) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hA0) hn0
    _ ≤ ((3 ^ (d - 1) * L ^ (d - 1)) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1)) * (L ^ (-((d : ℝ) - γ)) * 1) := by
        have h4 : n ≤ (3 ^ (d - 1) * L ^ (d - 1)) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1) :=
          hn.trans (mul_le_mul_of_nonneg_right h3 hKnn)
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 3 ^ (d - 1) * ((d : ℝ) * δ⁻¹ * ρ⁻¹ * (L ^ (γ - 1) * (L ^ (-2 * γ) * L)) + L ^ (γ - 1)) := by
        rw [← hpow]; field_simp
    _ ≤ _ := by
        rw [hpow2]
        have : 0 ≤ (d : ℝ) * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1) := by positivity
        exact mul_le_mul_of_nonneg_right h3d this


theorem cycle_countA_le {d : ℕ} (hd : 0 < d) {L γ δ C1 ρ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hρ : 0 < ρ) {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hne : M.atoms.Nonempty) (hch : ∀ b ∈ M.atoms, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ M.atoms ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1))) := by
  classical
  have hLp : 0 < L := by linarith
  have hdeg : ∀ a ∈ M.atoms, M.deg a = 2 := fun a ha => by
    have := Mole.outdeg_add_indeg M a; have := hch a ha; omega
  have hM : M.IsMolecule := by
    refine ⟨fun a ha => by have := hch a ha; omega, fun v hv => ⟨v, hv, Relation.EqvGen.refl _, by
      have := hdeg v hv; omega⟩⟩
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (MoleProp.GapScale L) hMA).trans ?_
  refine (cycle_A hL hδ hC1 hρ M hne hch hconn _ _ (fun κ hκ => hAdm κ hκ.1)).trans ?_
  have hb0 : 0 ≤ C1⁻¹ * δ ^ (1 / 2 : ℝ) := by have := hδ.1; positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hC : 0 < C1 := by linarith
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by have := hδ.1; positivity) zero_le_one
      _ = 1 := one_mul 1
  set B := min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1)) with hB
  have hB0 : 0 ≤ B := le_min (by positivity) (by have := hδ.1; positivity)
  have hfl : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le hB0
  rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact slab_real hd hL hδ.1 hρ hb0 hb1 (Nat.cast_nonneg _) (hfl.trans (min_le_right _ _))

end WaveTurbulence.FinalCountG8
