/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EraseNorm
import Mathlib.Tactic

/-! # `𝔄(M)` from a label count for the removal of a pair of atoms

If `𝔈(M; Adm) ≤ n · 𝔈(M ∖ {a,b}; erased Adm)` and `χ(M) = χ(M ∖ {a,b}) + r` with both connected, then
`𝔄(M; Adm) ≤ n · L^{-(d-γ) r} (C₁⁻¹ δ^{1/2})^r (log L)^8 · 𝔄*(M ∖ {a,b})`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The erasure of a pair is nonempty when a bond leaves the pair. -/
theorem erase_pair_nonempty (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b : V}
    (hab : a ≠ b) (h : 2 * M.bondsBetween a b < M.deg a + M.deg b) :
    (Degen.eraseAtoms M {a, b}).atoms.Nonempty := by
  classical
  have h1 := card_cross_pair M hloop hab
  obtain ⟨z, hz⟩ : (crossDarts M {a, b}).Nonempty := card_pos.mp (by omega)
  obtain ⟨_, h2⟩ := mem_crossDarts.mp hz
  exact ⟨M.atom (M.mate z), mem_sdiff.mpr ⟨M.atom_mem _, h2⟩⟩

theorem countAFree_le_erase_pair (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4) {a b : V} (hab : a ≠ b) (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    (hconnM : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hconnP : ∀ u ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ v ∈ (Degen.eraseAtoms M {a, b}).atoms,
      (Degen.eraseAtoms M {a, b}).SameComponent u v)
    (hne : (Degen.eraseAtoms M {a, b}).atoms.Nonempty) {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hδ : 0 < δ) (hC1 : 0 < C1) (P : Finset V → ℝ)
    (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm M L γ η P κ) (n : ℕ) {r : ℕ}
    (hr : ((M.deg a + M.deg b - M.bondsBetween a b : ℤ) - 2) = r)
    (hcount : MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤ (n : ℕ∞) *
      MoleProp.countEFree (Degen.eraseAtoms M {a, b}) L γ δ (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility M {a, b} Adm)) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal ((n : ℝ) * (L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r) *
        (Real.log L ^ 2) ^ 4) * AFreeSup (Degen.eraseAtoms M {a, b}) d L γ δ η C1 := by
  classical
  have hLp : 0 < L := by linarith
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  set Q := Degen.eraseAtoms M {a, b}
  have hPQ : ∀ S ∈ MoleProp.ladderCells Q, 0 ≤ P S := fun S hS => hP S (by
    have h := (MoleProp.isLadderCell_erase_iff M {a, b} S).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M h.1), h.1⟩)
  have hrank := circuitRank_erase_pair M hloop hab ha hb hconnM hconnP hne
  rw [hr] at hrank
  have hbne : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hcells := cellProduct_le_erase M hloop hdeg {a, b} (L := L) (γ := γ) (δ := δ) hLp.le hδ.le hlog P hP
  rw [card_pair hab] at hcells
  have np := MoleProp.freeNormalization_pos Q (d := d) (γ := γ) hLp hδ hC1 hlog0 P hPQ
  -- the normalization of `M` against that of `Q`
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      (L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r *
        (Real.log L ^ 2) ^ 4) * MoleProp.freeNormalization Q (d := d) L γ δ C1 P := by
    unfold MoleProp.freeNormalization
    have hrk : M.circuitRank = Q.circuitRank + (r : ℤ) := hrank
    have hsplit := norm_split (L := L) (a := (d : ℝ) - γ) hLp hbne hrk (MoleProp.cellProduct Q L γ δ P * 1)
      (MoleProp.cellProduct Q L γ δ P) 1 (by ring)
    have hAN : 0 ≤ L ^ (-((d : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank := by
      positivity
    calc L ^ (-((d : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          MoleProp.cellProduct M L γ δ P
        ≤ L ^ (-((d : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          (MoleProp.cellProduct Q L γ δ P * (Real.log L ^ 2) ^ 4) := mul_le_mul_of_nonneg_left hcells hAN
      _ = (L ^ (-((d : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          (MoleProp.cellProduct Q L γ δ P * 1)) * (Real.log L ^ 2) ^ 4 := by ring
      _ = _ := by rw [hsplit]; simp only [mul_one, Int.cast_natCast, zpow_natCast]; ring
  have hmonoP : MoleProp.countEFree Q L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility M {a, b} Adm) ≤
      MoleProp.countEFree Q L γ δ (0 : Mom d) (lgAdm Q L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, h0, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase M L γ η 0 _ (hAdm κ0 h0).1,
        MoleProp.cellGapRestriction_erase M L 0 _ P _ (hAdm κ0 h0).2⟩
  have h1 := afree_le_afreeSup Q (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) P hPQ
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
      ≤ (((n : ℕ∞) * MoleProp.countEFree Q L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility M {a, b} Adm) : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r *
          (Real.log L ^ 2) ^ 4) * MoleProp.freeNormalization Q (d := d) L γ δ C1 P) :=
        mul_le_mul' (ENat.toENNReal_mono hcount) (ENNReal.ofReal_le_ofReal hnorm)
    _ = ENNReal.ofReal ((n : ℝ) * (L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r) *
          (Real.log L ^ 2) ^ 4) *
        ((MoleProp.countEFree Q L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility M {a, b} Adm) : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization Q (d := d) L γ δ C1 P)) := by
        rw [ENat.toENNReal_mul, ENat.toENNReal_coe, ENNReal.ofReal_mul (by positivity)]
        rw [show ((n : ℝ) * (L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r) *
          (Real.log L ^ 2) ^ 4) = (n : ℝ) * (L ^ (-((d : ℝ) - γ) * (r : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ r *
          (Real.log L ^ 2) ^ 4) by ring, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (le_trans ?_ h1)
        unfold AFree
        rw [MoleProp.countAFree_eq_normalization]
        exact mul_le_mul' (ENat.toENNReal_mono hmonoP) le_rfl

end WaveTurbulence.FinalCountG8
