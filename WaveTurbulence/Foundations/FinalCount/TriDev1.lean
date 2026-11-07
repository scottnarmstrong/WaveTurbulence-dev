/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriArith4
/-! Triangles, part 20 (FINALCOUNT-G2): the generic deviation of a triangle removal. From `𝔈(M) ≤ N 𝔈(kept)` the
deviation is `N · rankFactor(3 - ΔF) · (log L)^{12}`; the three cuts lose `(log L)^4` each (ladders), the removed
triangle `T` has `χ(T) = 1` and no ladders. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem cd2 : T.m1.IsCutData (T.t 1) (T.f 1) (T.a 1) (T.b 1) :=
  ⟨T.t_mem_m1 1, T.f_fresh_m1, T.m1_atom_tri _ 1 (Or.inl rfl), T.m1_atom_tri _ 1 (Or.inr rfl),
    T.b_ne_mate_a 1, T.out_a 1, T.out_b 1⟩

theorem cd3 : T.m2.IsCutData (T.t 2) (T.f 2) (T.a 2) (T.b 2) :=
  ⟨T.t_mem_m2 2, T.f_fresh_m2, T.m2_atom_tri _ 2 (Or.inl rfl), T.m2_atom_tri _ 2 (Or.inr rfl),
    T.b_ne_mate_a 2, T.out_a 2, T.out_b 2⟩

theorem deg_m1 (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) : ∀ a ∈ T.m1.atoms, T.m1.deg a ≤ 4 :=
  cut_deg_le_four M T.cd1 (hM _ (T.t_mem 0)) hM

theorem deg_m2 (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) : ∀ a ∈ T.m2.atoms, T.m2.deg a ≤ 4 :=
  cut_deg_le_four T.m1 T.cd2 (T.deg_m1 hM _ (T.t_mem_m1 1)) (T.deg_m1 hM)

theorem tcomp_ladders : T.tcomp.maximalLadders = ∅ := by
  ext S
  simp only [Finset.notMem_empty, iff_false]
  intro hS
  obtain ⟨m, u, w, hL, rfl⟩ := ((mem_maximalLadders_iff _).1 hS).1
  have h3 := ladder_deg_ge_three_u T.tcomp hL 0
  have hmem : u 0 ∈ T.tcomp.atoms :=
    ladderAtoms_subset_atoms T.tcomp hL ((mem_ladderAtoms u w _).2 ⟨0, Or.inl rfl⟩)
  rw [T.tcomp_atoms] at hmem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
  rw [← hj, T.tcomp_deg j] at h3
  omega

theorem circuitRank_kept :
    M.circuitRank = T.kept.circuitRank + (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) := by
  unfold Molecule.circuitRank
  have h1 := T.kept_bonds_card
  have h2 := T.kept_atoms_card
  have h1' : (T.kept.bonds.card : ℤ) + 3 = M.bonds.card := by exact_mod_cast h1
  have h2' : (T.kept.atoms.card : ℤ) = M.atoms.card := by exact_mod_cast h2
  linarith

theorem ladderProd_m3 (f : Finset V → ℝ) :
    ∏ S ∈ T.m3.maximalLadders, f S = ∏ S ∈ T.kept.maximalLadders, f S := by
  have := ladderProd_restrictP T.m3 T.TP T.pclosed f
  change ∏ S ∈ T.m3.maximalLadders, f S =
    (∏ S ∈ T.kept.maximalLadders, f S) * ∏ S ∈ T.tcomp.maximalLadders, f S at this
  rw [this, T.tcomp_ladders]; simp

/-- **The generic triangle deviation.** -/
theorem tri_isDeviation (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (N : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤ N) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      ((N : ℝ≥0∞) * ENNReal.ofReal
        (rankFactor d L γ δ C₁ (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) * Real.log L ^ 12)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  rw [countA_eq, countA_eq]
  have hE := T.countE_le_tri hM L γ δ w Adm Adm' hAdm' N hN
  have hX1 : ∀ S, 1 ≤ Molecule.ladderWeight L γ δ (P S) := fun S => ladderWeight_ge_one L γ δ (P S) hL hδ.le (hP0 S)
  have hXK : ∀ S, Molecule.ladderWeight L γ δ (P S) ≤ Real.log L ^ 2 := fun S => ladderWeight_le L γ δ (P S)
  have hl1 := ladderProd_le M T.cd1 (hM _ (T.t_mem 0)) hM (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    hX1 hXK (fun S' hS' S hS hsub => by simp only [hP1 S' hS' S hS hsub])
  have hl2 := ladderProd_le T.m1 T.cd2 (T.deg_m1 hM _ (T.t_mem_m1 1)) (T.deg_m1 hM)
    (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    hX1 hXK (fun S' hS' S hS hsub => by simp only [hP2 S' hS' S hS hsub])
  have hl3 := ladderProd_le T.m2 T.cd3 (T.deg_m2 hM _ (T.t_mem_m2 2)) (T.deg_m2 hM)
    (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    hX1 hXK (fun S' hS' S hS hsub => by simp only [hP3 S' hS' S hS hsub])
  have hK1 : 1 ≤ Real.log L ^ 2 := by
    have hP1' : 1 ≤ Real.log L := by
      have := Real.log_le_log (Real.exp_pos 1) hL
      rwa [Real.log_exp] at this
    nlinarith
  have hΛ : 0 ≤ ∏ S ∈ T.kept.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => pow_nonneg (zero_le_one.trans (hX1 S)) _
  have hlad : ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
      Real.log L ^ 12 * ∏ S ∈ T.kept.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S := by
    have h3 := T.ladderProd_m3 (fun S => Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
    have hK2 : 0 ≤ (Real.log L ^ 2) ^ 2 := by positivity
    calc _ ≤ (Real.log L ^ 2) ^ 2 * ∏ S ∈ T.m1.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S := hl1
      _ ≤ (Real.log L ^ 2) ^ 2 * ((Real.log L ^ 2) ^ 2 * ∏ S ∈ T.m2.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :=
          mul_le_mul_of_nonneg_left hl2 hK2
      _ ≤ (Real.log L ^ 2) ^ 2 * ((Real.log L ^ 2) ^ 2 * ((Real.log L ^ 2) ^ 2 * ∏ S ∈ T.m3.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl3 hK2) hK2
      _ = Real.log L ^ 12 * ∏ S ∈ T.kept.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S := by
          rw [h3]; ring
  have hrk := T.circuitRank_kept
  have hrf : rankFactor d L γ δ C₁ M.circuitRank =
      rankFactor d L γ δ C₁ T.kept.circuitRank *
        rankFactor d L γ δ C₁ (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) := by
    rw [← rankFactor_add d hL0 hδ (zero_lt_one.trans_le hC).ne', ← hrk]
  have hr1 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (zero_le_one.trans hC) T.kept.circuitRank
  have hr2 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (zero_le_one.trans hC)
    (3 - ((T.kept.numComponents : ℤ) - M.numComponents))
  have hc : 0 ≤ rankFactor d L γ δ C₁ (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) * Real.log L ^ 12 := by
    have : 0 ≤ Real.log L := by linarith [Real.log_nonneg hL1]
    positivity
  have := countA_dev_of_parts _ _
    (rankFactor d L γ δ C₁ M.circuitRank *
      ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
    (rankFactor d L γ δ C₁ T.kept.circuitRank *
      ∏ S ∈ T.kept.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
    (N : ℕ∞) _ hc hE (by
      rw [hrf]
      calc _ ≤ rankFactor d L γ δ C₁ T.kept.circuitRank * rankFactor d L γ δ C₁ (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) *
            (Real.log L ^ 12 * ∏ S ∈ T.kept.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :=
            mul_le_mul_of_nonneg_left hlad (mul_nonneg hr1 hr2)
        _ = _ := by ring)
  simpa [ENat.toENNReal_coe] using this

end TriData
end WaveTurbulence.FinalCount
