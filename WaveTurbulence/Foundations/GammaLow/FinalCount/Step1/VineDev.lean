/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VineDev`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 Vine removal, part 4 (FINALCOUNT-G2): the generic deviation of removing a VC (DH23 (fbyg), L1797--L1799):
`𝔄(M) ≤ 𝔉 · rankFactor(χ(M) - χ(post)) · (log L)^8 · ∏_{ladders ⊂ VC} 𝔛^z · 𝔄(post)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace VineCut
open WaveTurbulence.FinalCount.VineCut
variable {M : Molecule V D} (K : VineCut g M)

/-- The removed vine component. -/
def vc : Molecule V (PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms))) :=
  restrictP K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) K.closed.neg

theorem deg_m1 (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) : ∀ a ∈ K.m1.atoms, K.m1.deg a ≤ 4 :=
  cut_deg_le_four M K.cut_a (hM _ K.a_atom) hM

/-- **The generic vine deviation.** -/
theorem vine_isDeviation (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (N : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ N) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (K.post.countA L γ δ C₁ w Adm' P)
      ((N : ℝ≥0∞) * ENNReal.ofReal
        (rankFactor d L γ δ C₁ (M.circuitRank - K.post.circuitRank) * Real.log L ^ 8 *
          ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  rw [countA_eq, countA_eq]
  have hE := K.countE_le_vine hM L γ δ w Adm Adm' hAdm' N hN
  have hX1 : ∀ S, 1 ≤ Molecule.ladderWeight L γ δ (P S) := fun S => ladderWeight_ge_one L γ δ (P S) hL hδ.le (hP0 S)
  have hXK : ∀ S, Molecule.ladderWeight L γ δ (P S) ≤ Real.log L ^ 2 := fun S => ladderWeight_le L γ δ (P S)
  have hl1 := ladderProd_le M K.cut_a (hM _ K.a_atom) hM (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    hX1 hXK (fun S' hS' S hS hsub => by simp only [hP1 S' hS' S hS hsub])
  have hl2 := ladderProd_le K.m1 K.cut_b (K.deg_m1 hM _ (by
      show K.C.lower ∈ insert K.fa M.atoms; exact Finset.mem_insert_of_mem K.b_atom)) (K.deg_m1 hM)
    (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    hX1 hXK (fun S' hS' S hS hsub => by simp only [hP2 S' hS' S hS hsub])
  have hK2 : 0 ≤ (Real.log L ^ 2) ^ 2 := by positivity
  have h3 := ladderProd_restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed
    (fun S => Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
  change ∏ S ∈ K.cutMol.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S =
    (∏ S ∈ K.post.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) *
      ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S at h3
  have hΛ : 0 ≤ ∏ S ∈ K.post.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => pow_nonneg (zero_le_one.trans (hX1 S)) _
  have hΛv : 0 ≤ ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => pow_nonneg (zero_le_one.trans (hX1 S)) _
  have hlad : ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
      Real.log L ^ 8 * ((∏ S ∈ K.post.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) *
        ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := by
    calc _ ≤ (Real.log L ^ 2) ^ 2 * ∏ S ∈ K.m1.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S := hl1
      _ ≤ (Real.log L ^ 2) ^ 2 * ((Real.log L ^ 2) ^ 2 * ∏ S ∈ K.cutMol.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :=
          mul_le_mul_of_nonneg_left hl2 hK2
      _ = _ := by rw [h3]; ring
  have hrf : rankFactor d L γ δ C₁ M.circuitRank =
      rankFactor d L γ δ C₁ K.post.circuitRank * rankFactor d L γ δ C₁ (M.circuitRank - K.post.circuitRank) := by
    rw [← rankFactor_add d hL0 hδ (zero_lt_one.trans_le hC).ne']; congr 1; ring
  have hr1 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (zero_le_one.trans hC) K.post.circuitRank
  have hr2 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (zero_le_one.trans hC) (M.circuitRank - K.post.circuitRank)
  have hP1' : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hc : 0 ≤ rankFactor d L γ δ C₁ (M.circuitRank - K.post.circuitRank) * Real.log L ^ 8 *
      ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S := by positivity
  have := countA_dev_of_parts _ _
    (rankFactor d L γ δ C₁ M.circuitRank *
      ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
    (rankFactor d L γ δ C₁ K.post.circuitRank *
      ∏ S ∈ K.post.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)
    (N : ℕ∞) _ hc hE (by
      rw [hrf]
      calc _ ≤ rankFactor d L γ δ C₁ K.post.circuitRank * rankFactor d L γ δ C₁ (M.circuitRank - K.post.circuitRank) *
            (Real.log L ^ 8 * ((∏ S ∈ K.post.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) *
              ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S)) :=
            mul_le_mul_of_nonneg_left hlad (mul_nonneg hr1 hr2)
        _ = _ := by ring)
  simpa [ENat.toENNReal_coe] using this

end VineCut
end WaveTurbulence.GammaLow.FinalCount.Step1
