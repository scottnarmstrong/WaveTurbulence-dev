/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RestInv
/-! # Finite support and size of the non-ladder amplitude (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_ball_decorations (G : Garden w) (hp : G.IsPlain)
    {L : ℝ} (hL : 0 < L) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (center : GardenDart G → Mom d) :
    {z : GenDecoration G d roots 0 |
      ∀ x, ‖base + latticePoint L (bondIndex G z.1 x) - center x‖ ≤ 1}.Finite := by
  have hfin := Set.Finite.pi' (fun x : GardenDart G => finite_coset_unit_ball hL base (center x))
  exact Set.Finite.preimage (bondIndex_injective G hp roots).injOn hfin

theorem finite_momAmp_support (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    {z : GenDecoration G d roots 0 | splicedMomentumAmplitude G D L γ η base z.1 ≠ 0}.Finite := by
  apply (finite_ball_decorations G hp hL base roots D.center).subset
  intro z hz x
  have hballs := (splicedMomentumAmplitude_support G D hD L γ η base z.1 hz).2.2
  have hdec := spliced_molecule_decoration G hp hL.ne' base roots z
  by_cases hx : G.molecule.out x = true
  · exact hballs x (by simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx)
  · have hx' : G.molecule.out x = false := Bool.eq_false_iff.mpr hx
    have hm : G.molecule.mate x ∈ G.molecule.bonds := by
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and, G.molecule.out_mate, hx',
        Bool.not_false]
    have hh := hballs (G.molecule.mate x) hm
    simpa only [hdec.1 x, hD.1 x] using hh

lemma norm_edge_prod_le_one (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (s : Finset (GardenDart G)) (hs : s ⊆ G.molecule.bonds) (L : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) :
    ‖∏ x ∈ s, D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))‖ ≤ 1 := by
  rw [norm_prod]
  apply prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro x hx
  have hh := WaveTurbulence.Induct.SNorm_pointwise (D.edgeAmplitude x) 1 zero_le_one (by simpa using (hD.2.1 x (hs hx)).1)
    (base + latticePoint L (bondIndex G z x))
  simpa only [pow_zero, one_mul] using hh

lemma norm_outer_le_one (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (S : Finset (GBranch G.tree)) (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    ‖outerLadderMomentumAmplitude G D S L γ η base z‖ ≤ 1 := by
  unfold outerLadderMomentumAmplitude
  have h1 : ‖(((∏ v ∈ (univ.filter fun v => v ∉ D.hinges) \ S,
      epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro v _
    unfold epsCoef
    split_ifs <;> norm_num
  have h2 : ‖(((∏ v ∈ univ \ S, splicedVertexGapFactor G D L γ η base z v) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_prod]
    apply prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro v _
    unfold splicedVertexGapFactor
    cases D.gapSpecification v <;> simp only
    · norm_num
    · split_ifs <;> norm_num
  have h3 := norm_edge_prod_le_one D hD (G.molecule.bonds \ (G.molecule.bonds.filter (G.molecule.InGroup S)))
    (Finset.sdiff_subset) L base z
  have h4 := hD.2.2.1 (fun x : HingeDarts G D.hinges => base + latticePoint L (bondIndex G z x.1))
  simp only [Complex.ofReal_prod] at h1 h2
  rw [norm_mul, norm_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) h1).trans h2)).trans h3)).trans h4

omit [DecidableEq ι] in
lemma norm_restAmp_le_one (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (S : ι → Finset (GBranch G.tree)) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ‖restAmp D S L γ η base z‖ ≤ 1 := by
  unfold restAmp
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_outer_le_one D hD (Uni S) L γ η base z)).trans
    (norm_edge_prod_le_one D hD _ (fun x hx => (mem_filter.mp hx).1) L base z)

end WaveTurbulence.CoarseSpliced
