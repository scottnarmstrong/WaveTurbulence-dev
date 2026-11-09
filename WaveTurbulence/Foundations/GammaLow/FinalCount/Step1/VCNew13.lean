/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew12
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCNew13`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 35 (session 4): **`prop94_vine_newcomp`** -- TARGET Prop `excessprop1` (2), (excesseqn2+), with the
right-hand side written literally (T L2158--L2161). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {d : ℕ}

/-- **TARGET `excessprop1` (2)** (L2154, L2158--L2177): an Operation 1 that creates a new connected component removes a
single vine (an ordinary VC, or a hyper object whose adjoint is a single vine), with `ΔF = 1`, `ΔV_β = 2` and no new
`α`-atom; then `𝔍 ≲ L^{γ₀-η³} · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}` (the empty product over `α`-atoms).  a chart (`Charted`; main: `VINEPARAM`) is the only vine hypothesis;
the other premises are source facts: the fixed-set fact `NewCompFixed` (L2174), the ladder-gap clause of `Adm`
(`SourceLadderGaps`, L1692) and the heredity of `P`. -/
theorem prop94_vine_newcomp (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → SingleVineVC K →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents + 1 → NewCompFixed M K L γ δ ν w Adm →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) *
            excessRHS2 L γ η [] 1 2)) := by
  obtain ⟨Cs, C₂, hCs, hC₂, h⟩ := prop94_vine_newcomp_all hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V D _ _ _ M K hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF hfix => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) (hL₀.trans hL)
  rw [excessRHS2_eq L γ η [] 1 2 hL0]
  exact hh L hL C₁ η ν hC₁ hη hη1 hν M K hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF hfix

end WaveTurbulence.GammaLow.FinalCount.Step1
