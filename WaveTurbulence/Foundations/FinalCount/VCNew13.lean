/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew12
/-! # VINE-COUNT part 35 (session 4): **`prop94_vine_newcomp`** -- TARGET Prop `excessprop1` (2), (excesseqn2+), with the
right-hand side written literally (T L2158--L2161). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {d : ℕ}

/-- **The right-hand side of (excesseqn2+)** (TARGET L2158--L2161):
`L^{γ₀-η³} · ∏^{(α)}_v L^{(γ+3η)/2-κ_vη} Q_v · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}`, `γ₀ = min(γ, 1-γ)`, the product over the newly
created `α`-atoms (labels `(Q_v, κ_v)`). It differs from `excessRHS` (T L2157, (excesseqn2)) only by the factor `L^{γ₀}`. -/
noncomputable def excessRHS2 (L γ η : ℝ) (αs : List (ℝ × ℕ)) (ΔF ΔVβ : ℤ) : ℝ :=
  L ^ (min γ (1 - γ) - η ^ 3) * (αs.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod *
    L ^ ((2 * min γ (1 - γ) + 5 * η ^ 2) * (ΔF : ℝ) - (min γ (1 - γ) + 2 * η ^ 2) * (ΔVβ : ℝ))

theorem excessRHS2_eq (L γ η : ℝ) (αs : List (ℝ × ℕ)) (ΔF ΔVβ : ℤ) (hL : 0 < L) :
    excessRHS2 L γ η αs ΔF ΔVβ = L ^ (min γ (1 - γ)) * excessRHS L γ η αs ΔF ΔVβ := by
  unfold excessRHS2 excessRHS
  rw [sub_eq_add_neg, Real.rpow_add hL]
  ring

/-- **TARGET `excessprop1` (2)** (L2154, L2158--L2177): an Operation 1 that creates a new connected component removes a
single vine (an ordinary VC, or a hyper object whose adjoint is a single vine), with `ΔF = 1`, `ΔV_β = 2` and no new
`α`-atom; then `𝔍 ≲ L^{γ₀-η³} · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}` (the empty product over `α`-atoms).  `VINEPARAM` is the only vine hypothesis;
the other premises are source facts: the fixed-set fact `NewCompFixed` (L2174), the ladder-gap clause of `Adm`
(`SourceLadderGaps`, L1692) and the heredity of `P`. -/
theorem prop94_vine_newcomp (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
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
  obtain ⟨Cs, C₂, hCs, hC₂, h⟩ := prop94_vine_newcomp_all hvp hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V D _ _ _ M K hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF hfix => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) (hL₀.trans hL)
  rw [excessRHS2_eq L γ η [] 1 2 hL0]
  exact hh L hL C₁ η ν hC₁ hη hη1 hν M K hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF hfix

end WaveTurbulence.VineCount
