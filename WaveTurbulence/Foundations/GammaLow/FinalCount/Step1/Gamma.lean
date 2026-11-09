/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Chart
/-! # Step 1 / Operation 1 for the objects of `𝒱_γ` (L6-STEP1, PLAN-L6 row G)

DH23 Prop 9.4 Step 1 (L1797--L1802) and TARGET `excessprop1` (2) (L2154--L2177) when the removed vine-like object is an
object of the `γ`-dependent family `𝒱_γ` (ruling D11; L6's carrier `Src.Object γ M`):

* `prop94_vine_all_gamma`: the removed VC is a single vine of `𝒱_γ` (a block vine: (I), (II) or a T-vine for
  `γ ≤ 1/2`; or the adjoint of an HV of such a vine) or two double bonds (a block or hyper VC:I+I), with the new
  `α`-atoms labelled `Rg ∈ [L⁻¹, L^{-γ+η}]`, `κ ∈ {0, 50}`: the deviation is `≲ L^{-η³} ∏ L^{(γ+3η)/2-κη} Rg`
  (excesseqn2; N1 §3.2, N2 §2.1, M2 §3.5 (i)–(iii));
* `prop94_vine_newcomp_gamma`: an Operation 1 that creates a new component (`ΔF = 1`, `ΔV_β = 2`, no new `α`-atom):
  `𝔍 ≲ L^{γ₀-η³} · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}` (excesseqn2+; N2 §2.1, M2 §3.5 (iv)).

The only vine hypothesis is L4's Theorem C for T-vines (`TVine.Chart.TVineChartExists`, M4 §3.2: the piece chart; L4
derives it from the piece-shape theorem N2 Prop 1.17(b), L6 `NamedInputs.TVinePiecesInput`). The bad and drawn vines
use main's sealed charts. All other premises are main's source premises, verbatim. Both bounds hold for every
`γ ∈ (0, 1)`; at `γ ≤ 1/2` the T-vine core is counted by A.2(3) (gain `L^{-γ₀}`, `γ₀ = γ`), each 2-atom piece by A.2(1),
the joints by `L^d (ρL)^d`. -/
@[expose] public section
set_option autoImplicit false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount

variable {d : ℕ}

/-- **The removed VC of `K` is a single vine of `𝒱_g`** (main's `VineCount.SingleVineVC` with the family `𝒱_g`): of `M`
for an ordinary VC, of the adjoint `eraseBond M R.added` for a hyper object (an HV; DH23 L1797, first alternative of
`Prop subsetvc`). -/
def SingleVineVCGamma {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : VineCut g M) : Prop :=
  match K.C.shape with
  | .vc _ => Src.IsSomeVine g M K.C.atoms K.C.upper K.C.lower
  | .hyper R => Src.IsSomeVine g (Molecule.eraseBond M R.added) K.C.atoms K.C.upper K.C.lower

/-- A single vine of `𝒱_g` is a charted single vine (given Theorem C). -/
theorem singleVineVC_of_gamma (hT : TVine.Chart.TVineChartExists) {g : ℝ} {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (hMol : M.IsMolecule) (K : VineCut g M) (h : SingleVineVCGamma K) :
    SingleVineVC K := by
  unfold SingleVineVCGamma at h
  unfold SingleVineVC
  rcases hsh : K.C.shape with hv | R
  · rw [hsh] at h
    exact charted_of_isSomeVine hT hMol h
  · rw [hsh] at h
    exact charted_of_isSomeVine hT (Vine.eraseBond_isMolecule M hMol _ (added_nonloop K R hsh)) h

/-- **DH23 Prop 9.4, Step 1, for every `𝒱_γ` vine-like object removed by `Stage2Op.vine K`** (L1773--L1802; N1 §3.2,
N2 §2.1, M2 §3.5 (i)–(iii)): a single vine of `𝒱_γ` (an ordinary VC, or the adjoint of an HV) or two double bonds
(VC:I+I, block or hyper), with the new `α`-atoms labelled `Rg ∈ [L⁻¹, L^{-γ+η}]`, `κ ∈ {0, 50}`. Vine hypothesis: L4's
Theorem C only. The other premises are main's `prop94_vine_all`, verbatim: the classification of `Prop subsetvc`
(`hcls`; for `𝒱_γ` it is N3 Cor 1.16′), `ΔF = 0` (L1798), the gap `|r| ∼ Rg` (L1800), `ι` (L1782, L1801), the heredity
of `P` along maximal ladders and the ladder-gap clause of `Adm` (`SourceLadderGaps`, L1692). -/
theorem prop94_vine_all_gamma (hT : TVine.Chart.TVineChartExists) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (SingleVineVCGamma K ∨ Nonempty (DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * Rg) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * Rg ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        (κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, h⟩ := prop94_vine_all (g := γ) hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ V D _ _ _ M K hMol hM hcls => ?_⟩
  exact hh L hL C₁ η hC₁ hη hη1 hηγ M K hMol hM (hcls.imp_left (singleVineVC_of_gamma hT hMol K))

/-- **TARGET `excessprop1` (2) for `𝒱_γ`** (L2154, L2158--L2177; N2 §2.1, M2 §3.5 (iv)): an Operation 1 that creates a
new connected component removes a single vine of `𝒱_γ` (an ordinary VC, or the adjoint of an HV), with `ΔF = 1`,
`ΔV_β = 2` and no new `α`-atom; then `𝔍 ≲ L^{γ₀-η³} · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}`. Vine hypothesis: L4's Theorem C
only; the other premises are main's `prop94_vine_newcomp`, verbatim (the fixed-set fact `NewCompFixed`, L2174). -/
theorem prop94_vine_newcomp_gamma (hT : TVine.Chart.TVineChartExists) (hd : 3 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → SingleVineVCGamma K →
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
  obtain ⟨Cs, C₂, hCs, hC₂, h⟩ := prop94_vine_newcomp (g := γ) hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V D _ _ _ M K hMol hM hs => ?_⟩
  exact hh L hL C₁ η ν hC₁ hη hη1 hν M K hMol hM (singleVineVC_of_gamma hT hMol K hs)

end WaveTurbulence.GammaLow.FinalCount.Step1
