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

end WaveTurbulence.GammaLow.FinalCount.Step1
