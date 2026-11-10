/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCStmt`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 23: Prop 9.4, Step 1, single vine (DH23 L1797--L1801), of a charted vine (main: from `VINEPARAM`). -/
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
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas
variable {d : ℕ}

section Bonds
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut g M)
  (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
include hB

/-- The bonds of the removed vine are the internal bonds of the block. -/
theorem vc_bonds_card : K.vc.bonds.card = (internalBondSet M K.C.atoms).card := by
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have ho : K.vc.out x = true := (Finset.mem_filter.mp hx).2
    unfold internalBondSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, (vc_dart_iff K hB x.1).mp x.2⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro y hy
    unfold internalBondSet at hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y, (vc_dart_iff K hB y).mpr hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy1).2⟩, rfl⟩

end Bonds

section Single
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **Prop 9.4, Step 1, a single vine, given the re-scoped count `𝔉`** -- `prop94_vine_single'` (R17):
the same statement as `FinalCount.prop94_vine_single` with `VineCountInput'` and `C₂ ≤ C₁`. -/
theorem prop94_vine_single' (K : VineCut g M) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ C₂ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂) (hle : C₂ ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 2 ≤ K.C.atoms.card)
    (R : ℝ) (hR0 : 0 ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountInput' K L γ δ ρ Cf C₂ w Adm P e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1))) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) :=
  vine_excess_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL hδ hC hC₂ hle hP0 hP1 hP2 hη hη1 hηγ hF hB hm
    R hR0 hRu κ ρ (hρ.imp id (fun h => ⟨h.1, h.2.1⟩)) Cf hCf e hcount

end Single

end WaveTurbulence.GammaLow.FinalCount.Step1
