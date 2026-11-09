/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproStep1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproVcShape`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-DISJ goal 3: a vc-shaped object excludes the `eraseBond` disjunct of `step1_vc_shape`

An ordinary (VC-shaped) object `P` is a block of the molecule `M`, so its joints have `M`-internal degree 2. If `P.atoms` were a
double chain or a type-V vine of the adjoint molecule `eraseBond M e` with `e` a bond joining the joints, the joint would have
`M`-internal degree `>= 3`.


**Low-range change (L6-HDS).** TARGET `subsetvc`′ (N3 Cor 1.16′(2)): the alternative "vine (V)" (ordinary, or the adjoint
of a joint-to-joint bond) is a T-vine (`subsetvc_classification`, restated).
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **S4-DISJ goal 3.** For an object of ordinary (VC) shape the `eraseBond` disjunct of `step1_vc_shape` is impossible:
the SG object outside `C_1` and hinge-free is a T-vine, or one or two double bonds, in `M` itself. -/
theorem step1_vc_shape' {w d : ℕ} (G : Garden w) (C : Src.SubproChoices Src.γL G) (L γ η : ℝ) (base : Mom d)
    (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ))
    (hs : SubproSupportA G C L γ η base kFix κ)
    (c : GBranch G.tree → Mom d) (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (P : Src.Object Src.γL G.molecule) (hP : P.HasGapKind L γ η base κ .SG)
    (hout : ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) (hdis : Disjoint P.atoms C.hinges)
    (hvc : ∃ h, P.shape = Src.VineLikeObject.vc h) :
    Vine.DoubleChain G.molecule P.atoms P.upper P.lower 1 ∨ Vine.DoubleChain G.molecule P.atoms P.upper P.lower 2 ∨
      G.molecule.IsTVine P.atoms P.upper P.lower := by
  rcases step1_vc_shape G C L γ η base kFix κ hs c hκ hc P hP hout hdis hvc with h | h | h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have hB := object_vc_block P hvc
    have hlt := eraseBond_degIn_lt_two_of_block hB he
    rcases h with h | h
    · exact absurd (doubleChain_two_le_degIn h) (by omega)
    · exact absurd (Mole.block_joint_degrees _ h.1).1 (by omega)

end WaveTurbulence.GammaLow.FinalCount.H
