/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGShape`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level): the shape hypothesis `hsh` for the members of `C₂`** (census item (c)).

`c2_shape`: every member `U` of G3's `C₂` (any shape) has three atoms or is `ObjVine` (a single vine, in the adjoint of its own
designated bond if `U` is hyper).
* ordinary `U`: S4-DISJ `step1_vc_shape'` (one double bond = a type-I vine, two double bonds = three atoms, or a T-vine);
* hyper `U` with a DV host, or with an LG/ZG host containing it designation-wise: `subsetvc_classification`; its fourth disjunct
  (`∃ e`, an adjoint of some joint-to-joint bond `e` is a T-vine or a chain of two double bonds) gives three atoms, or `ObjVine`
  for `e = R.added`, for `e = mate R.added` (`eraseMateIso`), and for another bond `e` (`hyper_other_isSomeVine`);
* hyper `U` whose only LG/ZG host has the same atoms and another designation (the CORNER of S4-DISJ): `hyper_other_isSomeVine`
  directly. 

**Low-range change (L6-HDS).** The `subsetvc` alternative "vine (V)" is a T-vine (TARGET `subsetvc`′); a T-vine (or its
adjoint) is `ObjVine` (= `IsVineEnl`); the mate adjoint is transported by L6-HTV's `InducedIso.isVineT`.
-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Subpro

section generic
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

/-- A hyper object with a `subsetvc` classification has three atoms or is a single vine in its own adjoint. -/
theorem hyper_shape_of_cls {N : Molecule V D} (U : Src.Object Src.γL N) {R : Src.HyperLikeRealization Src.γL N U.atoms U.upper U.lower}
    (hR : U.shape = .hyper R)
    (h : Vine.DoubleChain N U.atoms U.upper U.lower 1 ∨ Vine.DoubleChain N U.atoms U.upper U.lower 2 ∨
      N.IsTVine U.atoms U.upper U.lower ∨
      ∃ e, N.ends e = s(U.upper, U.lower) ∧
        (Vine.DoubleChain (Mole.eraseBond N e) U.atoms U.upper U.lower 2 ∨
          (Mole.eraseBond N e).IsTVine U.atoms U.upper U.lower)) :
    U.atoms.card = 3 ∨ ObjVine N U := by
  have hdeg : N.degIn U.atoms U.upper = 3 := object_hyper_degIn U ⟨R, hR⟩ (Or.inl rfl)
  rcases h with h | h | h | ⟨e, he, h | h⟩
  · exfalso
    have := (Mole.block_joint_degrees N (doubleChain_one_isVineI h).1).1; omega
  · exact Or.inl (by have := Vine.doubleChain_card h; omega)
  · exfalso
    have := (Mole.block_joint_degrees N h.1).1; omega
  · exact Or.inl (by have := Vine.doubleChain_card h; omega)
  · right
    unfold ObjVine
    rw [hR]
    by_cases h1 : R.added = e
    · show (Molecule.eraseBond N R.added).IsVineEnl U.atoms U.upper U.lower
      rw [h1]; exact Or.inr (Or.inr h)
    by_cases h2 : R.added = N.mate e
    · show (Molecule.eraseBond N R.added).IsVineEnl U.atoms U.upper U.lower
      rw [h2]; exact Or.inr (Or.inr ((eraseMateIso N e U.atoms (objectAtoms_sub' U)).isVineT h))
    · let O : Src.Object Src.γL N := ⟨U.atoms, U.upper, U.lower, .hyper ⟨e, he, ⟨h.1, 1, Src.Chain.single (Src.isSomeVine_of_T h)⟩⟩⟩
      exact hyper_other_isSomeVine O U rfl (R := ⟨e, he, ⟨h.1, 1, Src.Chain.single (Src.isSomeVine_of_T h)⟩⟩) rfl hR
        (fun h' => h'.elim h1 h2)

/-- The corner: a hyper object contained atom-wise but not designation-wise in an object `Q` is `ObjVine` (the host is hyper with
the same atoms and another designated bond). -/
theorem objVine_of_not_contained {N : Molecule V D} (U Q : Src.Object Src.γL N) {R : Src.HyperLikeRealization Src.γL N U.atoms U.upper U.lower}
    (hR : U.shape = .hyper R) (hsub : U.atoms ⊆ Q.atoms) (hnc : ¬ U.IsContained Q) : ObjVine N U := by
  obtain ⟨SQ, qu, ql, shQ⟩ := Q
  cases shQ with
  | vc hQ =>
    exfalso; apply hnc
    unfold Src.Object.IsContained Src.VineLikeObject.IsContained
    rw [hR]
    exact hsub
  | hyper RQ =>
    have hc' : ¬ (U.atoms = SQ → R.added = RQ.added ∨ R.added = N.mate RQ.added) := by
      intro h; apply hnc
      unfold Src.Object.IsContained Src.VineLikeObject.IsContained
      rw [hR]
      exact ⟨hsub, h⟩
    push Not at hc'
    obtain ⟨hat, h1, h2⟩ := hc'
    unfold ObjVine
    rw [hR]
    exact hyper_other_isSomeVine ⟨SQ, qu, ql, .hyper RQ⟩ U hat.symm rfl hR (fun h => h.elim h1 h2)

end generic

section garden
variable {w d : ℕ} {G : Garden w}

/-- lg-spine-u's `Src.SubproSupport` (AMEND5, atom level) is S4's `SubproSupportA`. -/
theorem supportA_of_support {C : Src.SubproChoices Src.γL G} {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} (h : Src.SubproSupport Src.γL G C L γ η base kFix κ) : SubproSupportA G C L γ η base kFix κ :=
  ⟨h.selectedSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩

/-- **`hsh` for `C₂`**: every member of G3's `C₂` has three atoms or is a single vine (in its own adjoint if hyper). -/
theorem c2_shape (C : Src.SubproChoices Src.γL G) {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hs : Src.SubproSupport Src.γL G C L γ η base kFix κ)
    {Un : Set (Src.Object Src.γL G.molecule)} {U : Src.Object Src.γL G.molecule} (hU : U ∈ (collDataOf C).C2Of L γ η base κ Un) :
    U.atoms.card = 3 ∨ ObjVine G.molecule U := by
  have hM := Mole.garden_isMolecule G
  obtain ⟨⟨⟨hsg, hout, hdis, hhost⟩, -⟩, -⟩ := hU
  rcases object_shape_cases U with hvc | ⟨R, hR⟩
  · rcases step1_vc_shape' G C L γ η base kFix κ (supportA_of_support hs) c hκ hc U hsg hout hdis hvc with h | h | h
    · right
      obtain ⟨hh, hsh⟩ := hvc
      unfold ObjVine
      rw [hsh]
      exact Or.inl (doubleChain_one_isVineI h)
    · left; have := Vine.doubleChain_card h; omega
    · right
      obtain ⟨hh, hsh⟩ := hvc
      unfold ObjVine
      rw [hsh]
      exact Or.inr (Or.inr h)
  · obtain ⟨r', hr', hk'⟩ := hsg
    have hrP := (U.shape.toVine_isGap L base κ r').mpr hr'
    rcases hhost with ⟨S, a, b, hDV, hUS, -, -⟩ | ⟨Q, hUQ, hQk, -, -⟩
    · exact hyper_shape_of_cls U hR
        (subsetvc_classification G.molecule hM U.shape.toVine hUS L γ η base c κ hκ hc hrP hk' (Or.inl hDV))
    · obtain ⟨r, hr, hkr⟩ : ∃ r, Q.shape.IsGap L base κ r ∧
          (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG) := by
        rcases hQk with ⟨r, hr, hk⟩ | ⟨r, hr, hk⟩
        · exact ⟨r, hr, Or.inl hk⟩
        · exact ⟨r, hr, Or.inr hk⟩
      by_cases hcont : U.IsContained Q
      · exact hyper_shape_of_cls U hR
          (subsetvc_classification G.molecule hM U.shape.toVine hUQ L γ η base c κ hκ hc hrP hk'
            (Or.inr ⟨Q.shape.toVine, (U.shape.toVine_isContained Q.shape).mpr hcont,
              r, (Q.shape.toVine_isGap L base κ r).mpr hr, hkr⟩))
      · exact Or.inr (objVine_of_not_contained U Q hR hUQ hcont)

end garden

end WaveTurbulence.GammaLow.FinalCount.H
