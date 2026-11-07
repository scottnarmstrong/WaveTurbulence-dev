/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGBase
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.FinalCount.SubproVcShape
/-! **FINALCOUNT-ASSEMBLY (garden level): the shape hypothesis `hsh` for the members of `C₂`** (census item (c)).

`c2_shape`: every member `U` of G3's `C₂` (any shape) has three atoms or is `ObjVine` (a single vine, in the adjoint of its own
designated bond if `U` is hyper).
* ordinary `U`: S4-DISJ `step1_vc_shape'` (one double bond = a type-I vine, two double bonds = three atoms, or a type-V vine);
* hyper `U` with a DV host, or with an LG/ZG host containing it designation-wise: `subsetvc_classification`; its fourth disjunct
  (`∃ e`, an adjoint of some joint-to-joint bond `e` is a type-V vine or a chain of two double bonds) gives three atoms, or `ObjVine`
  for `e = R.added`, for `e = mate R.added` (`eraseMateIso`), and for another bond `e` (`hyper_other_isSomeVine`);
* hyper `U` whose only LG/ZG host has the same atoms and another designation (the CORNER of S4-DISJ): `hyper_other_isSomeVine`
  directly. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Subpro

section generic
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem doubleChain_one_isVineI {N : Molecule V D} {S : Finset V} {a b : V} (h : Vine.DoubleChain N S a b 1) :
    N.IsVine .I S a b := by
  cases h with
  | single h => exact h
  | append h _ _ _ => cases h

/-- A hyper object with a `subsetvc` classification has three atoms or is a single vine in its own adjoint. -/
theorem hyper_shape_of_cls {N : Molecule V D} (U : Object N) {R : HyperLikeRealization N U.atoms U.upper U.lower}
    (hR : U.shape = .hyper R)
    (h : Vine.DoubleChain N U.atoms U.upper U.lower 1 ∨ Vine.DoubleChain N U.atoms U.upper U.lower 2 ∨
      N.IsVine .V U.atoms U.upper U.lower ∨
      ∃ e, N.ends e = s(U.upper, U.lower) ∧
        (Vine.DoubleChain (Mole.eraseBond N e) U.atoms U.upper U.lower 2 ∨
          (Mole.eraseBond N e).IsVine .V U.atoms U.upper U.lower)) :
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
    · exact ⟨.V, isVine_eraseBond_congr h1.symm h⟩
    by_cases h2 : R.added = N.mate e
    · exact ⟨.V, isVine_eraseBond_congr h2.symm ((eraseMateIso N e U.atoms (objectAtoms_sub' U)).isVine h)⟩
    · let O : Object N := ⟨U.atoms, U.upper, U.lower, .hyper ⟨e, he, ⟨h.1, 1, Chain.single ⟨.V, h⟩⟩⟩⟩
      exact hyper_other_isSomeVine O U rfl (R := ⟨e, he, ⟨h.1, 1, Chain.single ⟨.V, h⟩⟩⟩) rfl hR
        (fun h' => h'.elim h1 h2)

/-- The corner: a hyper object contained atom-wise but not designation-wise in an object `Q` is `ObjVine` (the host is hyper with
the same atoms and another designated bond). -/
theorem objVine_of_not_contained {N : Molecule V D} (U Q : Object N) {R : HyperLikeRealization N U.atoms U.upper U.lower}
    (hR : U.shape = .hyper R) (hsub : U.atoms ⊆ Q.atoms) (hnc : ¬ U.IsContained Q) : ObjVine N U := by
  obtain ⟨SQ, qu, ql, shQ⟩ := Q
  cases shQ with
  | vc hQ =>
    exfalso; apply hnc
    unfold Object.IsContained VineLikeObject.IsContained
    rw [hR]
    exact hsub
  | hyper RQ =>
    have hc' : ¬ (U.atoms = SQ → R.added = RQ.added ∨ R.added = N.mate RQ.added) := by
      intro h; apply hnc
      unfold Object.IsContained VineLikeObject.IsContained
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

/-- lg-spine-u's `SubproSupport` (AMEND5, atom level) is S4's `SubproSupportA`. -/
theorem supportA_of_support {C : SubproChoices G} {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} (h : SubproSupport G C L γ η base kFix κ) : SubproSupportA G C L γ η base kFix κ :=
  ⟨h.selectedSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩

/-- **`hsh` for `C₂`**: every member of G3's `C₂` has three atoms or is a single vine (in its own adjoint if hyper). -/
theorem c2_shape (C : SubproChoices G) {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hs : SubproSupport G C L γ η base kFix κ)
    {Un : Set (Object G.molecule)} {U : Object G.molecule} (hU : U ∈ (collDataOf C).C2Of L γ η base κ Un) :
    U.atoms.card = 3 ∨ ObjVine G.molecule U := by
  have hM := Mole.garden_isMolecule G
  obtain ⟨⟨⟨hsg, hout, hdis, hhost⟩, -⟩, -⟩ := hU
  rcases object_shape_cases U with hvc | ⟨R, hR⟩
  · rcases step1_vc_shape' G C L γ η base kFix κ (supportA_of_support hs) c hκ hc U hsg hout hdis hvc with h | h | h
    · right
      obtain ⟨hh, hsh⟩ := hvc
      unfold ObjVine
      rw [hsh]
      exact ⟨.I, doubleChain_one_isVineI h⟩
    · left; have := Vine.doubleChain_card h; omega
    · right
      obtain ⟨hh, hsh⟩ := hvc
      unfold ObjVine
      rw [hsh]
      exact ⟨.V, h⟩
  · obtain ⟨r', hr', hk'⟩ := hsg
    have hrP := (U.shape.toVine_isGap L base κ r').mpr hr'
    rcases hhost with ⟨S, a, b, hDV, hUS, -, -⟩ | ⟨Q, hUQ, hQk, -, -⟩
    · exact hyper_shape_of_cls U hR
        (Vine.subsetvc_classification G.molecule hM U.shape.toVine hUS L γ η base c κ hκ hc hrP hk' (Or.inl hDV))
    · obtain ⟨r, hr, hkr⟩ : ∃ r, Q.shape.IsGap L base κ r ∧
          (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG) := by
        rcases hQk with ⟨r, hr, hk⟩ | ⟨r, hr, hk⟩
        · exact ⟨r, hr, Or.inl hk⟩
        · exact ⟨r, hr, Or.inr hk⟩
      by_cases hcont : U.IsContained Q
      · exact hyper_shape_of_cls U hR
          (Vine.subsetvc_classification G.molecule hM U.shape.toVine hUQ L γ η base c κ hκ hc hrP hk'
            (Or.inr ⟨Q.shape.toVine, (U.shape.toVine_isContained Q.shape).mpr hcont,
              r, (Q.shape.toVine_isGap L base κ r).mpr hr, hkr⟩))
      · exact Or.inr (objVine_of_not_contained U Q hR hUQ hcont)

end garden

end WaveTurbulence.FinalCountAsm
