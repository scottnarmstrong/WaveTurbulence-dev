/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.TVine.Struct.Statement
/-! # H-G3: the named inputs of the layer H-G3 (packet L6-HG3; hand-written)

The layer H-G3 (PLAN-L6 §3e–3f: main's G3 run, `S1*`, `VrHyper3`) is ported over the low family `𝒱_{γL}`
(`Src.IsSomeVine.cases`: (I), (II) and T-vines). Main's ρ-loss of an Operation-1 removal (VINE-RHO,
`VineRho.vine_ladderLoss_le_of_agree`: a vine meets at most `42` maximal ladders and free atoms) is proved for the drawn
vines from their template realization; for a T-vine it is L3's ladder theorem:

* `ladders` — N3 Theorem 6 (iv) (`TVine.Struct.LaddersStatement`; `research-gamma-half-3/NOTES.txt` L142–L170,
  proof L291–L305, REFEREED REF3): a T-vine of a molecule contains at most 3 pairwise disjoint B2 ladders leaving at
  most 13 of its atoms uncovered. Owner L3 (helper L3-LAD, `SPLIT L3-LAD`).

The field is L3's statement verbatim (universe-polymorphic in the atom and dart types, so that it applies to the adjoint
molecules `Molecule.eraseBond M e`, whose dart type is a subtype). A declaration of this layer that needs it adds
`[Src.G3Inputs V D]`; L6 merges the class into `Src.HInputs` at the gate (`G3Inputs.of`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

universe u v

/-- **The named inputs of the layer H-G3** (L3's T-vine ladder theorem N3 Thm 6 (iv)). The parameters only fix the
universes of the molecules to which the field is applied. -/
class G3Inputs (V : Type u) (D : Type v) : Prop where
  /-- N3 Theorem 6 (iv): at most 3 disjoint ladders, at most 13 uncovered atoms (owner L3). -/
  ladders : TVine.Struct.LaddersStatement.{u, v}

/-- The class from L3's published statement. -/
theorem G3Inputs.of (h : TVine.Struct.LaddersStatement.{u, v}) (V : Type u) (D : Type v) : G3Inputs V D :=
  ⟨h⟩

/-- The field does not depend on the atom or dart type, so the class passes to subtypes of darts (the adjoint molecules
`Molecule.eraseBond M e`). -/
instance G3Inputs.subtype {V : Type u} {D : Type v} [h : G3Inputs V D] {p : D → Prop} : G3Inputs V {x : D // p x} :=
  ⟨h.ladders⟩

end WaveTurbulence.GammaLow.FinalCount.Src
