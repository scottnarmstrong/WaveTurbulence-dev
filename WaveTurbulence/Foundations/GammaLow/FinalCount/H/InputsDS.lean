/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.TVine.Struct.LemmaP.Proof
/-! # H-DS: the named inputs of the drawn-type layer (packet L6-HDS; hand-written)

The layer H-DS (PLAN-L6 §3e–3f) consists of the ported modules of main that name the drawn vine types (III)–(VIII).
In the low family `𝒱_{γL}` (`Src.IsSomeVine.cases`) a vine is of type (I), (II) or a T-vine, and the drawn-type
classifications of main (TARGET `subsetvc`: "a double bond, two double bonds, or a vine (V)") are replaced by the T-vine
statements of L3 (`TVine/Struct/Statement.lean`, published in `status/L3-defs.txt`):

* `cor116` — N3 Corollary 1.16′ (1)–(3) for a single-vine container (`Struct.Cor116SingleStatement`, = L6's
  `Cor116PrimeInput`; `research-gamma-half-3/NOTES.txt` L459–L499, REFEREED REF3). Owner L3.
* `subObjects` — N2 Theorem 1.15 (F1)–(F6) (`Struct.SubObjectsStatement`; `research-m4/NOTES.md` §2.2 L191–L201, REF2 R1
  patch in N3 §2.1, REFEREED). Owner L3.
* `lemmaP` — N3 Lemma P (parity; `Struct.LemmaPStatement`; `research-gamma-half-3/NOTES.txt` L500–L513, REFEREED REF3):
  removing the joint bond of a vine with `σ = 1` keeps it connected after removals. Used for a DV′ one of whose
  branches is removed whole (TARGET `subsetvc` removal clause). Owner L3 (helper L3-LP).

The fields are L3's statements verbatim (universe-polymorphic in the atom and dart types, so that they apply to the
adjoint molecules `Molecule.eraseBond M e`, whose dart type is a subtype). **They are all proved** (L3, L3-LP; wt-orch
2026-11-09): the instance `DSInputs.holds` discharges the class, and no declaration of the layer takes it as a hypothesis.
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

universe u v

/-- **The named inputs of the layer H-DS** (L3's T-vine statements N3 Cor 1.16′ and N2 Thm 1.15). The parameters only
fix the universes of the molecules to which the fields are applied. -/
class DSInputs (V : Type u) (D : Type v) : Prop where
  /-- N3 Corollary 1.16′ (1)–(3), single-vine container (owner L3). -/
  cor116 : TVine.Struct.Cor116SingleStatement.{u, v}
  /-- N2 Theorem 1.15 (F1)–(F6) (owner L3). -/
  subObjects : TVine.Struct.SubObjectsStatement.{u, v}
  /-- N3 Lemma P (owner L3, helper L3-LP). -/
  lemmaP : TVine.Struct.LemmaPStatement.{u, v}

/-- The class from L3's published statements. -/
theorem DSInputs.of (h₁ : TVine.Struct.Cor116SingleStatement.{u, v}) (h₂ : TVine.Struct.SubObjectsStatement.{u, v})
    (h₃ : TVine.Struct.LemmaPStatement.{u, v}) (V : Type u) (D : Type v) : DSInputs V D :=
  ⟨h₁, h₂, h₃⟩

/-- **All fields are proved (2026-11-09):** L3's `Struct.cor116Single_holds`, `Struct.subObjects_holds`
(`TVine/Struct/Final.lean`) and L3-LP's `Struct.lemmaP` (`TVine/Struct/LemmaP/Proof.lean`), unconditionally. The layer
H-DS therefore carries no named input: its declarations use the fields through this instance. -/
instance DSInputs.holds (V : Type u) (D : Type v) : DSInputs V D :=
  DSInputs.of TVine.Struct.cor116Single_holds TVine.Struct.subObjects_holds TVine.Struct.lemmaP V D

end WaveTurbulence.GammaLow.FinalCount.Src
