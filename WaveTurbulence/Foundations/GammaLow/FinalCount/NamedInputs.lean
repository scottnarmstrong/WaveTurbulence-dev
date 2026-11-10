/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
/-! # Named inputs of L6 (FINALCOUNT-LOW) from the T-vine combinatorics (owner L3)

One copy, for L6 and its helpers (L6E, L6-COUNT, L6-STEP1). Each is a `def … : Prop` stated over the pinned D11 text
(`TVine/Defs.lean`) and L6's `𝒱_γ` object layer `Src`, exactly as (or as a direct special case of) the refereed note.
They are hypotheses of internal theorems under these names only; wt-orch discharges them at assembly from L3.

* `TVinePiecesInput` — N2 Proposition 1.17(b) (piece-shape theorem; `research-m4/NOTES.md` L218–L222, from
  `research-gamma-half-2/NOTES.md`; REFEREED REF2).
* `Cor116PrimeInput` — N3 Corollary 1.16′ (1) location, (2) list and (3) connectivity, for a container that is a single
  vine of `𝒱_enl` (`research-gamma-half-3/NOTES.txt` L459–L499, sources' removal semantics; REFEREED REF3). The
  multi-ingredient containers (HV, VC, HVC, DV′: (L-b), (L-c)) and part (4) are NOT included; they are a later
  extension once L3 publishes the full statement (this def is then a consequence of it).
* `DrawnTVineInput` — N2 Lemma 5.2 (`research-gamma-half-2/NOTES.md` L828–L837; REFEREED REF2). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
open Finset
universe u v

section shapes
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

end shapes

/-- **NAMED INPUT (N2 Lemma 5.2, `𝒱_{>1/2} ⊂ 𝒱_{≤1/2}`; owner L3).** Every expansion of a drawn template
(III)–(VIII) is a T-vine ("Every expansion T_X(k⃗) of the B2 templates X = III–VIII is a T-vine"). -/
def DrawnTVineInput : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (X : VineType)
    (S : Finset V) (a b : V), X ≠ .I → X ≠ .II → M.IsVine X S a b → M.IsTVine S a b

end WaveTurbulence.GammaLow.FinalCount
