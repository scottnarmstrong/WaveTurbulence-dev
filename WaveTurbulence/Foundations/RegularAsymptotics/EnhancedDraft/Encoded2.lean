/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Encoded

/-!
# Dominant couples ↔ encoded trees (DH21 Prop 4.23, L892–L895)

* `encCode_spec`: `cplEnc (encCode T) = T`, and `encCode T` is a well-formed dominant code
  (`encCode_good`); hence **the map `𝒬 ↦ 𝒯(𝒬)` is onto** (`cplEnc_surjective`);
* `DomCpl`: well-formed dominant couple codes, with DH21's equivalence for `Z = ∅`
  (`DomCpl.equiv_iff_enh`: it is the equivalence of the enhanced couples `(𝒬, ∅)`);
* **`𝒬 ~ 𝒬'` iff `𝒯(𝒬) ~ 𝒯(𝒬')`** (`domCpl_equiv_iff_enc`), and the induced map of classes is a
  bijection (`domClassEquiv`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg EncTree

/-- Well-formed and dominant. -/
def Good (Q : RegCpl) : Prop := Q.wf = true ∧ Q.dominant = true

/-! ### The equivalence classes -/

/-- Well-formed dominant couple codes. -/
abbrev DomCpl : Type := {Q : RegCpl // Good Q}

/-- **DH21's equivalence of dominant couples** (Def 4.18 with `Z = ∅`). -/
instance DomCpl.setoid : Setoid DomCpl where
  r q q' := Shape.Equiv (cplShape0 q.1) (cplShape0 q'.1)
  iseqv := ⟨fun _ => Shape.equiv_refl _, Shape.Equiv.symm, Shape.Equiv.trans⟩

end WaveTurbulence.Links
