/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.ObjBridge3
public import WaveTurbulence.Foundations.TVine.Core.Statements
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F2), (F3) for the members of a T-vine, molecule level (packet L3)

* NAMED INPUT `ContainerJointsInput` (N2 Lemma 1.12; owner L1; verbatim body of L1's drafted
  `ContainerJointsStatement`);
* `joints_not_mem_of_subObj` (U level, (F2)): no proper sub-object of a T-vine contains a joint;
* **`tvine_member`**: for `γ ≤ 1/2`, every vine-like object `U` (`Src.Object`) with `S(U) ⊊ S` inside a T-vine `S`
  avoids the joints and has L6's `TVineMemberType` (N3 Cor 1.16′ (1) (L-a), (2) for a T-vine container).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

/-- **NAMED INPUT (N2 Lemma 1.12, container joints; owner L1).** Verbatim body of L1's drafted
`ContainerJointsStatement` (`research-gamma-half-2/NOTES.md` L281–L292; REFEREED REF2). -/
def ContainerJointsInput : Prop := Core.ContainerJointsStatement.{u}

/-- **(F2) at U level**: no proper sub-object of a T-vine contains a joint. -/
theorem joints_not_mem_of_subObj (I : Thm115Inputs.{u}) (hcj : ContainerJointsInput.{u}) {V : Type u}
    [DecidableEq V] {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U) :
    j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms :=
  hcj G j₁ j₂ U hT.1 (loopless_of_isTVineU hT) (interior_connOn (t6Ctx_of_isTVineU I.pend hT))
    (noCut_of_inputs I hT) hU

/-- **The members of a T-vine** (N3 Cor 1.16′ (1), (2) for a T-vine container; N2 Thm 1.15 (F2), (F3)). -/
theorem tvine_member (I : Thm115Inputs.{u}) (hcj : ContainerJointsInput.{u}) {V : Type u} {D : Type v}
    [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ} (hγ : γ ≤ 1 / 2) {S : Finset V}
    {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂) (U : Src.Object γ M) (hUS : U.atoms ⊂ S) :
    j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms ∧ TVineMemberType M U := by
  obtain ⟨ks, hks⟩ := vineLike_suOf hγ U hUS
  have hTU := ((isTVine_iff M).mp hT).2
  obtain ⟨hj₁, hj₂⟩ := joints_not_mem_of_subObj I hcj hTU hks.1
  have hk := (subObj_single I _ (groupGraph M S) j₁ j₂ rfl hTU (suOf U) ks hks).1
  exact ⟨hj₁, hj₂, memberType_of_kinds hT U hUS hks hk⟩

end WaveTurbulence.TVine.Struct
