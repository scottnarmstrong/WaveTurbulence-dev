/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.F6Main
public import WaveTurbulence.Foundations.TVine.Struct.FamBridge
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F1)–(F6): `SubObjectsStatement` (packet L3)

* `memberI`: a member of a T-vine with two atoms is a vine (I);
* `f6_mol`: (F6) at the molecule level;
* **`subObjects`**: `SubObjectsStatement` from `Thm115Inputs` (L2's base statements and size bound, L1's 1.14(c′));
* **`subObjects_of_open`**, **`cor116Single_of_open`**: the same from the open part `Thm115Open` only.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem card_of_isVCII {M : Molecule V D} {S : Finset V} {a b : V} (h : IsVCII M S a b) : S.card = 3 := by
  obtain ⟨c, h1, h2, h3, rfl, -, -⟩ := h
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm h1, h3]), Finset.card_pair h2]

theorem five_le_of_isTVine {D' : Type*} [Fintype D'] [DecidableEq D'] {M : Molecule V D'} {S : Finset V} {a b : V}
    (h : M.IsTVine S a b) : 5 ≤ S.card := by
  have := (card_isTVineU ((isTVine_iff M).mp h).2).2
  rwa [groupGraph_verts] at this

/-- A two-atom member of a T-vine is a vine (I). -/
theorem memberI {γ : ℝ} {M : Molecule V D} (U : Src.Object γ M) (hmt : TVineMemberType M U)
    (hc : U.atoms.card = 2) : M.IsVine .I U.atoms U.upper U.lower := by
  obtain ⟨A, a, b, sh⟩ := U
  have hc' : A.card = 2 := hc
  cases sh with
  | vc h =>
    rcases (hmt : M.IsVine .I A a b ∨ IsVCII M A a b ∨ M.IsTVine A a b) with h1 | h1 | h1
    · exact h1
    · have := card_of_isVCII h1; omega
    · have := five_le_of_isTVine h1; omega
  | hyper R =>
    exfalso
    rcases (hmt : IsVCII (Molecule.eraseBond M R.added) A a b ∨ (Molecule.eraseBond M R.added).IsTVine A a b)
      with h1 | h1
    · have := card_of_isVCII h1; omega
    · have := five_le_of_isTVine h1; omega

/-- **N2 Theorem 1.15 (F6)**, molecule level. -/
theorem f6_mol (I : Thm115Inputs.{u}) {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hT : M.IsTVine S j₁ j₂) (U U' : Src.Object γ M) (hUS : U.atoms ⊂ S) (hU'S : U'.atoms ⊂ S)
    (hne : (U.atoms ∩ U'.atoms).Nonempty) (h1 : ¬ U.atoms ⊆ U'.atoms) (h2 : ¬ U'.atoms ⊆ U.atoms) :
    M.IsVine .I U.atoms U.upper U.lower ∧ M.IsVine .I U'.atoms U'.upper U'.lower ∧
      (U.atoms ∩ U'.atoms).card = 1 := by
  have hTU := ((isTVine_iff M).mp hT).2
  obtain ⟨ks, hks⟩ := vineLike_suOf hγ U hUS
  obtain ⟨ks', hks'⟩ := vineLike_suOf hγ U' hU'S
  obtain ⟨hk, hk', hc⟩ := f6U I hTU hks hks' hne h1 h2
  subst hk hk'
  exact ⟨memberI U (tvine_member I containerJointsInput_holds hγ hT U hUS).2.2 (kinds_card_I hks),
    memberI U' (tvine_member I containerJointsInput_holds hγ hT U' hU'S).2.2 (kinds_card_I hks'), hc⟩

/-- **N2 Theorem 1.15 (F1)–(F6)** (= L5c / L07 `SubObjectsInput`). -/
theorem subObjects (I : Thm115Inputs.{u}) : SubObjectsStatement.{u, v} := by
  intro V D _ _ _ M S j₁ j₂ hT
  have hTU := ((isTVine_iff M).mp hT).2
  refine ⟨(f1_mol hT).1, (f1_mol hT).2, f2_mol hT, fun γ hγ => ⟨fun U hUS => ⟨?_, ?_⟩,
    fun n U hsub hdisj => tvineFamilies_of I M γ hγ S j₁ j₂ hT n U hsub hdisj,
    fun U U' hUS hU'S hne h1 h2 => f6_mol I hγ hT U U' hUS hU'S hne h1 h2⟩⟩
  · exact (tvine_member I containerJointsInput_holds hγ hT U hUS).2.2
  · obtain ⟨ks, hks⟩ := vineLike_suOf hγ U hUS
    exact gapFree_of_gapFreeU hT U hks.1
      (subObj_single I _ (groupGraph M S) j₁ j₂ rfl hTU (suOf U) ks hks).2.1

end WaveTurbulence.TVine.Struct
