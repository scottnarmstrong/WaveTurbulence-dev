/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Collection
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyOutputs
import Mathlib.Tactic

/-!
# TARGET Definition `defcong` (L1934-L1937), congruence via LF twists at `𝒱`

States of the LF family machinery are `LFTwist.FamilyReconstruction` (a skeleton, the transported
core family, reconstruction data decoding the layered garden).  A state is a **`𝒱`-state** if its
family consists of exactly the core members of `vinesV` of its own skeleton.  Congruence of states is
reachability by a once-per-member batch of LF operations over all members; the congruence class of a state
`A` is therefore literally M7's `A.allCoreOutputs` (`outputs` over all members).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open WaveTurbulence.LFTwist WaveTurbulence.Twist

variable {w : ℕ} {ι : Type*}

/-- Member `i` of the family of `A` is the (CL) vine `c` of the skeleton. -/
@[expose] def FamilyRealizes (A : FamilyReconstruction w ι) (i : ι) (c : CLVine A.skeleton) : Prop :=
  c.atoms = A.family.atoms i ∧ c.upper = A.family.upper i ∧ c.lower = (A.family.placement i).lower

/-- The family of `A` is the core part of `𝒱` of the skeleton of `A`. -/
@[expose] def IsVFamily (A : FamilyReconstruction w ι) : Prop :=
  (∀ i, ∃ c ∈ vinesV A.skeleton, FamilyRealizes A i c) ∧
  (∀ c ∈ vinesV A.skeleton, (∃ X, IsCoreCLVine A.skeleton X c.atoms c.upper c.lower) →
    ∃ i, FamilyRealizes A i c)

/-- **Congruence** (TARGET `defcong`, L1936): `B` is obtained from `A` by an LF twist at the vines of the
family, i.e. by a once-per-member batch of admissible LF operations over all members. -/
@[expose] def Congruent (p : ℕ) (kind : Bool) [Fintype ι] (A B : FamilyReconstruction w ι) : Prop :=
  ∃ M : List ι, M.Perm Finset.univ.toList ∧ FamilyBatch p kind M A B

/-- The congruence class of `A` is exactly M7's `outputs` (so `sum_localCoordinates` applies). -/
theorem congruent_layered_iff (p : ℕ) (kind : Bool) [Fintype ι] (A : FamilyReconstruction w ι)
    (LH : LayeredGarden w) :
    LH ∈ A.allCoreOutputs (p := p) (kind := kind) ↔ ∃ B, Congruent p kind A B ∧ B.layered = LH := by
  constructor
  · rintro ⟨M, B, hM, hB, rfl⟩
    exact ⟨B, ⟨M, hM, hB⟩, rfl⟩
  · rintro ⟨B, ⟨M, hM, hB⟩, rfl⟩
    exact ⟨M, B, hM, hB, rfl⟩

theorem Congruent.refl (p : ℕ) (kind : Bool) [Fintype ι] (A : FamilyReconstruction w ι) :
    Congruent p kind A A := by
  refine ⟨(Finset.univ : Finset ι).toList, List.Perm.refl _, ?_⟩
  generalize (Finset.univ : Finset ι).toList = L
  induction L with
  | nil => exact .nil A
  | cons i L ih => exact .skip i ih

end WaveTurbulence.Stage1
