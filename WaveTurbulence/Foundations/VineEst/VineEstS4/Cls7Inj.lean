/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls6Zp

/-! # Class combinatorics, part 6: `zp_eq_of_sigStar` (V5 Step 4b, WP-A, step 1 of the Σ-bijection)

Two states reached from a state with a prime skeleton by a batch over `[i]` (so: the start state itself, or the output of one
operation at `i`) that have the same signature `sigStar _ i` are equal.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

section Op
variable (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))

/-- Two operations at `i` with the same choice and the same signature have the same output layered garden. -/
theorem layered_eq_same {ε : Bool} (con con' : LFConstruction (A.source i hcan hel htc hcc) ε)
    (h : sigStar (opOut A i hcan hel htc hcc con) i = sigStar (opOut A i hcan hel htc hcc con') i) :
    (opOut A i hcan hel htc hcc con).layered = (opOut A i hcan hel htc hcc con').layered := by
  rw [sigStar_output, sigStar_output] at h
  have h23 := (Prod.mk.inj h).2
  have h2 := (Prod.mk.inj h23).1
  have h3 := (Prod.mk.inj h23).2
  exact Compat.layered_eq (compat_op A i hcan hel htc hcc con) (compat_op A i hcan hel htc hcc con') h3 h2

/-- The start state and a FALSE operation with the same signature have the same layered garden. -/
theorem layered_eq_skip (con : LFConstruction (A.source i hcan hel htc hcc) false)
    (h : sigStar A i = sigStar (opOut A i hcan hel htc hcc con) i) :
    A.layered = (opOut A i hcan hel htc hcc con).layered := by
  rw [sigStar_self, sigStar_output] at h
  have h23 := (Prod.mk.inj h).2
  have h2 := (Prod.mk.inj h23).1
  have h3 := (Prod.mk.inj h23).2
  have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain false
      (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
      pairOfLeaf A.skeleton A.plain (A.family.placement i).retained := pairOfLeaf_firstLeaf A.skeleton A.plain _
  have h2' : nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A)
      (chosenPairEquiv A.skeleton (A.family.placement i) A.plain false
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) =
      nativeCoupleLayered (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering _)
        (chosenPairEquiv A.skeleton (A.family.placement i) A.plain false
          (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) := by
    rw [hq] at h2 ⊢
    exact h2
  exact Compat.layered_eq (compat_self A i hcan) (compat_op A i hcan hel htc hcc con) h3 h2'

/-- The start state and a TRUE operation have different signatures. -/
theorem sigStar_ne_skip_true (con : LFConstruction (A.source i hcan hel htc hcc) true) :
    sigStar A i ≠ sigStar (opOut A i hcan hel htc hcc con) i := by
  intro h
  rw [sigStar_self, sigStar_output] at h
  have h1 := (Prod.mk.inj h).1
  rw [sign_out_true A i hcan hel htc hcc con] at h1
  exact units_ne_neg _ h1

/-- A FALSE and a TRUE operation have different signatures. -/
theorem sigStar_ne_false_true (con : LFConstruction (A.source i hcan hel htc hcc) false)
    (con' : LFConstruction (A.source i hcan hel htc hcc) true) :
    sigStar (opOut A i hcan hel htc hcc con) i ≠ sigStar (opOut A i hcan hel htc hcc con') i := by
  intro h
  rw [sigStar_output, sigStar_output] at h
  have h1 := (Prod.mk.inj h).1
  rw [sign_out_true A i hcan hel htc hcc con'] at h1
  exact units_ne_neg _ h1

end Op

section Inj
variable {A : FamilyReconstruction w ι} {i : ι}

theorem zp_layered_eq {X X' : FamilyReconstruction w ι} (hX : FamilyBatch p kind [i] A X)
    (hX' : FamilyBatch p kind [i] A X') (h : sigStar X i = sigStar X' i) : X.layered = X'.layered := by
  cases hX with
  | skip _ h1 =>
    cases h1
    cases hX' with
    | skip _ h1' => cases h1'; rfl
    | apply op' h1' =>
      cases h1'
      obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op'
      cases ε
      · exact layered_eq_skip A i hcan hel htc hcc con h
      · exact absurd h (sigStar_ne_skip_true A i hcan hel htc hcc con)
  | apply op h1 =>
    cases h1
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases hX' with
    | skip _ h1' =>
      cases h1'
      cases ε
      · exact (layered_eq_skip A i hcan hel htc hcc con h.symm).symm
      · exact absurd h.symm (sigStar_ne_skip_true A i hcan hel htc hcc con)
    | apply op' h1' =>
      cases h1'
      obtain ⟨hcan', hel', htc', hcc', ε', con'⟩ := op'
      cases ε <;> cases ε'
      · exact layered_eq_same A i hcan hel htc hcc con con' h
      · exact absurd h (sigStar_ne_false_true A i hcan hel htc hcc con con')
      · exact absurd h.symm (sigStar_ne_false_true A i hcan hel htc hcc con' con)
      · exact layered_eq_same A i hcan hel htc hcc con con' h

/-- **Injectivity of the signature on `Zp(A)`.** -/
theorem zp_eq_of_sigStar [DecidableEq ι] (hA : IsPrimeGarden A.skeleton) {X X' : FamilyReconstruction w ι}
    (hX : FamilyBatch p kind [i] A X) (hX' : FamilyBatch p kind [i] A X') (h : sigStar X i = sigStar X' i) :
    X = X' :=
  eq_of_prime_layered hA (List.nodup_singleton i) (List.nodup_singleton i) hX hX' (zp_layered_eq hX hX' h)

end Inj

end WaveTurbulence.VineEstS4
