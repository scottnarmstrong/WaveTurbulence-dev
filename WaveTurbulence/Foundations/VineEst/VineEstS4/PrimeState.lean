/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport
import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceStructure
import WaveTurbulence.Foundations.Molecule.TwistPrime

/-! # Canonical representatives: prime skeletons are unique and preserved by LF batches (V5 Step 4b, R31(1))

TARGET `propstructure2` (L870): a garden has a unique prime skeleton and unique regular replacements over it.  In the
universe this is `existsUnique_prime_with_replacements` (SKELETON, DH21 4.13 / DH21-2 4.4, L833 general-couple
uniqueness included).

* `batch_prime`: an LF batch preserves primeness of the skeleton (`unitTwist_prime`, TARGET twist: "`G'` is prime iff
  `G` is").
* `eq_of_prime_layered`: two batch outputs from a state with a prime skeleton, along nodup lists, that have the same
  layered garden are equal states (skeleton, family, reconstruction data, layered garden): there is exactly one
  canonical representative of each garden of the class.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

/-- One LF operation preserves a prime skeleton. -/
theorem prime_output {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (h : IsPrimeGarden A.skeleton) : IsPrimeGarden op.output.skeleton := by
  change IsPrimeGarden (chosenSkeleton A.skeleton (A.family.placement i) op.choice)
  generalize op.choice = ε
  cases ε
  · exact h
  · exact (unitTwist_prime A.skeleton (A.family.placement i) (A.family.core i) (A.family.designated i)).mpr h

/-- An LF batch preserves a prime skeleton: LF twists map canonical representatives to canonical ones. -/
theorem batch_prime {L : List ι} {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B)
    (hA : IsPrimeGarden A.skeleton) : IsPrimeGarden B.skeleton := by
  induction h with
  | nil => exact hA
  | skip i h ih => exact ih hA
  | apply op h ih => exact ih (prime_output op hA)

theorem Reach.prime {L : List ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {c' : ChainAt B.skeleton B.family} (h : Reach p kind L A c B c') (hA : IsPrimeGarden A.skeleton) :
    IsPrimeGarden B.skeleton :=
  batch_prime h.batch hA

/-- The reconstruction data over a prime skeleton is determined by the decoded garden (SKELETON, L833). -/
theorem data_eq_of_prime (B B' : FamilyReconstruction w ι) (hS : B.skeleton = B'.skeleton)
    (hB : IsPrimeGarden B.skeleton) (hg : B.layered.garden = B'.layered.garden) :
    B.data = hS ▸ B'.data := by
  cases B with
  | mk S F pl D L d =>
    cases B' with
    | mk S' F' pl' D' L' d' =>
      dsimp only at hS hB hg ⊢
      subst hS
      dsimp only at D' d' ⊢
      exact reconstructionData_unique D D' hB (by simpa using d) (by rw [hg]; exact d')

/-- Two states with prime skeletons and equal decoded gardens have the same skeleton. -/
theorem skeleton_eq_of_prime (B B' : FamilyReconstruction w ι) (hB : IsPrimeGarden B.skeleton)
    (hB' : IsPrimeGarden B'.skeleton) (hg : B.layered.garden = B'.layered.garden) : B.skeleton = B'.skeleton := by
  have hP : ∀ C : FamilyReconstruction w ι, IsPrimeGarden C.skeleton →
      ∃ hS : IsPrimeGarden C.skeleton, ∃! D : ReconstructionData C.skeleton, D.Decodes hS.1 C.layered.garden :=
    fun C hC => ⟨hC, C.data, C.decodes, fun E he => reconstructionData_unique E C.data hC he C.decodes⟩
  obtain ⟨S, _, hu⟩ := existsUnique_prime_with_replacements B.layered.garden B.decodes.1
  have h1 := hu B.skeleton (hP B hB)
  have h2 := hu B'.skeleton (by rw [hg]; exact hP B' hB')
  exact h1.trans h2.symm

/-- **There is exactly one canonical representative of each garden of the class.**  Two outputs of LF batches (nodup
lists) from a state with a prime skeleton that have the same layered garden are the same state: the prime skeleton, the
carried core family and the regular replacement data are all determined (`existsUnique_prime_with_replacements` for the
skeleton and the data, `familyBatch_garden_injective` for the twist subset). -/
theorem eq_of_prime_layered [DecidableEq ι] {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup) {B B' : FamilyReconstruction w ι}
    (h : FamilyBatch p kind M A B) (h' : FamilyBatch p kind M' A B') (hl : B.layered = B'.layered) : B = B' := by
  have hB := batch_prime h hA
  have hB' := batch_prime h' hA
  have hg : B.layered.garden = B'.layered.garden := by rw [hl]
  have hS := skeleton_eq_of_prime B B' hB hB' hg
  have hd := data_eq_of_prime B B' hS hB hg
  obtain ⟨T, _, eT⟩ := h.skeleton_subset hM
  obtain ⟨T', _, eT'⟩ := h'.skeleton_subset hM'
  have hTT : T = T' := by
    apply familyBatch_garden_injective A.familyState
    have e1 := congrArg Sigma.fst eT
    have e2 := congrArg Sigma.fst eT'
    exact e1.symm.trans (hS.trans e2)
  have hF : B.familyState = B'.familyState := eT.trans (hTT ▸ eT'.symm)
  revert hS hd hF hl
  cases B with
  | mk S F pl D L d =>
    cases B' with
    | mk S' F' pl' D' L' d' =>
      intro hl hS hd hF
      dsimp only at hS hd hF hl
      subst hS
      have hFF : F = F' := eq_of_heq (Sigma.mk.inj hF).2
      subst hFF
      subst hl
      have hDD : D = D' := hd
      subst hDD
      rfl

end WaveTurbulence.VineEstS4
