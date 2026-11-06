/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NonregularCoupleP
public import WaveTurbulence.Foundations.Molecule.TwistPrime
public import WaveTurbulence.Foundations.Molecule.LFTwist.TruncationScale
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleSkeletonRegularity
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceStructure
/-! AMEND6' (R44 (i), R53): `TwistClosed` for the actual sets `A` of the nonregular estimates: the canonical
truncated gardens of width `2m >= 4`, order `N`, signature `ζ` (`gardenSet`) and the nonregular canonical couples
of order `N` (`coupleSet`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open TTree Reg Reg.Skeleton Twist LFTwist
open scoped Classical

theorem canonObject_false_width {p w : ℕ} {LG : LayeredGarden w} (h : CanonicalObject p false LG) : w = 2 := by
  cases h
  rfl

theorem canonObject_true_GC {p w : ℕ} {LG : LayeredGarden w} (h : CanonicalObject p true LG) :
    IsCanonGC (p + 1) LG := by
  cases h with
  | garden hc => exact ⟨hc.2.1, Or.inl ⟨hc.1, hc.2.2.1⟩, hc.2.2.2⟩

/-- The signature of the decoded garden is the signature of its skeleton. -/
theorem FamilyReconstruction_layered_sig {w : ℕ} {ι : Type*} (B : FamilyReconstruction w ι) :
    B.layered.garden.sig = B.skeleton.sig := by
  have hs := congrArg Raw.sig B.decodes.2
  exact hs.symm

theorem _root_.WaveTurbulence.LFTwist.FamilyBatch.skeleton_sig {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) : B.skeleton.sig = A.skeleton.sig := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih
  | @apply L A B i op h ih =>
    refine ih.trans ?_
    change (chosenSkeleton A.skeleton (A.family.placement i) op.choice).sig = _
    cases op.choice <;> rfl

theorem _root_.WaveTurbulence.LFTwist.FamilyBatch.layered_sig {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) :
    B.layered.garden.sig = A.layered.garden.sig := by
  rw [FamilyReconstruction_layered_sig, FamilyReconstruction_layered_sig, h.skeleton_sig]

theorem twistClosed_gardenSet (P : WTParams) (hd : 1 ≤ P.d) {p N m : ℕ} (hp : p < P.D) (hm2 : 2 ≤ m)
    (ζ : Fin (2 * m) → ℤˣ) (hN : N ≤ P.N (p + 1) ^ 4) : TwistClosed p (gardenSet P p N m ζ) := by
  intro kind ι B L _ hcan hmem LH hLH
  have hmem' := (Canon.finite_truncSum_support P (p + 1) N (2 * m) ζ).mem_toFinset.mp hmem
  obtain ⟨M', B', _, hbatch, rfl⟩ := hLH
  have hn : B.layered.garden.order ≤ P.N (p + 1 - 1) := by
    rw [hmem'.2.2.2]
    exact hN.trans (LFTwist.N_fourth_le_pred P (q := p + 1) (by omega) (by omega) hd)
  refine (Canon.finite_truncSum_support P (p + 1) N (2 * m) ζ).mem_toFinset.mpr ⟨?_, ?_, ?_, ?_⟩
  · have hc := hbatch.canonical hcan
    cases kind with
    | true => exact canonObject_true_GC hc
    | false => have := canonObject_false_width hc; omega
  · exact (hbatch.isTrunc (P.N (p + 1)) (P.N (p + 1 - 1)) hn).mpr hmem'.2.1
  · rw [hbatch.layered_sig]; exact hmem'.2.2.1
  · exact hbatch.order.trans hmem'.2.2.2


theorem corePlacement_not_trivial {w : ℕ} {S : Garden w} (P : CorePlacement S) : ¬ IsTrivialGarden S := by
  intro h
  have := P.lower.2
  rw [h.2] at this
  simp [TTree.branching] at this

/-- A batch of unit twists keeps a prime skeleton prime and a nontrivial skeleton nontrivial. -/
theorem _root_.WaveTurbulence.LFTwist.FamilyBatch.prime_nontrivial {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) :
    IsPrimeGarden A.skeleton → ¬ IsTrivialGarden A.skeleton →
      IsPrimeGarden B.skeleton ∧ ¬ IsTrivialGarden B.skeleton := by
  induction h with
  | nil => intro h1 h2; exact ⟨h1, h2⟩
  | skip i h ih => exact ih
  | @apply L A B i op h ih =>
    intro h1 h2
    apply ih
    · change IsPrimeGarden (chosenSkeleton A.skeleton (A.family.placement i) op.choice)
      cases op.choice with
      | false => exact h1
      | true =>
        exact (unitTwist_prime A.skeleton (A.family.placement i) (A.family.core i) (A.family.designated i)).mpr h1
    · change ¬ IsTrivialGarden (chosenSkeleton A.skeleton (A.family.placement i) op.choice)
      cases op.choice with
      | false => exact h2
      | true => exact corePlacement_not_trivial (reversePlacement A.skeleton (A.family.placement i))

theorem canonObject_two {p : ℕ} {kind : Bool} {LG : LayeredGarden 2} (h : CanonicalObject p kind LG) :
    IsCanonC (p + 1) LG := by
  cases h with
  | garden hc => exact absurd hc.1 (by norm_num)
  | couple hc => exact hc

/-- A couple decodes from its prime skeleton, so it is regular iff the skeleton is trivial. -/
theorem couple_regular_iff_of_reconstruction {ι : Type*} (B : FamilyReconstruction 2 ι)
    (hprime : IsPrimeGarden B.skeleton) (hc : IsCouple B.layered.garden) :
    IsRegularCouple B.layered.garden ↔ IsTrivialGarden B.skeleton := by
  refine couple_regular_iff_prime_skeleton_trivial B.layered.garden B.skeleton hc hprime ?_
  exact (reconstructs_iff_exists_reconstructionData B.skeleton B.layered.garden hprime.1 B.decodes.1).mpr
    ⟨B.data, B.decodes⟩

/-- R53 (1): an LF twist at a prime-skeleton vine keeps a nonregular couple nonregular. -/
theorem twistClosed_coupleSet (P : WTParams) (hd : 1 ≤ P.d) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) : TwistClosed p (coupleSet P p N) := by
  intro kind ι B L hprime hcan hmem LH hLH
  have hmem1 : B.layered ∈ coupleCarrier P (p + 1) N ∧ ¬ IsRegularCouple B.layered.garden := by
    unfold coupleSet at hmem
    exact Finset.mem_filter.mp hmem
  have hmem' := (Canon.finite_truncSumC_support P (p + 1) N).mem_toFinset.mp hmem1.1
  obtain ⟨M', B', _, hbatch, rfl⟩ := hLH
  have hn : B.layered.garden.order ≤ P.N (p + 1 - 1) := by
    rw [hmem'.2.2]
    exact hN.trans (LFTwist.N_fourth_le_pred P (q := p + 1) (by omega) (by omega) hd)
  have hcanB' := canonObject_two (hbatch.canonical hcan)
  have hnt : ¬ IsTrivialGarden B.skeleton := fun ht =>
    hmem1.2 ((couple_regular_iff_of_reconstruction B hprime hmem'.1.1).mpr ht)
  obtain ⟨hprime', hnt'⟩ := hbatch.prime_nontrivial hprime hnt
  unfold coupleSet
  refine Finset.mem_filter.mpr ⟨(Canon.finite_truncSumC_support P (p + 1) N).mem_toFinset.mpr
    ⟨hcanB', (hbatch.isTrunc (P.N (p + 1)) (P.N (p + 1 - 1)) hn).mpr hmem'.2.1,
      hbatch.order.trans hmem'.2.2⟩, ?_⟩
  intro hreg
  exact hnt' ((couple_regular_iff_of_reconstruction B' hprime' hcanB'.1).mp hreg)

end WaveTurbulence.LGSpine
