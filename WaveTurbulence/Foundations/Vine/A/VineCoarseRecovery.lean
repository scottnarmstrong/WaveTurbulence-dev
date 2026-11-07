/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.Vine.A.VinePrimeUnique
public import WaveTurbulence.Foundations.Vine.A.VineGardenOrbits
/-! Exact recovery of the full V-family state from its actual prime
garden representative, independent of family enumeration. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Twist
open WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {ι : Type*}

/-- A prime coarse family state is the canonical state of its actual garden up to reindexing. -/
theorem coarseState_recovery (A : FamilyReconstruction w ι) (hp : IsPrimeGarden A.skeleton)
    (hF : IsVFamily A) :
    ∃ e : ι ≃ CoreIndex (vinesV A.skeleton),
      stateReindex ((⟨A.skeleton, hp, A.data, A.decodes⟩ : PrimeData A.layered).coarseState) e = A := by
  have hmem : ∀ i, familyVine A.family i ∈ vinesV A.skeleton := by
    intro i
    obtain ⟨c, hc, hat, _, _⟩ := hF.1 i
    have he : c = familyVine A.family i := clVine_eq_of_atoms hat
    exact he ▸ hc
  have hcover : ∀ c ∈ vinesV A.skeleton,
      (∃ X, IsCoreCLVine A.skeleton X c.atoms c.upper c.lower) → ∃ i, A.family.atoms i = c.atoms := by
    intro c hc hcore
    obtain ⟨i, hi, _, _⟩ := hF.2 c hc hcore
    exact ⟨i, hi.symm⟩
  obtain ⟨e, he⟩ := coreFamilyOf_reindex_data A.family (vinesV A.skeleton) (fun _ h => h) hmem hcover
  refine ⟨e, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · apply heq_of_eq
    apply CoreFamily.ext_data
    · exact funext fun i => (he i).1
    · exact funext fun i => (he i).2.1
    · exact funext fun i => (he i).2.2.1
    · exact funext fun i => (he i).2.2.2
  · rfl
  · rfl

/-- The complete coarse garden orbit depends only on the actual prime representative. -/
theorem coarse_outputs_recovery [Fintype ι] {p : ℕ} {kind : Bool}
    (A : FamilyReconstruction w ι) (hp : IsPrimeGarden A.skeleton) (hF : IsVFamily A) :
    A.allCoreOutputs (p := p) (kind := kind) =
      ((⟨A.skeleton, hp, A.data, A.decodes⟩ : PrimeData A.layered).coarseState).allCoreOutputs
        (p := p) (kind := kind) := by
  obtain ⟨e, he⟩ := coarseState_recovery A hp hF
  have h := allCoreOutputs_reindex (p := p) (kind := kind)
    ((⟨A.skeleton, hp, A.data, A.decodes⟩ : PrimeData A.layered).coarseState) e
  rw [he] at h
  exact h

end WaveTurbulence.VineA
