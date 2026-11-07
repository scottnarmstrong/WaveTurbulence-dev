/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGardenPartition
/-! Fine tau classes partition prescribed points. Their garden projections
are exactly the actual once-per-member LF outputs, not a larger generated orbit. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool}

/-- The fine tau class keeps the locally transported prescription. -/
def tauClass (a : PrescribedPrimeGarden w) : Set (PrescribedPrimeGarden w) :=
  {b | Related (p := p) (kind := kind) a b}

theorem mem_tauClass_self (a : PrescribedPrimeGarden w) : a ∈ a.tauClass (p := p) (kind := kind) :=
  Relation.EqvGen.refl a

/-- Exact garden projection: closing actual prescribed batch edges introduces no extra gardens. -/
theorem tauClass_image (a : PrescribedPrimeGarden w) :
    PrescribedPrimeGarden.layered '' a.tauClass (p := p) (kind := kind) =
      a.outputs (p := p) (kind := kind) := by
  ext LG
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Related.outputs_eq hb]
    exact b.mem_outputs_self
  · intro hLG
    obtain ⟨B, ⟨L, hL, hb⟩, he⟩ := (congruent_layered_iff p kind a.state LG).mp hLG
    let b := ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma)
    exact ⟨b, Relation.EqvGen.rel a b ⟨L, B, hb, hL, rfl⟩, he⟩

/-- Fine tau classes of prescribed points coincide exactly at related representatives. -/
theorem tauClass_eq_iff (a b : PrescribedPrimeGarden w) :
    a.tauClass (p := p) (kind := kind) = b.tauClass (p := p) (kind := kind) ↔
      Related (p := p) (kind := kind) a b := by
  constructor
  · intro h
    change b ∈ a.tauClass (p := p) (kind := kind)
    rw [h]
    exact b.mem_tauClass_self
  · intro h
    ext c
    exact ⟨fun hc => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hc,
      fun hc => Relation.EqvGen.trans _ _ _ h hc⟩

/-- Distinct fine classes are disjoint on the prescribed-garden carrier. -/
theorem tauClass_disjoint_or_eq (a b : PrescribedPrimeGarden w) :
    Disjoint (a.tauClass (p := p) (kind := kind)) (b.tauClass (p := p) (kind := kind)) ∨
      a.tauClass (p := p) (kind := kind) = b.tauClass (p := p) (kind := kind) := by
  classical
  by_cases h : Related (p := p) (kind := kind) a b
  · exact Or.inr ((tauClass_eq_iff a b).mpr h)
  · left
    rw [Set.disjoint_left]
    intro c hac hbc
    exact h (Relation.EqvGen.trans _ _ _ hac (Relation.EqvGen.symm _ _ hbc))

/-- Every prescribed point belongs to exactly one fine tau class. -/
theorem existsUnique_tauClass (a : PrescribedPrimeGarden w) :
    ∃! T : Set (PrescribedPrimeGarden w), (∃ b : PrescribedPrimeGarden w, T = b.tauClass (p := p) (kind := kind)) ∧ a ∈ T := by
  refine ⟨a.tauClass (p := p) (kind := kind), ⟨⟨a, rfl⟩, a.mem_tauClass_self⟩, ?_⟩
  rintro T ⟨⟨b, rfl⟩, hba⟩
  exact (tauClass_eq_iff b a).mpr hba

/-- Every projected fine class lies in its representative's actual coarse garden class. -/
theorem tauClass_image_subset_coarse (a : PrescribedPrimeGarden w) :
    PrescribedPrimeGarden.layered '' a.tauClass (p := p) (kind := kind) ⊆
      a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  rw [tauClass_image]
  exact a.prime.fine_outputs_subset_coarse a.totalSigma

/-- A prescribed point's whole fine class stays inside any coarse class containing it. -/
theorem tauClass_stays_in_coarse (a b : PrescribedPrimeGarden w)
    (hb : b.layered ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind)) :
    PrescribedPrimeGarden.layered '' b.tauClass (p := p) (kind := kind) ⊆
      a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  rw [a.prime.coarse_outputs_rebase b.prime hb]
  exact b.tauClass_image_subset_coarse

end WaveTurbulence.VineA.PrescribedPrimeGarden
