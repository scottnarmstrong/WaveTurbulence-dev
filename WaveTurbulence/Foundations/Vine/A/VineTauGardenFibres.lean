/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
/-! At a fixed actual garden, tau classes are represented by its local restricted
prescriptions. This uses prime uniqueness and assumes no global identification. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist Represents
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-- A local prescribed point at the unique prime representative of a fixed garden. -/
def atGarden (A : PrimeData LG) (σ : GroupPrescription A.skeleton) : PrescribedPrimeGarden w := ⟨LG, A, σ⟩

/-- Every prescribed point over this garden is one of its local restricted prescriptions. -/
theorem exists_atGarden (A : PrimeData LG) (b : PrescribedPrimeGarden w) (hb : b.layered = LG) :
    ∃ σ : GroupPrescription A.skeleton, b = atGarden A σ := by
  rcases b with ⟨LH, B, σ⟩
  change LH = LG at hb
  subst LH
  have he : B = A := primeData_unique B A
  subst B
  exact ⟨σ, rfl⟩

/-- The projected classes meeting a garden are precisely those of its local prescriptions. -/
theorem tauClass_over_garden_iff (A : PrimeData LG) (T : Set (PrescribedPrimeGarden w)) :
    (∃ b : PrescribedPrimeGarden w, T = b.tauClass (p := p) (kind := kind)) ∧
        LG ∈ PrescribedPrimeGarden.layered '' T ↔
      ∃ σ : GroupPrescription A.skeleton, T = (atGarden A σ).tauClass (p := p) (kind := kind) := by
  constructor
  · rintro ⟨⟨a, rfl⟩, ⟨b, hb, hLG⟩⟩
    obtain ⟨σ, he⟩ := exists_atGarden A b hLG
    exact ⟨σ, ((tauClass_eq_iff a b).mpr hb).trans (congrArg (tauClass (p := p) (kind := kind)) he)⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨atGarden A σ, rfl⟩, ⟨atGarden A σ, mem_tauClass_self _, rfl⟩⟩

/-- There are finitely many prescribed tau classes through any one actual garden. -/
theorem finite_tauClasses_over_garden (A : PrimeData LG) :
    {T : Set (PrescribedPrimeGarden w) |
      (∃ b : PrescribedPrimeGarden w, T = b.tauClass (p := p) (kind := kind)) ∧
        LG ∈ PrescribedPrimeGarden.layered '' T}.Finite := by
  have he : {T : Set (PrescribedPrimeGarden w) |
      (∃ b : PrescribedPrimeGarden w, T = b.tauClass (p := p) (kind := kind)) ∧
        LG ∈ PrescribedPrimeGarden.layered '' T} =
      Set.range (fun σ : GroupPrescription A.skeleton => (atGarden A σ).tauClass (p := p) (kind := kind)) := by
    ext T
    constructor
    · intro hT
      obtain ⟨σ, hσ⟩ := (tauClass_over_garden_iff A T).mp hT
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, hσ⟩
      exact (tauClass_over_garden_iff A T).mpr ⟨σ, hσ.symm⟩
  rw [he]
  exact Set.finite_range _

end WaveTurbulence.VineA.PrescribedPrimeGarden
