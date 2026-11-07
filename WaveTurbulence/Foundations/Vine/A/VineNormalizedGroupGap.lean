/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedHVCGroupGap
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesigCovariance
/-! Actual successor group gap kinds in every maximal-group case. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Stage1 RedSplice LGSpine.SourceVine
variable {w d : ℕ} {G : Garden w}

/-- Exact object covariance implies the same decorated group kind. -/
theorem groupGapKind_of_object_map {H : Garden w} (F : MolIso G.molecule H.molecule)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (he : designatedObject H (F.img S) = (designatedObject G S).map (mapObject F))
    (scale γ η : ℝ) (base : Mom d) (κ : GardenDart H → (Fin d → ℤ)) :
    groupGapKind H scale γ η base κ (F.img S) = groupGapKind G scale γ η base (κ ∘ F.d) S := by
  obtain ⟨a, O, _, hO, _⟩ := designatedObject_spec hS
  rw [hO] at he
  obtain ⟨k, hk⟩ := Represents.exists_hasGapKind (mapObject F O) scale γ η base κ
  exact (groupGapKind_eq scale γ η base κ he hk).trans
    (groupGapKind_eq scale γ η base (κ ∘ F.d) hO ((mapObject_gapKind F O scale γ η base κ k).mp hk)).symm

/-- The complete successor designation gap is LF-covariant, including HV and DV. -/
theorem groupGapKind_twist (Z : TwistGroupSite G)
    (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch Z.target.tree → Mom d)
    (κ : GardenDart Z.target → (Fin d → ℤ)) (hκ : Z.target.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ v ∈ Z.target.molecule.atoms, Z.target.molecule.deg v = 4 → charge v = 0) :
    groupGapKind Z.target scale γ η base κ (Z.iso.img S) =
      groupGapKind G scale γ η base (κ ∘ Z.iso.d) S := by
  classical
  by_cases hvc : ∃ a b, IsVC G.molecule S a b
  · obtain ⟨a, b, hvc⟩ := hvc
    exact groupGapKind_image_of_VC Z.iso hS hvc scale γ η base charge κ hκ hc0
  by_cases hhvc : ∃ a b, IsHVC G.molecule S a b
  · obtain ⟨a, b, hhvc⟩ := hhvc
    exact groupGapKind_image_of_HVC Z.iso hS hhvc scale γ η base charge κ hκ hc0
  by_cases hhv : ∃ a b, IsHV G.molecule S a b
  · exact groupGapKind_of_object_map Z.iso hS
      (designatedObject_singleHV_twist Z hsel ⟨hS, hhv, hhvc⟩) scale γ η base κ
  · have hdv : PureDVGroup G S := by
      refine ⟨hS, ?_, ?_⟩
      · obtain ⟨a, b, h | h | h | h⟩ := hS.1
        · exact (hhv ⟨a, b, h⟩).elim
        · exact (hvc ⟨a, b, h⟩).elim
        · exact (hhvc ⟨a, b, h⟩).elim
        · exact ⟨a, b, h⟩
      · rintro ⟨a, b, h | h | h⟩
        · exact hhv ⟨a, b, h⟩
        · exact hvc ⟨a, b, h⟩
        · exact hhvc ⟨a, b, h⟩
    exact groupGapKind_of_object_map Z.iso hS (designatedObject_pureDV_twist Z hsel hdv) scale γ η base κ

/-- Selection on dart labels; the node-label `selOf` is its bondIndex specialization. -/
def selDarts (σ : Represents.GroupPrescription G) (scale γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∀ S, groupGapKind G scale γ η base κ S.1 = σ S

/-- Actual selection is preserved under a coarse LF operation for every local coloring. -/
theorem selDarts_twist (Z : TwistGroupSite G)
    (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0)
    (σ : Represents.GroupPrescription G) (scale γ η : ℝ) (base : Mom d)
    (charge : GBranch Z.target.tree → Mom d) (κ : GardenDart Z.target → (Fin d → ℤ))
    (hκ : Z.target.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ v ∈ Z.target.molecule.atoms, Z.target.molecule.deg v = 4 → charge v = 0) :
    selDarts (transportGroupPrescription Z.iso σ) scale γ η base κ ↔
      selDarts σ scale γ η base (κ ∘ Z.iso.d) := by
  constructor
  · intro h S
    exact (groupGapKind_twist Z hsel S.2 scale γ η base charge κ hκ hc0).symm.trans
      ((h (groupEquiv Z.iso S)).trans (transportGroupPrescription_apply Z.iso σ S))
  · intro h T
    obtain ⟨S, rfl⟩ := (groupEquiv Z.iso).surjective T
    exact (groupGapKind_twist Z hsel S.2 scale γ η base charge κ hκ hc0).trans
      ((h S).trans (transportGroupPrescription_apply Z.iso σ S).symm)

end WaveTurbulence.VineA.NormalizedSplice
