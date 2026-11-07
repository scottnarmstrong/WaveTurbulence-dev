/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHVCObjectGap
public import WaveTurbulence.Foundations.Vine.A.VineOrdinaryGroupGap
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
/-! Actual HVC maximal-group gap kinds are invariant under molecular relabeling.
The deleted-bond compatibility is proved from the long adjoint chain. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine Represents
variable {d : ℕ}

/-- The actual independently chosen HVC group gap kinds agree under relabeling. -/
theorem groupGapKind_image_of_HVC {w : ℕ} {G H : Garden w} (F : MolIso G.molecule H.molecule)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {a b : GBranch G.tree} (hHVC : IsHVC G.molecule S a b)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch H.tree → Mom d)
    (κ : GardenDart H → (Fin d → ℤ)) (hκ : H.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ v ∈ H.molecule.atoms, H.molecule.deg v = 4 → charge v = 0) :
    groupGapKind H scale γ η base κ (F.img S) =
      groupGapKind G scale γ η base (κ ∘ F.d) S := by
  obtain ⟨P, hP, ha⟩ := designatedObject_atoms hS ⟨a, b, Or.inr (Or.inr hHVC)⟩
  obtain ⟨Q, hQ, hb⟩ := designatedObject_atoms (F.maximalGroups_img hS)
    ⟨F.e a, F.e b, Or.inr (Or.inr (F.isHVC_img hHVC))⟩
  have hat : (mapObject F P).atoms = Q.atoms := by
    change F.img P.atoms = Q.atoms
    rw [ha, hb]
  have htarget : IsHVC H.molecule (mapObject F P).atoms (F.e a) (F.e b) := by
    change IsHVC H.molecule (F.img P.atoms) (F.e a) (F.e b)
    rw [ha]
    exact F.isHVC_img hHVC
  have hi := objects_gapKind_iff_of_HVC (Mole.garden_isMolecule H) (mapObject F P) Q hat htarget
    scale γ η base charge κ hκ hc0
  obtain ⟨kind, hkind⟩ := exists_hasGapKind Q scale γ η base κ
  have hPk : P.HasGapKind scale γ η base (κ ∘ F.d) kind :=
    (mapObject_gapKind F P scale γ η base κ kind).mp ((hi kind).mpr hkind)
  exact (groupGapKind_eq scale γ η base κ hQ hkind).trans
    (groupGapKind_eq scale γ η base (κ ∘ F.d) hP hPk).symm

end WaveTurbulence.VineA
