/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesignatedSupport
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.Vine.A.VineCollectionGeometry
/-! Actual chosen gap kinds of ordinary maximal VC groups transport under
molecular relabeling, without a designated-object compatibility hypothesis. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine.SourceVine Represents
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- An ordinary object always has one of the three actual gap kinds. -/
theorem ordinary_object_hasGapKind (O : Object M) (hO : objectHyperTag O = false)
    (scale γ η : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ)) :
    ∃ kind, O.HasGapKind scale γ η base κ kind := by
  cases hs : O.shape with
  | hyper R => simp only [objectHyperTag, hs, Bool.true_eq_false] at hO
  | vc hv =>
    let r := Vine.groupFlow M O.atoms (Molecule.kvec scale base κ) O.upper
    refine ⟨Molecule.gapKind scale γ η r, r, ?_, rfl⟩
    rw [hs]
    exact Vine.block_groupGap_exists M hv.1 _

/-- The actual groupGapKind of an ordinary maximal group is invariant under actual relabeling.
Only the source decoration hypotheses are assumed, not equality of chosen designations. -/
theorem groupGapKind_image_of_VC {w : ℕ} {G H : Garden w} (F : MolIso G.molecule H.molecule)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {a b : GBranch G.tree} (hVC : IsVC G.molecule S a b)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch H.tree → Mom d)
    (κ : GardenDart H → (Fin d → ℤ)) (hκ : H.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ v ∈ H.molecule.atoms, H.molecule.deg v = 4 → charge v = 0) :
    groupGapKind H scale γ η base κ (F.img S) =
      groupGapKind G scale γ η base (κ ∘ F.d) S := by
  obtain ⟨P, hP, ha, htP⟩ := designatedObject_ordinary hS hVC
  obtain ⟨Q, hQ, hb, htQ⟩ := designatedObject_ordinary (F.maximalGroups_img hS) (F.isVC_img hVC)
  have hat : (mapObject F P).atoms = Q.atoms := by
    change F.img P.atoms = Q.atoms
    rw [ha, hb]
  have htag : objectHyperTag (mapObject F P) = false := (mapObject_hyperTag F P).trans htP
  have hi := ordinary_objects_gapKind_iff (Mole.garden_isMolecule H) (mapObject F P) Q hat htag htQ
    scale γ η base charge κ hκ hc0
  obtain ⟨kind, hkind⟩ := ordinary_object_hasGapKind Q htQ scale γ η base κ
  have hPk : P.HasGapKind scale γ η base (κ ∘ F.d) kind :=
    (mapObject_gapKind F P scale γ η base κ kind).mp ((hi kind).mpr hkind)
  exact (groupGapKind_eq scale γ η base κ hQ hkind).trans
    (groupGapKind_eq scale γ η base (κ ∘ F.d) hP hPk).symm

end WaveTurbulence.VineA.NormalizedSplice
