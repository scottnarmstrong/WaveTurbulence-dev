/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceLeafPieces

/-! # Equality of the actual source spliced gardens under a unit twist

TARGET twistexplain (c): ordered trees, signatures, leaf pairings, and
marks agree. This theorem compares the accepted concrete CL construction.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The actual retained-leaf pullbacks commute with the concrete unit-twist bijection. -/
theorem unitTwist_spliceLeaf_diagram (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (l : GLeaf (originalSplicedGarden G P hB hCL D).tree) :
    coreLeafEquiv G P (Mole.spliceLeafEquiv (originalSpliceBoundary G P hB hCL D) l).1 =
      (Mole.spliceLeafEquiv (twistedSpliceBoundary G P hB hCL hP D)
        (forestLeafCast (unitTwist_splicedForest G P hB hCL hP D).symm l)).1 := by
  obtain ⟨p,rfl⟩ := Mole.splicePieceNew_surjective (originalSpliceBoundary G P hB hCL D) l
  have he : forestLeafCast (unitTwist_splicedForest G P hB hCL hP D).symm
      (Mole.splicePieceNew (originalSpliceBoundary G P hB hCL D) p) =
    Mole.splicePieceNew (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceLeafPiece G P hB hCL hP D p) :=
      Subtype.ext (twistedSpliceLeafPiece_new_val G P hB hCL hP D p).symm
  have h₀ := spliceLeafEquiv_piece (originalSpliceBoundary G P hB hCL D) p
  have h₁ := spliceLeafEquiv_piece (twistedSpliceBoundary G P hB hCL hP D)
    (twistedSpliceLeafPiece G P hB hCL hP D p)
  have hc := congrArg (fun z => (Mole.spliceLeafEquiv (twistedSpliceBoundary G P hB hCL hP D) z).1) he
  exact (congrArg (coreLeafEquiv G P) h₀).trans
    ((twistedSpliceLeafPiece_old G P hB hCL hP D p).trans (h₁.symm.trans hc.symm))

/-- The two actual accepted CL-spliced gardens are literally equal. -/
theorem unitTwist_splicedGarden (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    twistedSplicedGarden G P hB hCL hP D = originalSplicedGarden G P hB hCL D := by
  unfold twistedSplicedGarden originalSplicedGarden Mole.clSplicedGardenOfSlots
  exact spliceTransport_eq_of_diagram G (unitTwistGarden G P) _ _ _ _ _ _ _ _ rfl
    (unitTwist_splicedForest G P hB hCL hP D) (coreLeafEquiv G P) (unitTwistGarden_pair G P)
    (unitTwistGarden_mark G P) (unitTwist_spliceLeaf_diagram G P hB hCL hP D)

/-- The justified CL child-slot choices are unique, so canonical splicing uses the same slots. -/
theorem clSpliceSlots_unique {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D E : Mole.CLSpliceSlots G S a b) : D = E := by
  have he : D.excluded = E.excluded := by
    by_contra hn
    exact D.excluded_missing ((E.upper D.excluded).mpr hn)
  have hk : D.kept = E.kept := (E.lower D.kept).mp ((D.lower D.kept).mpr rfl)
  cases D
  cases E
  cases he
  cases hk
  rfl

/-- TARGET twistexplain (c), for the literal canonical source CL-splicing functions. -/
theorem unitTwist_canonicalSplice (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P) :
    Mole.clSplicedGarden (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP) =
    Mole.clSplicedGarden hB hCL := by
  let D := Mole.clSpliceSlotsOfBlock hB hCL
  have he := unitTwist_splicedGarden G P hB hCL hP D
  have hslots := clSpliceSlots_unique
    (Mole.clSpliceSlotsOfBlock (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP)) (twistedSpliceSlots G P hB hCL hP D)
  change Mole.clSplicedGardenOfSlots _ _ _ = _
  exact (congrArg (Mole.clSplicedGardenOfSlots
    (isBlock_twistedAtoms G P hB)
    (clParentPattern_twistedAtoms G P hB hCL hP)) hslots).trans he

end WaveTurbulence.Twist
