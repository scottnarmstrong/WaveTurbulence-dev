/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.GluedMatchingEdges
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListMembership

/-! # Independent native fibers glue to actual fixed-root garden decorations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem glueRelativeLabels_sourcePair {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s)
    (q : Pair w) (hq : q ∈ sourcePairs (D.garden hS))
    (x y : GNode (D.forest hS)) (hx : x.1 = q.1) (hy : y.1 = q.2) :
    glueRelativeLabels D hS κ ρ x = glueRelativeLabels D hS κ ρ y := by
  have hs := congrArg Raw.pairs (D.garden_raw hS)
  change sourcePairs (D.garden hS) = D.attachmentPairs hS at hs
  rw [hs,← D.pairList_toFinset hS] at hq
  rcases D.pairList_mem_cases hS q (List.mem_toFinset.mp hq) with ⟨p,hp⟩ | ⟨b,hb⟩
  · exact glueRelativeLabels_couple_edge D hS κ ρ p q hp x y hx hy
  · exact glueRelativeLabels_chain_edge D hS κ ρ b q hb x y hx hy

/-- TARGET regred: no matching equation is supplied for the full garden.
It follows from the exact native pair lists of the reconstruction. -/
theorem glueRelativeLabels_isDecoration {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ)) (hκ : IsDecoration S κ)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    IsDecoration (D.garden hS) (glueRelativeLabels D hS κ ρ) := by
  refine ⟨glueRelativeLabels_conservation D hS κ hκ ρ,?_⟩
  intro ℓ
  rcases sourcePairs_partner (D.garden hS) (D.garden_plain hS) ℓ with hp | hp
  · exact glueRelativeLabels_sourcePair D hS κ ρ _ hp ℓ.toNode ((D.garden hS).pair ℓ).toNode rfl rfl
  · exact (glueRelativeLabels_sourcePair D hS κ ρ _ hp ((D.garden hS).pair ℓ).toNode ℓ.toNode rfl rfl).symm

noncomputable def glueGenDecoration {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    GenDecoration (D.garden hS) d n nfl :=
  ⟨glueRelativeLabels D hS κ.1 ρ,glueRelativeLabels_isDecoration D hS κ.1 κ.2.1 ρ,
    fun j => (congrArg (glueRelativeLabels D hS κ.1 ρ) (attachedNode_root D hS j)).symm.trans
      ((glueRelativeLabels_attached D hS κ.1 κ.2.1 ρ _).trans (κ.2.2.1 j)),
    fun ℓ hℓ => (by
      have hm := D.garden_plain hS ℓ
      change (D.garden hS).mark ℓ = some .equal at hℓ
      rw [hℓ] at hm
      contradiction)⟩

theorem collapseGenDecoration_glue {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    collapseGenDecoration D hS (glueGenDecoration D hS κ ρ) = κ :=
  Subtype.ext (funext (fun a => glueRelativeLabels_attached D hS κ.1 κ.2.1 ρ a))

end WaveTurbulence.RegRed
