/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineAExports
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the producer, part 1 (prime data, decoration transport, selection)

* `layered_eq_reconstruction`: a layered garden decoded by `D` is `layeredReconstruction D hS layer hLayer`.
* `PrimeData.gardenEq`, `decCast`: decorations of `LG.garden` are decorations of the reconstructed garden.
* `selAt`: the `σ`-restriction of VINE-A's successor `NormalizedSplice.selOf`, read at a prescribed point.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed

variable {w : ℕ}

theorem layered_eq_reconstruction {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (LG : LayeredGarden w) (hd : D.Decodes hS LG.garden) :
    ∃ (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer),
      layeredReconstruction D hS layer hLayer = LG := by
  obtain ⟨G, _, hu⟩ := D.existsUnique_decodes hS
  have e : LG.garden = D.garden hS := (hu _ hd).trans (hu _ (D.garden_decodes hS)).symm
  rcases LG with ⟨g, l, hl⟩
  dsimp only at e
  subst e
  exact ⟨l, hl, rfl⟩

theorem _root_.WaveTurbulence.VineA.PrimeData.gardenEq {LG : LayeredGarden w} (pr : PrimeData LG) :
    pr.data.garden pr.prime.1 = LG.garden := by
  obtain ⟨G, _, hu⟩ := pr.data.existsUnique_decodes pr.prime.1
  exact (hu _ (pr.data.garden_decodes pr.prime.1)).trans (hu _ pr.decodes).symm

/-- A decoration of `LG.garden` as a decoration of the reconstructed garden of its prime data. -/
def decCast {LG : LayeredGarden w} (pr : PrimeData LG) {d : ℕ} {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration LG.garden d roots 0) : GenDecoration (pr.data.garden pr.prime.1) d roots 0 :=
  pr.gardenEq.symm ▸ κ

/-- The `σ`-restriction (VINE-A's successor `selOf`) of the skeleton decoration collapsed from `κ`. -/
def selAt (P : WTParams) (base : Mom P.d) {roots : Fin w → (Fin P.d → ℤ)} {LG : LayeredGarden w}
    (pr : PrimeData LG) (σ : GroupPrescription pr.skeleton) (κ : GenDecoration LG.garden P.d roots 0) : Prop :=
  NormalizedSplice.selOf σ P.L P.γ P.η base (collapseGenDecoration pr.data pr.prime.1 (decCast pr κ)).1

theorem selAt_exists_unique (P : WTParams) (base : Mom P.d) {roots : Fin w → (Fin P.d → ℤ)}
    {LG : LayeredGarden w} (pr : PrimeData LG) (κ : GenDecoration LG.garden P.d roots 0) :
    ∃! σ : GroupPrescription pr.skeleton, selAt P base pr σ κ :=
  NormalizedSplice.exists_unique_prescription P.L P.γ P.η base _

end WaveTurbulence.Represents
