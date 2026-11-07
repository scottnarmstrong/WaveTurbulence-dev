/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal2

/-!
# S2 REPRESENTS: pair-type families (AMEND6′, design P*) on the vine-free pieces

`U.toLF` is a leaf family; `U.Bounded p` gives leafwise control on every canonical garden of `𝒢_{p+1}` (all layers
`≤ p`, `Canon.layer_le_of_isCanonGC`), so the vine-free representation `NoVineRepresentsAt` applies to `U.toLF`
verbatim (`noVine_typeFamily`), and in the amended `RepresentsIntA` form (`noVine_typeFamilyA`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set

/-- A bounded pair-type family is leafwise controlled on every canonical garden of `𝒢_{p+1} ∪ 𝒞_{p+1}`. -/
theorem typeFamily_controlled {P : WTParams} {w p : ℕ} (U : TypeFamily P w) (hU : U.Bounded p)
    (LG : LayeredGarden w) (hc : IsCanonGC (p + 1) LG) : U.toLF.Controlled LG := by
  intro i ℓ _
  have hlay : LG.layer ℓ.toNode ≤ p := Canon.layer_le_of_isCanonGC hc _
  rw [show (U.toLF.H LG i) ℓ.1 = U.h i (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 from
    typeProfiles_leaf LG (U.h i) ℓ]
  exact hU i _ _ _ hlay

/-- `NoVineRepresentsAt` for a pair-type family, in the amended (AMEND9) form. -/
theorem noVine_typeFamilyA {P : WTParams} (hP : NoVineRepresentsAt P) (hL : 1 ≤ P.L) (hC : 0 ≤ P.C₁)
    (R : ℕ) (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ)
    (hp : p < P.D) (hN : D.size ≤ P.N (p + 1) ^ 4)
    (hcan : IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (U : TypeFamily P (2 * R)) (hU : U.Bounded p)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (σ : Prescription S)
    (hσ : unitBlocks S σ = []) (hM : S.molecule.IsMolecule)
    (n : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : U.toLF.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s)
    (hn : n - S.order = D.size) :
    Stage1Piece.RepresentsIntA (P := P)
      (stage1PieceOf P.d hS (RegRed.layeredReconstruction D hS layer hLayer) (D.garden_decodes hS) σ)
      n tt base roots s
      (U.toLF.valueSel tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
        (fun κ => selOf (GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS κ).1)) :=
  Stage1Piece.representsIntA_of_representsInt _ _ _ _ _ _ _ hL hC hs0
    (hP R S D hS layer hLayer p hp hN hcan tt htt U.toLF (typeFamily_controlled U hU _ hcan) base roots σ hσ hM
      n s hs hn)

end WaveTurbulence.Represents
