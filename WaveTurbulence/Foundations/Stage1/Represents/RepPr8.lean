/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr5
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr7
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `RepresentsIntA` of the vine-free pieces of the successor producer

`noVine_representsIntA`: for a prescribed prime point `b` of a canonical garden with no unit (`unitBlocks = []`), the successor piece
`b.normalizedPiece` carries the `RepresentsIntA` of `F.valueSel b.layered (selAt …)`, from `NoVineRepresentsAtN`
(`represents_noVineN`), at the layered reconstruction of `b`'s prime data (`layered_eq_reconstruction`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA

theorem noVineN_at (P : WTParams) (hP : NoVineRepresentsAtN P) {R : ℕ} {S : Garden (2 * R)}
    (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden)
    (hg : D.garden hS = LG.garden) (σ : Prescription S) (hnv : unitBlocks S σ = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : LG.garden.order = N)
    (hcan : IsCanonGC (p + 1) LG)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled LG)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size LG ≤ s) :
    Stage1Piece.RepresentsIntA (P := P) (NormalizedSplice.stage1PieceOf P.d hS LG hd σ) N tt base roots s
      (F.valueSel tt base roots LG (fun κ =>
        NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS (hg ▸ κ)).1)) := by
  classical
  obtain ⟨layer, hLayer, he⟩ := layered_eq_reconstruction D hS LG hd
  subst he
  have hsz := D.decoded_order hS hd
  exact hP R S D hS layer hLayer p hp (by omega) hcan tt htt F hF base roots σ hnv
    (Mole.garden_isMolecule _) N s hs (by omega)

theorem noVine_representsIntA (P : WTParams) (hP : NoVineRepresentsAtN P) {R : ℕ}
    (b : PrescribedPrimeGarden (2 * R)) (hnv : unitBlocks b.prime.skeleton b.totalSigma = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : b.layered.garden.order = N)
    (hcan : IsCanonGC (p + 1) b.layered)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled b.layered)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size b.layered ≤ s) :
    Stage1Piece.RepresentsIntA (P := P) (b.normalizedPiece P.d) N tt base roots s
      (F.valueSel tt base roots b.layered (fun κ => selAt P base b.prime b.sigma κ)) := by
  have h := noVineN_at P hP b.prime.data b.prime.prime.1 b.layered b.prime.decodes b.prime.gardenEq
    b.totalSigma hnv hp hNb hord hcan tt htt F hF base roots s hs
  have e : NormalizedSplice.GroupPrescription.ofPrescription b.totalSigma = b.sigma :=
    of_extendGroupPrescription b.sigma
  rw [e] at h
  exact h

end WaveTurbulence.Represents
