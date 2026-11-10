/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproFinal2
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceFinalR83
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceAmend7R83
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproFinal2R83
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedPiece
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `Stage1Piece.Sound` of VINE-A's successor producer, unconditionally

The successor of `RepGlue.stage1Piece_sound_uncond` (`RedSplice.stage1Piece_sound` rebuilt with the R83
`construction_facts`, `tripleDesignated_collectionChoices`, `hingeNoLoop_collectionChoices`; the S4 obligation is
FLOWER-P6's R83 port `VineA.NormalizedSplice.Subpro.subproObligationA`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open TTree Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton

variable {R : ℕ}

theorem stage1Piece_sound_succ_uncond (P : WTParams) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : RedSplice.Prescription S)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1Piece.Sound (P := P) (VineA.NormalizedSplice.stage1PieceOf P.d hS LG hd σ) p base roots := by
  obtain ⟨hB, hStr, hHinge⟩ := VineA.NormalizedSplice.construction_facts S hP hI hbal hn σ (RegRed.coreLayer LG D hS hd) p
    (P.N (p + 1) ^ 4) hN hlayer
  have hsub := VineA.NormalizedSplice.Subpro.subproObligationA P hS LG hd σ hP hI hbal hn p hN hlayer hL base roots
  exact
    { plain := hB.plain
      irreducible := hB.irreducible
      balanced := hB.balanced
      order_pos := hB.order_pos
      order_le := hB.order_le
      layer_le := hB.layer_le
      molecule := hB.molecule
      connected := hB.connected
      atom_count := hB.atom_count
      bond_count := hB.bond_count
      structural := hStr
      support := fun z h1 h2 => by
        have h := hsub z h1 h2
        exact ⟨h.selectedSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩
      hingeOutsideFirst := hHinge
      tripleDesignated :=
        VineA.NormalizedSplice.tripleDesignated_collectionChoices (Mole.garden_isMolecule S) (RedSplice.prime_noTriple S hP) σ
      hingeNoLoop := VineA.NormalizedSplice.hingeNoLoop_collectionChoices σ }

end WaveTurbulence.Represents
