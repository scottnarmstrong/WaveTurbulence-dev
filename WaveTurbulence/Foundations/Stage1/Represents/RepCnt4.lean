/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt3
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedPiece
import Mathlib.Tactic

/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 4: the clauses `1 ≤ r̄ ≤ N` and `ḡ ≤ N` of the successor piece

For `NormalizedSplice.stage1PieceOf` of a skeleton `S` with `1 ≤ n_sk`, `n_sk ≤ N` (and `n_sk + |D| ≤ N` for `ḡ`):
* `n_sb + #hinges ≤ n_sk` (each unit has at least two atoms, one crown per unit);
* `r̄ = ρ_sb + #hinges ≤ n_sb + #hinges ≤ N`, `1 ≤ r̄`;
* `ḡ = g_reg + Σ vineIncoh + g_sb ≤ |D|/2 + (n_sb + Σ_u (|u| - 1)) ≤ N`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.Mole

variable {R : ℕ}

/-- The successor piece has the same `ḡ` as the original producer's piece (the definitions agree). -/
theorem normalized_gbar_eq (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (VineA.NormalizedSplice.stage1PieceOf d hS LG hd σ).gbar = (RedSplice.stage1PieceOf d hS LG hd σ).gbar := rfl

theorem normalized_rbar_eq (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (VineA.NormalizedSplice.stage1PieceOf d hS LG hd σ).rbar = (RedSplice.stage1PieceOf d hS LG hd σ).rbar := rfl

theorem stage1Piece_rbar_bounds (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hn : 1 ≤ S.order) (hN : S.order ≤ N) :
    1 ≤ (VineA.NormalizedSplice.stage1PieceOf d hS LG hd σ).rbar ∧
      (VineA.NormalizedSplice.stage1PieceOf d hS LG hd σ).rbar ≤ N := by
  have hM : S.molecule.IsMolecule := Mole.garden_isMolecule S
  have hMsb : (stSt S σ).G.molecule.IsMolecule := Mole.garden_isMolecule _
  have hpos : 1 ≤ (stSt S σ).G.order := (stSt S σ).M.order_pos (stSt S σ).hcls hn
  have hat : (stSt S σ).G.molecule.atoms.card = (stSt S σ).G.order := garden_card_atoms _
  have h1 := rho_le_atoms hMsb
  have h2 := one_le_rho (M := (stSt S σ).G.molecule) (by omega)
  have h3 := order_add_hinges_le hM σ
  show 1 ≤ (stSt S σ).G.molecule.rho + (stSt S σ).hinges.card ∧ (stSt S σ).G.molecule.rho + (stSt S σ).hinges.card ≤ N
  omega

theorem stage1Piece_gbar_le (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {N : ℕ}
    (hN : S.order + D.size ≤ N) :
    (VineA.NormalizedSplice.stage1PieceOf d hS LG hd σ).gbar ≤ N := by
  have hM : S.molecule.IsMolecule := Mole.garden_isMolecule S
  have hMsb : (stSt S σ).G.molecule.IsMolecule := Mole.garden_isMolecule _
  have hat : (stSt S σ).G.molecule.atoms.card = (stSt S σ).G.order := garden_card_atoms _
  have h1 := sum_vineIncoh_le_units hM σ (RegRed.coreLayer LG D hS hd)
  have h2 := totalIncoherency_le_atoms hMsb (ladderDataOf (stSt S σ).G)
    ((stSt S σ).layer (RegRed.coreLayer LG D hS hd))
  have h3 := order_add_units_le hM σ
  have h4 := two_mul_gregOf_le D hS LG
  show gskOf (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) +
    (ladderDataOf (stSt S σ).G).totalIncoherency ((stSt S σ).layer (RegRed.coreLayer LG D hS hd)) ≤ N
  unfold gskOf
  omega

end WaveTurbulence.Represents
