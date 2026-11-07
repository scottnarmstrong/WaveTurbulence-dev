/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG15
import Mathlib.Tactic

/-!
# S2 REPRESENTS, `Stage1Counts` item 3, part 1: the vine part of `g_sk`

* `realized_two_mul_add_two_le`: a vine with atom set `S` has `2 * incoherency + 2 ≤ |S|` (the groups have two or three atoms and
  are disjoint, TARGET cohmol);
* `sum_pieces_atoms`: the atom sets of the pieces of a chain assembly of `U` satisfy `Σ (|T_i| - 1) + 1 = |U|`;
* `sum_pieces_incoh_le`: the incoherency indices of the pieces of a chain assembly sum to at most `|U| - 1`;
* `sum_vineIncoh_le_units`: `Σ_{T ∈ unitIngredients S σ} vineIncoh T ≤ Σ_{u ∈ unitBlocks S σ} (|u.atoms| - 1)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Stage1 WaveTurbulence.Vine
  WaveTurbulence.VineA

theorem realized_two_mul_add_two_le {V D L : Type*} [DecidableEq V] [Fintype D] [DecidableEq L] {M : Molecule V D}
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b) (layer : V → L) :
    2 * realizedIncoherencyIndex R layer + 2 ≤ S.card := by
  have hc : S.card = (X.expand R.k).n := by
    rw [← Finset.card_image_of_injOn R.injOn, R.image_eq, Finset.card_range]
  have h2 := expand_atoms_groups X R.k R.length_eq
  have h3 := realized_index_le R layer
  have h4 := expand_groups_exact X R.k R.length_eq
  have h5 : realizedIncoherencyIndex R layer ≤ (X.expand R.k).groups.length := by omega
  rw [hc, h2]
  split_ifs <;> omega

section Assembly
variable {w : ℕ} {G : Garden w}

theorem sum_pieces_atoms {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) :
    ∑ i : Fin n, ((assemblyPieceAt B i).atoms.card - 1) + 1 = U.card ∧ 1 ≤ U.card := by
  induction B with
  | @single U a b X hV R =>
    have h1 : 1 ≤ U.card := Finset.card_pos.mpr ⟨a, hV.1.2.1⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    simp only [assemblyPieceAt]
    omega
  | @append S T a b c n RP B X hT hi hU R ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hbT : b ∈ T := by
      have : b ∈ S ∩ T := by rw [hi]; simp
      exact (Finset.mem_inter.mp this).2
    have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨b, hbT⟩
    have h2 := Finset.card_union_add_card_inter S T
    rw [hi, Finset.card_singleton] at h2
    rw [Fin.sum_univ_succ]
    have e0 : (assemblyPieceAt (CLChainAssembly.append B hT hi hU R) 0).atoms = T := by simp [assemblyPieceAt]
    have es : ∀ j : Fin n, (assemblyPieceAt (CLChainAssembly.append B hT hi hU R) j.succ).atoms =
        (assemblyPieceAt B j).atoms := by intro j; simp [assemblyPieceAt]
    rw [e0]
    simp only [es]
    constructor <;> omega

theorem sum_pieces_incoh_le {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (layer0 : GBranch G.tree → ℕ) :
    ∑ i : Fin n, realizedIncoherencyIndex (pieceRealization B i) layer0 ≤ U.card - 1 := by
  obtain ⟨h1, h2⟩ := sum_pieces_atoms B
  have : ∑ i : Fin n, realizedIncoherencyIndex (pieceRealization B i) layer0 ≤
      ∑ i : Fin n, ((assemblyPieceAt B i).atoms.card - 1) :=
    Finset.sum_le_sum fun i _ => by
      have := realized_two_mul_add_two_le (pieceRealization B i) layer0
      omega
  omega

end Assembly

section Units
variable {w : ℕ} {S : Garden w}

theorem sum_vineIncoh_le_units (hM : S.molecule.IsMolecule) (σ : Prescription S) (layer0 : GBranch S.tree → ℕ) :
    ∑ T ∈ (Set.toFinite (unitIngredients S σ)).toFinset, vineIncoh S layer0 T ≤
      ((unitBlocks S σ).map fun u => u.atoms.card - 1).sum := by
  classical
  refine (sum_vineIncoh_le_cohmol σ (fun j => unitAssembly hM σ j) (hcov_units hM σ) layer0).trans ?_
  have h1 : ∀ j : Fin (unitBlocks S σ).length,
      ∑ i : Fin (unitN σ j), realizedIncoherencyIndex (pieceRealization (unitAssembly hM σ j) i) layer0 ≤
        ((unitBlocks S σ).get j).atoms.card - 1 := fun j => sum_pieces_incoh_le (unitAssembly hM σ j) layer0
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  have h2 := Fin.sum_univ_fun_getElem (unitBlocks S σ) (fun u : CLBlock S => u.atoms.card - 1)
  refine le_of_eq (Eq.trans ?_ h2)
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

end Units
end WaveTurbulence.Represents
