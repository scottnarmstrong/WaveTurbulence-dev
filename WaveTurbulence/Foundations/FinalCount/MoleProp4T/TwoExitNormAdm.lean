/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNorm
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCountAdm
import Mathlib.Tactic

/-! # The normalized (Y2) bound for any admissibility below `lgAdm`

As `TwoExit.countAFree_le_of_piece`, with `N`'s decorations restricted by `Adm ⊆ lgAdm` and the post side by the
images `postAdm` of `Adm` (supremum also over the multiplier `g`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The two-exit removal bound** (conditional on the piece bound `hpiece`, i.e. DH23 Prop 10.1 for the removed
part with constant `C₁' ≤ C₁/2`). -/
theorem countAFree_le_of_piece_adm
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hdegY : ∀ v ∈ T.Y, N.deg v = 4) (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η C1 C1' : ℝ}
    (hγd : γ ≤ d) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC1' : 1 ≤ C1') (hC : 2 * C1' ≤ C1) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ) (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (hW : ∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) →
      ∃ g ∈ Finset.Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ W g κ)
    (hpiece : MoleProp.countAFree (piece N T.Y) L γ δ C1' (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P ≤ 1) :
    MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
        ⨆ g ∈ Finset.Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
          MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g) P' := by
  classical
  have hLp : 0 < L := by linarith
  have hC1 : 0 < C1 := by linarith
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  set fam := T.scaleFamily L P
  set M : ℕ := 5 * T.windowK ^ 2 * fam.card
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm)
  have hcount := T.countEFree_le_adm hloop hdeg hopen (d := d) hL hδ P (γ := γ) Adm hAdm W hW
  -- the supremum over the finite family is attained
  set idx2 := Finset.Icc (0 : ℤ) 4 ×ˢ fam
  have hsupeq : (⨆ g ∈ Finset.Icc (0 : ℤ) 4, ⨆ P' ∈ fam,
      MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g)) =
      idx2.sup (fun p => MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) p.2 p.1)) := by
    rw [Finset.sup_eq_iSup]
    refine le_antisymm (iSup₂_le fun g hg => iSup₂_le fun P' hP' => ?_) (iSup₂_le fun p hp => ?_)
    · exact le_iSup₂_of_le (f := fun p (_ : p ∈ idx2) => MoleProp.countEFree T.post L γ δ (0 : Mom d)
        (T.postAdm Adm W L γ (η / 2) p.2 p.1)) (g, P') (mem_product.mpr ⟨hg, hP'⟩) le_rfl
    · obtain ⟨hg, hP'⟩ := mem_product.mp hp
      refine le_iSup₂_of_le (f := fun g (_ : g ∈ Finset.Icc (0 : ℤ) 4) => ⨆ P' ∈ fam,
        MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g)) p.1 hg ?_
      exact le_iSup₂_of_le (f := fun P' (_ : P' ∈ fam) => MoleProp.countEFree T.post L γ δ (0 : Mom d)
        (T.postAdm Adm W L γ (η / 2) P' p.1)) p.2 hP' le_rfl
  rw [hsupeq] at hcount
  rcases idx2.eq_empty_or_nonempty with hfe | hfne
  · rw [hfe, Finset.sup_empty, bot_eq_zero, mul_zero] at hcount
    rw [MoleProp.countAFree_eq_normalization, nonpos_iff_eq_zero.mp hcount]
    simp
  obtain ⟨⟨g0, P0⟩, hgP0, hmax⟩ := exists_mem_eq_sup idx2 hfne
    (fun p => MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) p.2 p.1))
  obtain ⟨hg0, hP0⟩ := mem_product.mp hgP0
  rw [hmax] at hcount
  -- normalizations
  have hP0nn := T.scaleFamily_nonneg hP0 (fun S hS hc => hP S (by
    have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N hcell.1), hcell.1⟩))
  have hagree := T.scaleFamily_agree hP0
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := by
    intro S hS; rw [T.ladderCells_piece_eq] at hS; exact hP S (mem_filter.mp hS).1
  have np := MoleProp.freeNormalization_pos (piece N T.Y) (d := d) (γ := γ) hLp hδ (by linarith : (0 : ℝ) < C1') hlog0 P hPpiece
  have nq := MoleProp.freeNormalization_pos T.post (d := d) (γ := γ) hLp hδ hC1 hlog0 P0 hP0nn
  have hcells := T.cellProduct_le (γ := γ) hloop hdeg hLp.le hδ.le hlog P P0 hP hP0nn hagree
  have hrank := T.circuitRank_identity
  have hFle := T.post_numComponents_le
  have hpr := T.piece_circuitRank hdegY hconn
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one (piece N T.Y)
    (by rw [piece_atoms T.sub]; exact ⟨N.atom T.x, T.atom_x⟩) (by rw [piece_atoms T.sub]; exact hconn)
  have hratio : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1' P *
        MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 *
          ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6) := by
    unfold MoleProp.freeNormalization
    rw [← hpr]
    exact norm_ratio hL (by linarith) hδ hδ1 hC1' hC (by rw [hFp] at hrank; omega) (by rw [hpr]; positivity)
      (MoleProp.cellProduct_pos _ hLp.le hδ.le hlog0 P hPpiece).le
      (MoleProp.cellProduct_pos _ hLp.le hδ.le hlog0 P0 hP0nn).le (by positivity) hcells
  -- assemble
  have hconst : (M : ℝ) * ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6) ≤
      110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 := by
    have hfam : (fam.card : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := by
      exact_mod_cast T.card_scaleFamily_le hloop hdeg L P
    have hK := sq_le_twentytwo_mul_two_pow T.Y.card
    have h2 : (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * 2 ^ T.Y.card = 1 := by
      rw [zpow_natCast, ← mul_pow]; norm_num
    have hW : (T.windowK : ℝ) = ((1 + 4 * T.Y.card : ℕ) : ℝ) := rfl
    have hlog6 : 0 ≤ (Real.log L ^ 2) ^ 6 := by positivity
    have hhalf : 0 ≤ (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) := by positivity
    simp only [M]; push_cast
    rw [hW]
    have hKh : ((1 + 4 * T.Y.card : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) ≤ 22 := by
      calc ((1 + 4 * T.Y.card : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ)
          ≤ 22 * 2 ^ T.Y.card * (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) := mul_le_mul_of_nonneg_right hK hhalf
        _ = 22 := by rw [mul_assoc, mul_comm ((2 : ℝ) ^ T.Y.card), h2, mul_one]
    calc 5 * ((1 + 4 * T.Y.card : ℕ) : ℝ) ^ 2 * (fam.card : ℝ) * ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) *
          (Real.log L ^ 2) ^ 6)
        = 5 * (((1 + 4 * T.Y.card : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ)) * (fam.card : ℝ) *
            (Real.log L ^ 2) ^ 6 := by ring
      _ ≤ 5 * 22 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 := by gcongr
      _ = _ := by ring
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((M : ℝ≥0∞) * F * MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P0 g0)) *
          ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1' P *
            MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 *
              ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6)) := by
        refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal hratio)
        have hc' : MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
            (M : ℕ∞) * F * MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P0 g0) := by
          simpa only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcount
        have h1 := ENat.toENNReal_mono hc'
        rw [ENat.toENNReal_mul, ENat.toENNReal_mul, ENat.toENNReal_coe] at h1
        exact h1
    _ = ((F : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1' P)) *
          (MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P0 g0) P0) *
            ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6)) := by
        rw [MoleProp.countAFree_eq_normalization, ENNReal.ofReal_mul (mul_nonneg np.le nq.le),
          ENNReal.ofReal_mul np.le, ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
        ring
    _ ≤ 1 * (⨆ g ∈ Finset.Icc (0 : ℤ) 4, ⨆ P' ∈ fam,
          MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g) P') *
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) := by
        gcongr
        · exact hpiece
        · refine le_iSup₂_of_le (f := fun g (_ : g ∈ Finset.Icc (0 : ℤ) 4) => ⨆ P' ∈ fam,
            MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g) P') g0 hg0 ?_
          exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countAFree T.post L γ δ C1 (0 : Mom d)
            (T.postAdm Adm W L γ (η / 2) P' g0) P') P0 hP0 le_rfl
    _ = _ := by ring

end TwoExit
end WaveTurbulence.MoleProp4
