/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EqCount
public import WaveTurbulence.Foundations.FinalCount.BridgeSplit
import Mathlib.Tactic

/-! # The normalized count through a two-exit removal with equal exit labels

`𝔄(N; Adm) ≤ |scaleSet|² (log L)^{12} · 𝔄*(N[Y]) · 𝔄*(post)`: no loss in the constant `C₁` (the circuit ranks add exactly,
`χ(N) = χ(N[Y]) + χ(post)`, since `N`, `N[Y]` and the post molecule are connected), and the per-position ladder factors
compare as in `TwoExit.cellProduct_le`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace EqPost
variable {N : Molecule V D} (T : TwoExit N)

theorem countAFree_le_eq
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S)
    (hconnN : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v)
    (hconnY : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) {d : ℕ} {L γ δ η C1 : ℝ}
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 < δ) (hC1 : 0 < C1) (P : Finset V → ℝ)
    (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ) (hEq : ∀ κ, Adm κ → (∀ z, κ (N.mate z) = κ z) → κ T.x = κ T.y) :
    MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
        AFreeSup (piece N T.Y) d L γ δ η C1 * AFreeSup T.post d L γ δ η C1 := by
  classical
  have hLp : 0 < L := by linarith
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  set fam := T.scaleFamily L P
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm)
  have hcount := countEFree_le_eq T hloop hdeg hopen (d := d) hL hδ P Adm hAdm hEq
  have hsupeq : (⨆ P' ∈ fam, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P')) =
      fam.sup (fun P' => MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P')) := by
    rw [Finset.sup_eq_iSup]
  rw [hsupeq] at hcount
  rcases fam.eq_empty_or_nonempty with hfe | hfne
  · rw [hfe, Finset.sup_empty, bot_eq_zero, mul_zero] at hcount
    rw [MoleProp.countAFree_eq_normalization, nonpos_iff_eq_zero.mp hcount]
    simp
  obtain ⟨P0, hP0, hmax⟩ := exists_mem_eq_sup fam hfne
    (fun P' => MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P'))
  rw [hmax] at hcount
  have hP0nn := T.scaleFamily_nonneg hP0 (fun S hS hc => hP S (by
    have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N hcell.1), hcell.1⟩))
  have hagree := T.scaleFamily_agree hP0
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := by
    intro S hS; rw [T.ladderCells_piece_eq] at hS; exact hP S (mem_filter.mp hS).1
  have np := MoleProp.freeNormalization_pos (piece N T.Y) (d := d) (γ := γ) hLp hδ hC1 hlog0 P hPpiece
  have nq := MoleProp.freeNormalization_pos T.post (d := d) (γ := γ) hLp hδ hC1 hlog0 P0 hP0nn
  have hcells := T.cellProduct_le (γ := γ) hloop hdeg hLp.le hδ.le hlog P P0 hP hP0nn hagree
  -- ranks add
  have hrank := T.circuitRank_identity
  have hFN : N.numComponents = 1 := Mole.numComponents_eq_one N
    ⟨N.atom T.x, N.atom_mem _⟩ hconnN
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one (piece N T.Y)
    (by rw [piece_atoms T.sub]; exact ⟨N.atom T.x, T.atom_x⟩) (by rw [piece_atoms T.sub]; exact hconnY)
  have hFq : T.post.numComponents = 1 := Mole.numComponents_eq_one T.post
    (by rw [T.post_atoms]; exact ⟨T.c, T.c_mem⟩) (T.post_connected hconnN)
  rw [hFN, hFp, hFq] at hrank
  have hrk : N.circuitRank = (piece N T.Y).circuitRank + T.post.circuitRank := by
    push_cast at hrank; omega
  have hbne : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hnorm : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1 P *
        MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 * (Real.log L ^ 2) ^ 6 := by
    unfold MoleProp.freeNormalization
    have hsplit := norm_split (L := L) (a := (d : ℝ) - γ) hLp hbne hrk (MoleProp.cellProduct (piece N T.Y) L γ δ P *
      MoleProp.cellProduct T.post L γ δ P0) (MoleProp.cellProduct (piece N T.Y) L γ δ P)
      (MoleProp.cellProduct T.post L γ δ P0) rfl
    have hAN : 0 ≤ L ^ (-((d : ℝ) - γ) * (N.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ N.circuitRank := by
      positivity
    calc L ^ (-((d : ℝ) - γ) * (N.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ N.circuitRank *
          MoleProp.cellProduct N L γ δ P
        ≤ L ^ (-((d : ℝ) - γ) * (N.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ N.circuitRank *
          (MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct T.post L γ δ P0 *
            (Real.log L ^ 2) ^ 6) := mul_le_mul_of_nonneg_left hcells hAN
      _ = (L ^ (-((d : ℝ) - γ) * (N.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ N.circuitRank *
          (MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct T.post L γ δ P0)) *
            (Real.log L ^ 2) ^ 6 := by ring
      _ = _ := by rw [hsplit]
  -- assemble
  have h1 := afree_le_afreeSup (piece N T.Y) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) P hPpiece
  have h2 := afree_le_afreeSup T.post (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) P0 hP0nn
  have hmonoP : MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) ≤
      MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (lgAdm (piece N T.Y) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, h0, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase N L γ η 0 _ (hAdm κ0 h0).1,
        MoleProp.cellGapRestriction_erase N L 0 _ P _ (hAdm κ0 h0).2⟩
  have hfam : ((fam.card : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((scaleSet L).card ^ 2) := by
    have := T.card_scaleFamily_le hloop hdeg L P
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast this)
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((fam.card : ℕ∞) * F * MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P0) : ℕ∞) *
          ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1 P *
            MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 * (Real.log L ^ 2) ^ 6) :=
        mul_le_mul' (ENat.toENNReal_mono hcount) (ENNReal.ofReal_le_ofReal hnorm)
    _ = (((fam.card : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal ((Real.log L ^ 2) ^ 6)) *
          ((F : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1 P)) *
          ((MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P0) : ℝ≥0∞) *
            ENNReal.ofReal (MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0)) := by
        rw [ENat.toENNReal_mul, ENat.toENNReal_mul, ENNReal.ofReal_mul (mul_nonneg np.le nq.le),
          ENNReal.ofReal_mul np.le]
        ring
    _ ≤ (ENNReal.ofReal ((scaleSet L).card ^ 2) * ENNReal.ofReal ((Real.log L ^ 2) ^ 6)) *
          (AFreeSup (piece N T.Y) d L γ δ η C1) * (AFreeSup T.post d L γ δ η C1) := by
        refine mul_le_mul' (mul_le_mul' (mul_le_mul' hfam le_rfl) ?_) ?_
        · refine le_trans ?_ h1
          unfold AFree
          rw [MoleProp.countAFree_eq_normalization]
          exact mul_le_mul' (ENat.toENNReal_mono hmonoP) le_rfl
        · refine le_trans ?_ h2
          unfold AFree
          rw [MoleProp.countAFree_eq_normalization]
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end EqPost
end WaveTurbulence.FinalCountG8
