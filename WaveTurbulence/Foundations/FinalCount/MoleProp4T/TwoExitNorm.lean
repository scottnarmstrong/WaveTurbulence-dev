/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitRank
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
import Mathlib.Tactic

/-! # The normalized two-exit bound (DH23 ylem2, (Y2) ending, L1954)

`𝔄(N) ≤ 110 |scaleSet L|² (log L)^{12} · sup_{P'} 𝔄(post)`, assuming the bound `𝔄(N[Y]) ≤ 1` for the piece with the
constant `C₁' ≤ C₁/2` (DH23 Prop 10.1 for the removed ladder, supplied by the caller). The factor `(1/2)^{|Y|}` from
`C₁' ≤ C₁/2` absorbs the window splitting `K² = (1 + 4|Y|)²`; `χ(N) − χ(post) − χ(N[Y]) = F(N) − F(post) ≥ 0`;
the piece of an all-degree-four `Y` with two exits has `χ = |Y|`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sq_le_twentytwo_mul_two_pow (t : ℕ) : ((1 + 4 * t : ℕ) : ℝ) ^ 2 ≤ 22 * 2 ^ t := by
  have key : ∀ t : ℕ, (1 + 4 * t) ^ 2 ≤ 22 * 2 ^ t := by
    intro t
    induction t with
    | zero => norm_num
    | succ n ih =>
      rcases Nat.lt_or_ge n 3 with h | h
      · interval_cases n <;> norm_num
      · have h2 : (1 + 4 * (n + 1)) ^ 2 ≤ 2 * (1 + 4 * n) ^ 2 := by nlinarith
        calc (1 + 4 * (n + 1)) ^ 2 ≤ 2 * (1 + 4 * n) ^ 2 := h2
          _ ≤ 2 * (22 * 2 ^ n) := Nat.mul_le_mul_left 2 ih
          _ = 22 * 2 ^ (n + 1) := by ring
  exact_mod_cast key t

/-- The normalization ratio of a removal: `𝔑(N) ≤ 𝔑'(piece) 𝔑(post) (1/2)^{χ(piece)} Λ`. -/
theorem norm_ratio {L a C1 C1' δ : ℝ} {χN χp χq : ℤ} {cN cp cq Λ : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hC1' : 1 ≤ C1') (hC : 2 * C1' ≤ C1) (he : χq + χp ≤ χN) (hχp : 0 ≤ χp) (hcp : 0 ≤ cp)
    (hcq : 0 ≤ cq) (hΛ : 0 ≤ Λ) (hcN : cN ≤ cp * cq * Λ) :
    L ^ (-a * χN) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χN * cN ≤
      (L ^ (-a * χp) * (C1'⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χp * cp) * (L ^ (-a * χq) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χq * cq) *
        ((1 / 2 : ℝ) ^ χp * Λ) := by
  have hLp : 0 < L := by linarith
  have hC1 : 0 < C1 := by linarith
  set b := C1⁻¹ * δ ^ (1 / 2 : ℝ) with hb
  set b' := C1'⁻¹ * δ ^ (1 / 2 : ℝ) with hb'
  have hs : 0 < δ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hs1 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hbpos : 0 < b := by positivity
  have hC1'p : 0 < C1' := by linarith
  have hb'pos : 0 < b' := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb]
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : 0 < C1⁻¹ := inv_pos.mpr hC1
    nlinarith
  have hbb : b ≤ b' * (1 / 2) := by
    rw [hb, hb']
    have : C1⁻¹ ≤ C1'⁻¹ * (1 / 2) := by
      rw [show C1'⁻¹ * (1 / 2 : ℝ) = (2 * C1')⁻¹ by field_simp]
      exact inv_anti₀ (by linarith) hC
    nlinarith
  set e := χN - χq - χp with hedef
  have he0 : 0 ≤ e := by omega
  have hχ : χN = χp + χq + e := by omega
  -- the power of `L`
  have hLpow : L ^ (-a * χN) = L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) := by
    rw [← Real.rpow_add hLp, ← Real.rpow_add hLp, hχ]; push_cast; ring_nf
  have hLe : L ^ (-a * e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by
    have : (0 : ℝ) ≤ e := by exact_mod_cast he0
    nlinarith)
  -- the power of `b`
  have hbpow : b ^ χN = b ^ χp * b ^ χq * b ^ e := by
    rw [hχ, zpow_add₀ hbpos.ne', zpow_add₀ hbpos.ne']
  have hbe : b ^ e ≤ 1 := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le he0
    rw [hn, zpow_natCast]; exact pow_le_one₀ hbpos.le hb1
  have hbχp : b ^ χp ≤ b' ^ χp * (1 / 2 : ℝ) ^ χp := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hχp
    rw [hn, zpow_natCast, zpow_natCast, zpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ hbpos.le hbb n
  have hLp1 : 0 ≤ L ^ (-a * χp) := (Real.rpow_pos_of_pos hLp _).le
  have hLq1 : 0 ≤ L ^ (-a * χq) := (Real.rpow_pos_of_pos hLp _).le
  have hLe0 : 0 ≤ L ^ (-a * e) := (Real.rpow_pos_of_pos hLp _).le
  have hbq : 0 ≤ b ^ χq := (zpow_pos hbpos _).le
  have hbp : 0 ≤ b ^ χp := (zpow_pos hbpos _).le
  have hb'p : 0 ≤ b' ^ χp := (zpow_pos hb'pos _).le
  have hhalf : 0 ≤ (1 / 2 : ℝ) ^ χp := (zpow_pos (by norm_num) _).le
  have hcN0 : 0 ≤ cN ∨ cN < 0 := le_or_gt 0 cN
  rw [hLpow, hbpow]
  calc L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) * (b ^ χp * b ^ χq * b ^ e) * cN
      ≤ L ^ (-a * χp) * L ^ (-a * χq) * 1 * (b ^ χp * b ^ χq * 1) * (cp * cq * Λ) := by
        rcases hcN0 with h0 | h0
        · gcongr
        · have : L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) * (b ^ χp * b ^ χq * b ^ e) * cN ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
          exact this.trans (by positivity)
    _ ≤ L ^ (-a * χp) * L ^ (-a * χq) * 1 * (b' ^ χp * (1 / 2 : ℝ) ^ χp * b ^ χq * 1) * (cp * cq * Λ) := by
        gcongr
    _ = _ := by ring

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The removed piece has circuit rank `|Y|`** (all atoms of `Y` of degree four, two exits, connected). -/
theorem piece_circuitRank (hdegY : ∀ v ∈ T.Y, N.deg v = 4)
    (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) :
    (piece N T.Y).circuitRank = T.Y.card := by
  classical
  have hne : T.Y.Nonempty := ⟨N.atom T.x, T.atom_x⟩
  have hF : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one (piece N T.Y)
    (by rw [piece_atoms T.sub]; exact hne) (by rw [piece_atoms T.sub]; exact hconn)
  have hsum := Mole.sum_degrees_eq_two_mul_bonds (piece N T.Y)
  rw [piece_atoms T.sub] at hsum
  have hsplit : ∀ v ∈ T.Y, (piece N T.Y).deg v + (Degen.removedDartsAt N (N.atoms \ T.Y) v).card = 4 := by
    intro v hv
    rw [deg_eraseAtoms_add (N := N) (N.atoms \ T.Y) (fun h => (mem_sdiff.mp h).2 hv), hdegY v hv]
  have hcross : ∑ v ∈ T.Y, (Degen.removedDartsAt N (N.atoms \ T.Y) v).card = 2 := by
    have hfib := card_eq_sum_card_fiberwise (s := crossDarts N T.Y) (t := T.Y) (f := N.atom)
      (fun z hz => (mem_crossDarts.mp hz).1)
    rw [T.cross, card_pair T.ne] at hfib
    rw [hfib]
    refine sum_congr rfl fun v hv => congrArg card ?_
    ext z
    simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_sdiff]
    rw [← T.cross]
    simp only [mem_crossDarts]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨⟨hv, h.2⟩, rfl⟩
    · rintro ⟨⟨_, h⟩, rfl⟩; exact ⟨rfl, N.atom_mem _, h⟩
  have htot : ∑ v ∈ T.Y, (piece N T.Y).deg v + 2 = 4 * T.Y.card := by
    rw [← hcross, ← sum_add_distrib, sum_congr rfl hsplit, sum_const, smul_eq_mul, mul_comm]
  unfold Molecule.circuitRank
  rw [hF, piece_atoms T.sub]
  omega

/-- **The two-exit removal bound** (conditional on the piece bound `hpiece`, i.e. DH23 Prop 10.1 for the removed
part with constant `C₁' ≤ C₁/2`). -/
theorem countAFree_le_of_piece (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hdegY : ∀ v ∈ T.Y, N.deg v = 4) (hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η C1 C1' : ℝ}
    (hγd : γ ≤ d) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hL11 : 11 ≤ L ^ (η / 2)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC1' : 1 ≤ C1') (hC : 2 * C1' ≤ C1) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S)
    (hpiece : MoleProp.countAFree (piece N T.Y) L γ δ C1' (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) (lgAdm (d := d) N L γ η P)) P ≤ 1) :
    MoleProp.countAFree N L γ δ C1 (0 : Mom d) (lgAdm N L γ η P) P ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
        ⨆ P' ∈ T.scaleFamily L P, MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (lgAdm T.post L γ (η / 2) P') P' := by
  classical
  have hLp : 0 < L := by linarith
  have hC1 : 0 < C1 := by linarith
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  set fam := T.scaleFamily L P
  set M : ℕ := 5 * T.windowK ^ 2 * fam.card
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) (lgAdm (d := d) N L γ η P))
  have hcount := T.countEFree_le hcap hloop hdeg hopen (d := d) hL hL11 hδ P (γ := γ)
  -- the supremum over the finite family is attained
  rcases fam.eq_empty_or_nonempty with hfe | hfne
  · have hzero : (⨆ P' ∈ fam, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P')) = 0 := by
      rw [hfe]; simp
    rw [hzero, mul_zero] at hcount
    rw [MoleProp.countAFree_eq_normalization, nonpos_iff_eq_zero.mp hcount]
    simp
  obtain ⟨P0, hP0, hmax⟩ := exists_mem_eq_sup fam hfne
    (fun P' => MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P'))
  rw [← Finset.sup_eq_iSup, hmax] at hcount
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
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((M : ℝ≥0∞) * F * MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P0)) *
          ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1' P *
            MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 *
              ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6)) := by
        refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal hratio)
        have hc' : MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) ≤
            (M : ℕ∞) * F * MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P0) := by
          simpa only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcount
        have h1 := ENat.toENNReal_mono hc'
        rw [ENat.toENNReal_mul, ENat.toENNReal_mul, ENat.toENNReal_coe] at h1
        exact h1
    _ = ((F : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ C1' P)) *
          (MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (lgAdm T.post L γ (η / 2) P0) P0) *
            ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ ((T.Y.card : ℕ) : ℤ) * (Real.log L ^ 2) ^ 6)) := by
        rw [MoleProp.countAFree_eq_normalization, ENNReal.ofReal_mul (mul_nonneg np.le nq.le),
          ENNReal.ofReal_mul np.le, ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
        ring
    _ ≤ 1 * (⨆ P' ∈ fam, MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (lgAdm T.post L γ (η / 2) P') P') *
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) := by
        gcongr
        · exact hpiece
        · exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countAFree T.post L γ δ C1 (0 : Mom d)
            (lgAdm T.post L γ (η / 2) P') P') P0 hP0 le_rfl
    _ = _ := by ring

end TwoExit

end WaveTurbulence.MoleProp4
