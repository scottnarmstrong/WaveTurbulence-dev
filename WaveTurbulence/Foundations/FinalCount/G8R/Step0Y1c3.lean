/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Pinch
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1c1
import Mathlib.Tactic

/-! # Prop 10.4(2)′, Step 0: a sequence ending in (Y1) case 3

DH23 L1963: "If the last operation is (Y1), which must be case 3 (since `𝕄` is 4-regular), then we have `E = 2V − 1`
for `𝕄′`, so the result for `𝔄(𝕄′)` follows from Proposition 10.2." With at most two triple bonds, `𝕄₁ = 𝕄 ∖ chain`
may keep one triple bond; a second complete sequence then ends in (Y1) case 2, (Y1) case 3 or (Y2) ((Y1) case 1 is
impossible: the far end `w` has degree two). After (Y1) case 3 the residual molecule has `E = 2V − 2`, and Prop 10.2's
second statement applies **if it has a bond**; otherwise it is the single atom `w`, so `w` would be a cut vertex of
`𝕄` (two chains attached to `w` only). This is where "no cut vertex" is used.

Conclusion: `𝔄(𝕄) ≲ (log L)^C · L^{−η/3}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- **DH23 Proposition 10.2, second statement, as an input** (packet G5): a connected molecule with no triple bond and
`E = 2V − 2 > 0` has `𝔄 ≲ L^{−η/3}`. -/
def Prop102SecondInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → (∀ a b, M.bondsBetween a b ≤ 2) →
      (M.bonds.card : ℤ) = 2 * M.atoms.card - 2 → 0 < M.bonds.card → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(η / 3)))

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
theorem loopFree_erase {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (Y : Finset V) :
    ∀ z, (Degen.eraseAtoms M Y).atom z ≠ (Degen.eraseAtoms M Y).atom ((Degen.eraseAtoms M Y).mate z) :=
  fun z => hloop z.val

omit [DecidableEq D] in
/-- Chain atoms have degree at least three. -/
theorem YChain.three_le_deg {M : Molecule V D} (C : YChain M) {v : V} (hv : v ∈ C.set) : 3 ≤ M.deg v := by
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
  · rcases Nat.lt_or_ge i C.n with h | h
    · have := (C.sat i h).1; omega
    · have := C.card_away_last_a; rw [le_antisymm hi h]; omega
  · rcases Nat.lt_or_ge i C.n with h | h
    · have := (C.sat i h).2; omega
    · have := C.card_away_last_b; rw [le_antisymm hi h]; omega

omit [DecidableEq D] in
/-- With degrees at most four and `E = 2V − 2`, some atom has degree `≠ 4`. -/
theorem exists_deg_ne_four' (N : Molecule V D)
    (hE : (N.bonds.card : ℤ) = 2 * N.atoms.card - 2) : ∃ z ∈ N.atoms, N.deg z ≠ 4 := by
  classical
  by_contra h
  push Not at h
  have hs := Mole.sum_degrees_eq_two_mul_bonds N
  rw [sum_congr rfl h, sum_const, smul_eq_mul] at hs
  omega

/-- **Step 0, (Y1) case 3 ending: the first alternative.** -/
theorem branch_y1c3 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (h1a : Prop102Input.{u, v} d γ η) (h1b : Prop102Input.{u, v} d γ (η / 2))
    (h2 : Prop102SecondInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (_hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2), (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      (∀ v ∈ M.atoms, M.deg v = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
        (Degen.eraseAtoms M {w}).SameComponent a b) →
      (∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
        s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u)) → (∀ p q, M.bondsBetween p q ≤ 3) →
      (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      ∀ (C : YChain M) (_ : Y1End3 C), ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 3))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hη2 : 0 < η / 2 := by linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by linarith
  obtain ⟨Cs1, hCs1, hb1⟩ := ylem2_Y1c3 d hd γ hγ η hη hηmax
  obtain ⟨Cs2, hCs2, hb2⟩ := ylem2_Y1c2 d hd γ hγ η hη hηmax
  obtain ⟨Cs3, hCs3, hb3⟩ := ylem2_Y2 d hd γ hγ η hη hηmax
  obtain ⟨Cs4, hCs4, hb4⟩ := h1a
  obtain ⟨Cs5, hCs5, hb5⟩ := h1b
  obtain ⟨Cs6, hCs6, hb6⟩ := h2
  set Cs := max (max Cs1 Cs2) (max Cs3 (max Cs4 (max Cs5 Cs6)))
  have hc1 : Cs1 ≤ Cs := (le_max_left _ _).trans (le_max_left _ _)
  have hc2 : Cs2 ≤ Cs := (le_max_right _ _).trans (le_max_left _ _)
  have hc3 : Cs3 ≤ Cs := (le_max_left _ _).trans (le_max_right _ _)
  have hc4 : Cs4 ≤ Cs := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hc5 : Cs5 ≤ Cs := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have hc6 : Cs6 ≤ Cs := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  refine ⟨Cs, hCs1.trans hc1, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hb1 C1 (by linarith) δ hδ
  obtain ⟨R2, hR2⟩ := hb2 C1 (by linarith) δ hδ
  obtain ⟨R3, hR3⟩ := hb3 C1 (by linarith) δ hδ
  obtain ⟨R4, hR4⟩ := hb4 m C1 (by linarith) δ hδ
  obtain ⟨R5, hR5⟩ := hb5 m C1 (by linarith) δ hδ
  obtain ⟨R6, hR6⟩ := hb6 m C1 (by linarith) δ hδ
  refine ⟨max (max (max R1 R2) (max R3 R4)) (max (max R5 R6) (Real.exp 1)), fun L hL => ?_⟩
  intro V D _ _ _ M hcap hloop h4 hconn hcut htri hle3 hsz C E P hP
  classical
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLR4 : R4 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLR5 : R5 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLR6 : R6 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  have hpw : L ^ (-(3 / 5 * min γ (1 - γ))) ≤ L ^ (-(η / 3)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  have hpos3 : 0 ≤ L ^ (-(η / 3)) := Real.rpow_nonneg hLp.le _
  have hfin1 : ENNReal.ofReal (L ^ (-(η / 3))) ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 3))) :=
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hpos3 hK)
  have hfin2 : ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 3))) :=
    (ENNReal.ofReal_le_ofReal hpw).trans hfin1
  -- the molecule after the first sequence
  have hdegM : (M.bonds.card : ℤ) = 2 * M.atoms.card := by
    have hs := Mole.sum_degrees_eq_two_mul_bonds M
    rw [sum_congr rfl h4, sum_const, smul_eq_mul] at hs
    omega
  have step1 := hR1 L hLR1 M hcap C E P hP
  let M1 := Degen.eraseAtoms M C.set
  have hcap1 : ∀ v ∈ M1.atoms, M1.outdeg v ≤ 2 ∧ M1.indeg v ≤ 2 := caps_eraseAtoms _ hcap
  have hloop1 := loopFree_erase hloop C.set
  have hconn1 := E.erase_connected hcap hconn
  have hsz1 : (M1.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    hsz.trans' (by exact_mod_cast card_le_card (sdiff_subset (s := M.atoms) (t := C.set)))
  have hcardM1 : (M1.atoms.card : ℤ) = M.atoms.card - C.set.card := by
    change ((M.atoms \ C.set).card : ℤ) = _
    rw [card_sdiff_of_subset C.set_sub, Nat.cast_sub (card_le_card C.set_sub)]
  have hE1 : (M1.bonds.card : ℤ) = 2 * M1.atoms.card - 1 := by
    have : (M1.bonds.card : ℤ) = M.bonds.card - 2 * C.set.card - 1 := E.erase_bonds hcap
    rw [hcardM1]; omega
  have hw1 : M.atom (M.mate E.x) ∈ M1.atoms := mem_sdiff.mpr ⟨M.atom_mem _, E.hxo⟩
  have hdw : M1.deg (M.atom (M.mate E.x)) = 2 := by
    have : M1.deg (M.atom (M.mate E.x)) + 2 = M.deg (M.atom (M.mate E.x)) := E.erase_deg_w
    rw [h4 _ (M.atom_mem _)] at this; omega
  have hmol1 : M1.IsMolecule := isMolecule_of_connected _ hcap1 hconn1 hw1 (by rw [hdw]; norm_num)
  have hP1 := nonneg_erase hP C.set
  have h3M1 : ∀ p q, 3 ≤ M1.bondsBetween p q → p ∉ C.set ∧ q ∉ C.set ∧ M.bondsBetween p q = 3 := by
    intro p q h
    by_cases hp : p ∈ C.set
    · rw [bondsBetween_erase_of_mem M C.set hp] at h; omega
    by_cases hq : q ∈ C.set
    · rw [Degen.bondsBetween_comm, bondsBetween_erase_of_mem M C.set hq] at h; omega
    rw [Degen.bondsBetween_erase_eq _ _ hp hq] at h
    exact ⟨hp, hq, by have := hle3 p q; omega⟩
  have hle3' : ∀ p q, M1.bondsBetween p q ≤ 3 := fun p q => (erase_bonds_le M C.set p q).trans (hle3 p q)
  -- no triple bond left: Prop 10.2
  by_cases hno : ∀ p q, M1.bondsBetween p q ≤ 2
  · exact step1.trans ((hR4 L hLR4 M1 hmol1 hconn1 hno hE1 hsz1 P hP1).trans hfin2)
  push Not at hno
  obtain ⟨p0, q0, hpq0⟩ := hno
  have h3 : M1.bondsBetween p0 q0 = 3 := by have := hle3' p0 q0; omega
  have hne0 : p0 ≠ q0 := by rintro rfl; rw [bondsBetween_self_eq_zero hloop1] at h3; omega
  have hq0 : q0 ∈ M1.atoms := mem_atoms_of_bondsBetween_pos (a := p0) (by omega)
  have hp0 : p0 ∈ M1.atoms := mem_atoms_of_bondsBetween_pos (a := q0) (by rw [Degen.bondsBetween_comm]; omega)
  obtain ⟨C2, hC2a, hC2b, hcomp⟩ := exists_complete hcap1 hloop1 hp0 hq0 hne0 h3
  -- the triple bonds of `𝕄₁`
  have htri1 : ∀ p q, 3 ≤ M1.bondsBetween p q → s(p, q) = s(C2.a 0, C2.b 0) := by
    intro p q h
    obtain ⟨hp, hq, h3'⟩ := h3M1 p q h
    obtain ⟨_, _, h3''⟩ := h3M1 p0 q0 (by omega)
    have ha0 : C.a 0 ∈ C.set := C.a_mem (Nat.zero_le _)
    rw [hC2a, hC2b]
    rcases htri p q p0 q0 (C.a 0) (C.b 0) (by omega) (by omega) (by rw [C.triple]) with h | h | h
    · exact h
    · exfalso; rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact hp (h' ▸ ha0)
      · exact hq (h' ▸ ha0)
    · exfalso
      obtain ⟨hp0', hq0', _⟩ := h3M1 p0 q0 (by omega)
      rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact hp0' (h' ▸ ha0)
      · exact hq0' (h' ▸ ha0)
  have hwC2 : M.atom (M.mate E.x) ∉ C2.set := fun h => by have := C2.three_le_deg h; omega
  rcases hcomp with h6 | hE2 | hE2 | ⟨E2, hE2c⟩
  · -- (Y1) case 1: impossible, `w` has degree two
    exact absurd ((C2.set_eq_atoms h6 hconn1).symm ▸ hw1) hwC2
  · -- (Y1) case 2
    obtain ⟨E2⟩ := hE2
    let M2 := Degen.eraseAtoms M1 C2.set
    have hstep := hR2 L hLR2 M1 hcap1 C2 E2 P hP1
    have hsum := C2.sum_deg_Y1End2 E2
    have hcY : 1 ≤ C2.set.card := by rw [C2.card_set]; omega
    have hE2 : (M2.bonds.card : ℤ) = 2 * M2.atoms.card - 1 := by
      have : (M2.bonds.card : ℤ) = M1.bonds.card - 2 * C2.set.card := E2.toOneExit.erase_bonds_card hsum hcY
      have hc2 : (M2.atoms.card : ℤ) = M1.atoms.card - C2.set.card := by
        change ((M1.atoms \ C2.set).card : ℤ) = _
        rw [card_sdiff_of_subset C2.set_sub, Nat.cast_sub (card_le_card C2.set_sub)]
      omega
    have hconn2 := E2.toOneExit.erase_connected hconn1
    obtain ⟨z, hz, hz4, _⟩ := exists_deg_ne_four _ (caps_eraseAtoms _ hcap1) hE2
    have hmol2 : M2.IsMolecule := isMolecule_of_connected _ (caps_eraseAtoms _ hcap1) hconn2 hz hz4
    exact step1.trans (hstep.trans ((hR4 L hLR4 M2 hmol2 hconn2 (erase_bonds_le_two C2 htri1) hE2
      (hsz1.trans' (by exact_mod_cast card_le_card (sdiff_subset (s := M1.atoms) (t := C2.set)))) P
      (nonneg_erase hP1 _)).trans hfin2))
  · -- (Y1) case 3
    obtain ⟨E2⟩ := hE2
    let M2 := Degen.eraseAtoms M1 C2.set
    have hstep := hR1 L hLR1 M1 hcap1 C2 E2 P hP1
    have hcardM2 : (M2.atoms.card : ℤ) = M1.atoms.card - C2.set.card := by
      change ((M1.atoms \ C2.set).card : ℤ) = _
      rw [card_sdiff_of_subset C2.set_sub, Nat.cast_sub (card_le_card C2.set_sub)]
    have hE2 : (M2.bonds.card : ℤ) = 2 * M2.atoms.card - 2 := by
      have : (M2.bonds.card : ℤ) = M1.bonds.card - 2 * C2.set.card - 1 := E2.erase_bonds hcap1
      rw [hcardM2]; omega
    have hw2 : M.atom (M.mate E.x) ∈ M2.atoms := mem_sdiff.mpr ⟨hw1, hwC2⟩
    by_cases hbig : 2 ≤ M2.atoms.card
    · have hconn2 := E2.erase_connected hcap1 hconn1
      obtain ⟨z, hz, hz4⟩ := exists_deg_ne_four' M2 hE2
      have hmol2 : M2.IsMolecule := isMolecule_of_connected _ (caps_eraseAtoms _ hcap1) hconn2 hz hz4
      exact step1.trans (hstep.trans ((hR6 L hLR6 M2 hmol2 hconn2 (erase_bonds_le_two C2 htri1) hE2
        (by omega) (hsz1.trans' (by exact_mod_cast card_le_card (sdiff_subset (s := M1.atoms) (t := C2.set)))) P (nonneg_erase hP1 _)).trans hfin1))
    · -- the residual molecule is `{w}`: `w` is a cut vertex of `𝕄`
      exfalso
      have hM2 : M2.atoms = {M.atom (M.mate E.x)} := by
        refine (eq_singleton_iff_unique_mem.mpr ⟨hw2, fun v hv => ?_⟩)
        have hc := card_le_one.mp (by omega : M2.atoms.card ≤ 1)
        exact hc v hv _ hw2
      have ha : C.a 0 ∈ M.atoms := (C.mem 0 (Nat.zero_le _)).1
      have hb : C2.a 0 ∈ M.atoms := (mem_sdiff.mp (C2.mem 0 (Nat.zero_le _)).1).1
      have hbC : C2.a 0 ∉ C.set := (mem_sdiff.mp (C2.mem 0 (Nat.zero_le _)).1).2
      have haw : C.a 0 ≠ M.atom (M.mate E.x) := fun h => E.hxo (by
        have := C.a_mem (i := 0) (Nat.zero_le _); rwa [h] at this)
      have hbw : C2.a 0 ≠ M.atom (M.mate E.x) := fun h => hwC2 (by
        have := C2.a_mem (i := 0) (Nat.zero_le _); rwa [h] at this)
      have hc := hcut (M.atom (M.mate E.x)) (M.atom_mem _) _ ha _ hb haw hbw
      -- `C.set` is closed in `𝕄 ∖ {w}`
      have hclosed : ∀ z, (Degen.eraseAtoms M {M.atom (M.mate E.x)}).atom z ∈ C.set →
          (Degen.eraseAtoms M {M.atom (M.mate E.x)}).atom
            ((Degen.eraseAtoms M {M.atom (M.mate E.x)}).mate z) ∈ C.set := by
        intro z hz
        by_contra hout
        have hcr : z.val ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hz, hout⟩
        rw [E.cross_eq] at hcr
        have hzw : M.atom (M.mate z.val) ≠ M.atom (M.mate E.x) := fun h => z.property.2 (by rw [h]; exact mem_singleton_self _)
        rcases mem_insert.mp hcr with h | h
        · exact hzw (by rw [h])
        · exact hzw (by rw [mem_singleton.mp h]; exact E.same.symm)
      exact hbC ((mem_iff_of_sameComponent_of_closed hclosed hc).mp (C.a_mem (Nat.zero_le _)))
  · -- (Y2), complete
    set T2 := E2.toTwoExit hcap1
    have hT2Y : T2.Y = C2.set := E2.toTwoExit_Y hcap1
    have hdegY2 : ∀ v ∈ T2.Y, M1.deg v = 4 := by rw [hT2Y]; exact E2.deg_four
    have hEp : (T2.post.bonds.card : ℤ) = 2 * T2.post.atoms.card - 1 := by
      rw [T2.post_bonds_card hdegY2, T2.post_atoms_card]; omega
    have hconnP := T2.post_connected hconn1
    obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four _ (T2.post_caps hcap1) hEp
    have hmolP : T2.post.IsMolecule := isMolecule_of_connected _ (T2.post_caps hcap1) hconnP hz hz4
    have hgood : ∀ S ∈ MoleProp.ladderCells T2.post, T2.c ∈ S → GoodCell T2.post S :=
      fun S hS _ => goodCell_of_connected_low hconnP hz hz3 hS
    have hcd := E2.toTwoExit_cd hcap1
    have hle2 : ∀ p q, T2.post.bondsBetween p q ≤ 2 := by
      intro p q
      unfold TwoExit.post
      rw [addBond_bondsBetween]
      have hbase := erase_bonds_le_two C2 htri1 p q
      rw [← hT2Y] at hbase
      by_cases hpq : s(T2.d, T2.c) = s(p, q)
      · rw [ite_of_pos hpq]
        have hval : (Degen.eraseAtoms M1 T2.Y).bondsBetween p q = M1.bondsBetween T2.d T2.c := by
          rw [← Degen.bondsBetween_erase_eq M1 T2.Y T2.d_notMem T2.c_notMem]
          rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Degen.bondsBetween_comm]
        rw [hval]
        have hne2 : M1.bondsBetween T2.d T2.c ≠ 2 := by
          rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2, Degen.bondsBetween_comm]; exact hE2c
          · rw [h1, h2]; exact hE2c
        have hle : M1.bondsBetween T2.d T2.c ≤ 2 := by
          have := erase_bonds_le_two C2 htri1 T2.d T2.c
          rw [← hT2Y, Degen.bondsBetween_erase_eq M1 T2.Y T2.d_notMem T2.c_notMem] at this; exact this
        omega
      · rw [ite_of_not hpq]; omega
    have hY2 := hR3 L hLR3 M1 hcap1 C2 E2 hgood P hP1
    have hsup : AFreeSup T2.post d L γ δ (η / 2) C1 ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) :=
      iSup₂_le fun P' hP' => hR5 L hLR5 T2.post hmolP hconnP hle2 hEp (hsz1.trans' (by rw [T2.post_atoms]; exact_mod_cast card_le_card (sdiff_subset (s := M1.atoms) (t := T2.Y)))) P' hP'
    refine step1.trans (hY2.trans ((mul_le_mul' le_rfl hsup).trans ?_))
    rw [← ENNReal.ofReal_mul (zero_le_one.trans hK)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpw (zero_le_one.trans hK))

end WaveTurbulence.MoleProp4
