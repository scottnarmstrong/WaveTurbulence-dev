/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BetaCut
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.VineIIHalf
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PolyLog
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1c1
import Mathlib.Tactic

/-! # DH23 Proposition 10.4(1) (L1838, proof L1959), conditional on Prop 10.2

A connected molecule with at most one triple bond and `E = 2V − 1`, with no exceptional β-cut and not a half-closed vine
(II) (B2 template with `m ≥ 1` rungs, F72; the `m = 1` member is the length-one omission of L1959), has
`𝔄 ≲ L^{−4γ₀/7}`.

Proof (L1959): one complete (Y) sequence removes the triple bond. Its ending is not (Y1) case 3 (β-cut, `BetaCut`), nor
(Y1) case 1 (half-closed vine (II), `VineIIHalf`). After (Y1) case 2 or (Y2), `𝕄′` is a connected molecule with no
triple bond and `E = 2V − 1`, so Prop 10.2 gives `𝔄(𝕄′) ≲ L^{−3γ₀/5}`, and `ylem2` gives
`𝔄(𝕄) ≲ (log L)^C 𝔄(𝕄′) ≲ L^{−4γ₀/7}`.

Prop 10.2 is an input (packet G5), stated here as `Prop102Input` in the relaxed counting language of G6, at LG
parameter `η/2` (the (Y2) step halves it, DH23 L1954).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- **DH23 Proposition 10.2, first statement, as an input** (packet G5): a connected molecule with no triple bond and
`E = 2V − 1` has `𝔄 ≲ L^{−3γ₀/5}` (relaxed count `AFree`, LG parameter `η`). -/
def Prop102Input (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → (∀ a b, M.bondsBetween a b ≤ 2) →
      (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ))))

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- After erasing the chain, no triple bond is left (the chain held the only one). -/
theorem erase_bonds_le_two {M : Molecule V D} (C : YChain M)
    (htri : ∀ p q, 3 ≤ M.bondsBetween p q → s(p, q) = s(C.a 0, C.b 0)) (p q : V) :
    (Degen.eraseAtoms M C.set).bondsBetween p q ≤ 2 := by
  by_cases hp : p ∈ C.set
  · rw [bondsBetween_erase_of_mem M C.set hp]; omega
  by_cases hq : q ∈ C.set
  · rw [Degen.bondsBetween_comm, bondsBetween_erase_of_mem M C.set hq]; omega
  rw [Degen.bondsBetween_erase_eq _ _ hp hq]
  by_contra h
  have := htri p q (by omega)
  rcases Sym2.eq_iff.mp this with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hp (h1 ▸ C.a_mem (Nat.zero_le _))
  · exact hp (h1 ▸ C.b_mem (Nat.zero_le _))

/-- **DH23 Proposition 10.4(1)**, conditional on Prop 10.2 (at LG parameter `η/2`). -/
theorem prop104_one (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (h102 : Prop102Input.{u, v} d γ (η / 2)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ p q r s, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → s(p, q) = s(r, s)) →
      (∀ p q, M.bondsBetween p q ≤ 3) → (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 →
      (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → ¬ HasBadBetaCut M → (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ IsVineIIHalfClosure M →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ)))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  obtain ⟨Cs1, hCs1, h1⟩ := ylem2_Y1c2 d hd γ hγ η hη hηmax
  obtain ⟨Cs2, hCs2, h2⟩ := ylem2_Y2 d hd γ hγ η hη hηmax
  obtain ⟨Cs3, hCs3, h3⟩ := h102
  refine ⟨max Cs1 (max Cs2 Cs3), hCs1.trans (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  have e1 : C1 ≥ 2 * Cs1 := by linarith [le_max_left Cs1 (max Cs2 Cs3)]
  have e2 : C1 ≥ 2 * Cs2 := by linarith [le_max_right Cs1 (max Cs2 Cs3), le_max_left Cs2 Cs3]
  have e3 : C1 ≥ Cs3 := by linarith [le_max_right Cs1 (max Cs2 Cs3), le_max_right Cs2 Cs3]
  obtain ⟨R1, hR1⟩ := h1 C1 e1 δ hδ
  obtain ⟨R2, hR2⟩ := h2 C1 e2 δ hδ
  obtain ⟨R3, hR3⟩ := h3 m C1 e3 δ hδ
  obtain ⟨R4, hR4⟩ := eventually_ylem2Const_le (θ := min γ (1 - γ) / 35) (by positivity)
  refine ⟨max (max R1 R2) (max (max R3 R4) (Real.exp 1)), fun L hL => ?_⟩
  intro V D _ _ _ M hmol hconn htri hle3 hE hsz hβ hfresh hII P hP
  classical
  have hLR1 : R1 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLR2 : R2 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLR3 : R3 ≤ L := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hL
  have hLR4 : R4 ≤ L := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hL
  have hLe : Real.exp 1 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hpow : L ^ (-(3 / 5 * min γ (1 - γ))) ≤ L ^ (-(4 / 7 * min γ (1 - γ))) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  have hcap := hmol.1
  -- loops give nothing
  by_cases hlo : ∃ z : D, M.atom z = M.atom (M.mate z)
  · obtain ⟨z, hz⟩ := hlo
    unfold AFree
    rw [MoleProp.countAFree_eq_zero_of_loop M hLp γ δ C1 η 0 _ (fun κ h => h.1) P z hz]
    exact bot_le
  have hloop : ∀ z, M.atom z ≠ M.atom (M.mate z) := fun z h => hlo ⟨z, h⟩
  -- no triple bond: Prop 10.2 directly
  by_cases hno : ∀ p q, M.bondsBetween p q ≤ 2
  · exact (afree_mono_eta M hL1 (by linarith) P).trans ((hR3 L hLR3 M hmol hconn hno hE hsz P hP).trans
      (ENNReal.ofReal_le_ofReal hpow))
  push Not at hno
  obtain ⟨a0, b0, hab3⟩ := hno
  have h3 : M.bondsBetween a0 b0 = 3 := by have := hle3 a0 b0; omega
  have hne : a0 ≠ b0 := by
    rintro rfl; rw [bondsBetween_self_eq_zero hloop] at h3; omega
  have hb0 : b0 ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := a0) (by omega)
  have ha0 : a0 ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := b0) (by rw [Degen.bondsBetween_comm]; omega)
  obtain ⟨C, hCa, hCb, hcomp⟩ := exists_complete hcap hloop ha0 hb0 hne h3
  have htri' : ∀ p q, 3 ≤ M.bondsBetween p q → s(p, q) = s(C.a 0, C.b 0) := fun p q h => by
    rw [hCa, hCb]; exact htri p q a0 b0 h (by omega)
  rcases hcomp with h6 | hE1 | hE3 | ⟨E, hE2⟩
  · -- (Y1) case 1: a half-closed vine (II)
    exact absurd (C.isVineIIHalfClosure h6 (C.set_eq_atoms h6 hconn)) hII
  · -- (Y1) case 2
    obtain ⟨E⟩ := hE1
    set T := E.toOneExit
    have hTY : T.Y = C.set := rfl
    have hEr : ((Degen.eraseAtoms M C.set).bonds.card : ℤ) = 2 * (Degen.eraseAtoms M C.set).atoms.card - 1 := by
      have := T.erase_bonds_card (C.sum_deg_Y1End2 E) (by rw [hTY, C.card_set]; omega)
      change ((Degen.eraseAtoms M C.set).bonds.card : ℤ) = 2 * ((M.atoms \ C.set).card : ℕ) - 1
      rw [card_sdiff_of_subset C.set_sub, Nat.cast_sub (card_le_card C.set_sub)]
      rw [hTY] at this; omega
    have hconnE := T.erase_connected hconn
    obtain ⟨z, hz, hz4, _⟩ := exists_deg_ne_four _ (caps_eraseAtoms _ hcap) hEr
    have hmolE : (Degen.eraseAtoms M C.set).IsMolecule :=
      isMolecule_of_connected _ (caps_eraseAtoms _ hcap) hconnE hz hz4
    refine (hR1 L hLR1 M hcap C E P hP).trans ((afree_mono_eta _ hL1 (by linarith) P).trans
      ((hR3 L hLR3 _ hmolE hconnE (erase_bonds_le_two C htri') hEr (hsz.trans' (by exact_mod_cast card_le_card (sdiff_subset (s := M.atoms) (t := C.set)))) P (nonneg_erase hP _)).trans
        (ENNReal.ofReal_le_ofReal hpow)))
  · -- (Y1) case 3: the excluded β-cut
    obtain ⟨E⟩ := hE3
    obtain ⟨v₂, hv₂⟩ := hfresh
    exact absurd ((E.toPinch hcap).hasBadBetaCut hv₂ (by rw [E.toPinch_Y]; exact E.deg_four)) hβ
  · -- (Y2), complete
    set T := E.toTwoExit hcap
    have hTY : T.Y = C.set := E.toTwoExit_Y hcap
    have hdegY : ∀ v ∈ T.Y, M.deg v = 4 := by rw [hTY]; exact E.deg_four
    have hEp : (T.post.bonds.card : ℤ) = 2 * T.post.atoms.card - 1 := by
      rw [T.post_bonds_card hdegY, T.post_atoms_card]; omega
    have hconnP := T.post_connected hconn
    obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four _ (T.post_caps hcap) hEp
    have hmolP : T.post.IsMolecule := isMolecule_of_connected _ (T.post_caps hcap) hconnP hz hz4
    have hcd := E.toTwoExit_cd hcap
    have hle2 : ∀ p q, T.post.bondsBetween p q ≤ 2 := by
      intro p q
      unfold TwoExit.post
      rw [addBond_bondsBetween]
      have hbase := erase_bonds_le_two C htri' p q
      rw [← hTY] at hbase
      by_cases hpq : s(T.d, T.c) = s(p, q)
      · rw [ite_of_pos hpq]
        have hcY := T.c_notMem
        have hdY := T.d_notMem
        have hval : (Degen.eraseAtoms M T.Y).bondsBetween p q = M.bondsBetween T.d T.c := by
          rw [← Degen.bondsBetween_erase_eq M T.Y hdY hcY]
          rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Degen.bondsBetween_comm]
        rw [hval]
        have hne2 : M.bondsBetween T.d T.c ≠ 2 := by
          rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2, Degen.bondsBetween_comm]; exact hE2
          · rw [h1, h2]; exact hE2
        have hle : M.bondsBetween T.d T.c ≤ 2 := by
          have := erase_bonds_le_two C htri' T.d T.c
          rw [← hTY, Degen.bondsBetween_erase_eq M T.Y hdY hcY] at this; exact this
        omega
      · rw [ite_of_not hpq]; omega
    have hgood : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S :=
      fun S hS _ => goodCell_of_connected_low hconnP hz hz3 hS
    have hY2 := hR2 L hLR2 M hcap C E hgood P hP
    have hsup : AFreeSup T.post d L γ δ (η / 2) C1 ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) :=
      iSup₂_le fun P' hP' => hR3 L hLR3 T.post hmolP hconnP hle2 hEp (le_trans (by rw [T.post_atoms]; exact_mod_cast card_le_card (sdiff_subset (s := M.atoms) (t := T.Y))) hsz) P' hP'
    refine hY2.trans ((mul_le_mul' le_rfl hsup).trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK := hR4 L hLR4
    calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(3 / 5 * min γ (1 - γ)))
        ≤ L ^ (min γ (1 - γ) / 35) * L ^ (-(3 / 5 * min γ (1 - γ))) :=
          mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLp.le _)
      _ = L ^ (-(4 / 7 * min γ (1 - γ))) := by rw [← Real.rpow_add hLp]; ring_nf

end WaveTurbulence.MoleProp4
