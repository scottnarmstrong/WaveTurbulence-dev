/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseI
public import WaveTurbulence.Foundations.FinalCount.PairGainInput
import Mathlib.Tactic

/-! # G8-XROUTE: the case-(I) bound for `𝔄(𝕄 ∖ ℓ)` of a core molecule (DH23 L1963-L1965)

Copy of `G8R.CoreCaseI.case_pair_ab` / `case_pair` (sha256 in COPIED-SHA256SUMS) with the conclusion
`SplitBound` replaced by the bound it is built from: `𝔄(𝕄 ∖ ℓ) ≤ K (log L)^B L^{-γ₀} L^{-η/3}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Case I, for a given pair `a, b`.** -/
theorem afree_pair_ab {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 0 < L) (hpg : PairGainAt.{u, v} d L γ δ η C1 K B)
    {m : ℕ} (h102s : Prop102SecondAt.{u, v} d L γ δ η C1 m) {M : Molecule V D}
    (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) (hM : IsCore M) (e : D)
    (hnoII : ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2)
    {a b : V} (haM : a ∈ M.atoms) (hbM : b ∈ M.atoms) (hab : a ≠ b)
    (hend : M.atom e ∈ ({a, b} : Finset V) ∨ M.atom (M.mate e) ∈ ({a, b} : Finset V))
    (hda : (MoleProp.eraseBond M e).deg a = 3)
    (hconf : ((MoleProp.eraseBond M e).deg b = 4 ∧ (MoleProp.eraseBond M e).bondsBetween a b = 2) ∨
      ((MoleProp.eraseBond M e).deg b = 3 ∧ (MoleProp.eraseBond M e).bondsBetween a b = 1))
    (hc4 : (crossDarts M {a, b}).card = 4) :
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        ENNReal.ofReal (K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-(η / 3))) := by
  classical
  have hY : ({a, b} : Finset V) ⊆ M.atoms := by
    intro z hz; rcases mem_insert.mp hz with rfl | hz
    · exact haM
    · rw [mem_singleton.mp hz]; exact hbM
  -- the rest is connected
  have hRconn : ∀ x ∈ (Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).atoms,
      ∀ y ∈ (Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).atoms,
      (Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).SameComponent x y :=
    fun x hx y hy => sameComponent_erase_eraseBond hend (erase_pair_connected hM hnoII hc4 x hx y hy)
  -- its bonds: `E = 2V − 2`
  have h4 := hM.four_le_card (M.atom_mem e)
  have hcardR : ((Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).atoms.card : ℤ) = M.atoms.card - 2 := by
    change ((M.atoms \ {a, b}).card : ℤ) = _
    rw [card_sdiff_of_subset hY, card_pair hab]
    have := card_le_card hY
    rw [card_pair hab] at this
    omega
  have hE1 := two_mul_erase_bonds (MoleProp.eraseBond M e) (Y := {a, b}) hY
  have hE2 := card_cross_pair (MoleProp.eraseBond M e) (hM.eraseBond_loop e) hab
  have hE3 := hM.eraseBond_sum_deg e (subset_refl M.atoms)
  rw [ite_of_pos (M.atom_mem e), ite_of_pos (M.atom_mem _)] at hE3
  have hE4 := sum_sdiff (f := fun v => (MoleProp.eraseBond M e).deg v) hY
  rw [sum_pair hab] at hE4
  have hER : ((Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).bonds.card : ℤ) =
      2 * (Degen.eraseAtoms (MoleProp.eraseBond M e) {a, b}).atoms.card - 2 := by
    rw [hcardR]
    change 2 * _ + _ = ∑ v ∈ M.atoms \ {a, b}, (MoleProp.eraseBond M e).deg v at hE1
    rcases hconf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- a low-degree atom of the rest
  obtain ⟨x, hx⟩ : (crossDarts (MoleProp.eraseBond M e) {a, b}).Nonempty := card_pos.mp (by
    rcases hconf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  obtain ⟨hx1, hx2⟩ := mem_crossDarts.mp hx
  set N := MoleProp.eraseBond M e with hN
  have hzR : N.atom (N.mate x) ∈ (Degen.eraseAtoms N {a, b}).atoms := mem_sdiff.mpr ⟨N.atom_mem _, hx2⟩
  have hz3 : (Degen.eraseAtoms N {a, b}).deg (N.atom (N.mate x)) ≠ 4 := by
    have h := deg_eraseAtoms_add (N := N) {a, b} (v := N.atom (N.mate x)) hx2
    have hmem : N.mate x ∈ Degen.removedDartsAt N {a, b} (N.atom (N.mate x)) := by
      unfold Degen.removedDartsAt Molecule.dartsAt
      simp only [mem_filter, mem_univ, true_and]
      rw [N.mate_mate]; exact hx1
    have := card_pos.mpr ⟨_, hmem⟩
    have hle : N.deg (N.atom (N.mate x)) ≤ 4 := hM.eraseBond_deg_le e (M.atom_mem _)
    omega
  have hcapR := caps_eraseAtoms (N := N) {a, b} (caps_eraseBond M e hM.cap)
  have hmolR := isMolecule_of_connected _ hcapR hRconn hzR hz3
  have hle2R : ∀ u w, (Degen.eraseAtoms N {a, b}).bondsBetween u w ≤ 2 := fun u w =>
    (erase_bonds_le N _ u w).trans ((bondsBetween_eraseBond_le' M e u w).trans (hM.le2 u w))
  have hpos : 0 < (Degen.eraseAtoms N {a, b}).bonds.card := by omega
  have hAR : AFreeSup (Degen.eraseAtoms N {a, b}) d L γ δ η C1 ≤ ENNReal.ofReal (L ^ (-(η / 3))) :=
    iSup₂_le fun P hP => h102s _ hmolR hRconn hle2R hER hpos
      (hsz.trans' (by exact_mod_cast card_le_card (sdiff_subset (s := M.atoms) (t := ({a, b} : Finset V))))) P hP
  intro P hP
  have hmain := hpg N (caps_eraseBond M e hM.cap) (hM.eraseBond_loop e) a haM b hbM hab hda hconf
    (hM.eraseBond_conn e) hRconn P hP
  refine hmain.trans ((mul_le_mul' le_rfl hAR).trans ?_)
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hL.le _)]

/-- **Case I: a double bond at an end of `ℓ`** — the second alternative. -/
theorem afree_case_pair {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 0 < L) (hpg : PairGainAt.{u, v} d L γ δ η C1 K B)
    {m : ℕ} (h102s : Prop102SecondAt.{u, v} d L γ δ η C1 m) {M : Molecule V D}
    (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) (hM : IsCore M) (e : D)
    (hnoII : ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2)
    (hI : ∃ w, M.bondsBetween (M.atom e) w = 2 ∨ M.bondsBetween (M.atom (M.mate e)) w = 2) :
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        ENNReal.ofReal (K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-(η / 3))) := by
  classical
  have hpq : M.atom e ≠ M.atom (M.mate e) := hM.loop e
  have hends : M.ends e = s(M.atom e, M.atom (M.mate e)) := rfl
  by_cases hd : M.bondsBetween (M.atom e) (M.atom (M.mate e)) = 2
  · -- `ℓ` is one copy of a double bond: a `(3,3)` single pair in `𝕄 ∖ ℓ`
    have hbb := bondsBetween_eraseBond_of_ends M e hends (M.atom e) (M.atom (M.mate e))
    rw [ite_of_pos rfl, hd] at hbb
    have h := card_cross_pair M hM.loop hpq
    rw [hd, hM.reg _ (M.atom_mem e), hM.reg _ (M.atom_mem _)] at h
    exact afree_pair_ab hL hpg h102s hsz hM e hnoII (M.atom_mem e) (M.atom_mem _) hpq (Or.inl (mem_insert_self _ _))
      (hM.eraseBond_deg_p e) (Or.inr ⟨hM.eraseBond_deg_q e, by omega⟩) (by omega) 
  obtain ⟨w, hw | hw⟩ := hI
  · have hwq : w ≠ M.atom (M.mate e) := fun h => hd (h ▸ hw)
    have hwp : w ≠ M.atom e := fun h => by rw [h, bondsBetween_self_eq_zero hM.loop] at hw; omega
    have hwM : w ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := M.atom e) (by omega)
    have h := card_cross_pair M hM.loop hwp.symm
    rw [hw, hM.reg _ (M.atom_mem e), hM.reg _ hwM] at h
    have hbb : (MoleProp.eraseBond M e).bondsBetween (M.atom e) w = 2 := by
      rw [bondsBetween_eraseBond_of_ne M e (by
        rw [hends]; intro h'; rcases Sym2.eq_iff.mp h' with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hwq h2.symm
        · exact hwp h1.symm)]
      exact hw
    exact afree_pair_ab hL hpg h102s hsz hM e hnoII (M.atom_mem e) hwM hwp.symm (Or.inl (mem_insert_self _ _))
      (hM.eraseBond_deg_p e) (Or.inl ⟨by rw [deg_eraseBond_of_ne M e hwp.symm hwq.symm, hM.reg _ hwM], hbb⟩)
      (by omega) 
  · have hwp : w ≠ M.atom e := fun h => hd (by rw [h, bondsBetween_symm] at hw; exact hw)
    have hwq : w ≠ M.atom (M.mate e) := fun h => by rw [h, bondsBetween_self_eq_zero hM.loop] at hw; omega
    have hwM : w ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := M.atom (M.mate e)) (by omega)
    have h := card_cross_pair M hM.loop hwq.symm
    rw [hw, hM.reg _ (M.atom_mem _), hM.reg _ hwM] at h
    have hbb : (MoleProp.eraseBond M e).bondsBetween (M.atom (M.mate e)) w = 2 := by
      rw [bondsBetween_eraseBond_of_ne M e (by
        rw [hends]; intro h'; rcases Sym2.eq_iff.mp h' with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hpq h1
        · exact hwp h1.symm)]
      exact hw
    exact afree_pair_ab hL hpg h102s hsz hM e hnoII (M.atom_mem _) hwM hwq.symm
      (Or.inr (mem_insert_self _ _)) (hM.eraseBond_deg_q e)
      (Or.inl ⟨by rw [deg_eraseBond_of_ne M e hwp.symm hwq.symm, hM.reg _ hwM], hbb⟩) (by omega) 



end WaveTurbulence.FinalCountG8
