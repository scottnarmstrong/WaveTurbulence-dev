/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCommon
public import WaveTurbulence.Foundations.FinalCount.MoleProp.PropositionThree
public import WaveTurbulence.Foundations.FinalCount.MoleProp.PropositionOne
import Mathlib.Tactic

/-! # Core cases: only single bonds; a cut vertex

DH23 L1963:
* "if `M′` has only single bonds, then the result for `𝔄(M′∖ℓ′)` follows from Proposition 10.3" (G6's
  `proposition_three_normalized_bound`): the second alternative for every decoration;
* "if `M′` admits a β-cut … by performing this cut … we can divide `M′` … into two molecules with `E = 2V − 1` and no
  triple bonds, so the result for `𝔄(M′)` … follows from Proposition 10.2": the first alternative for every decoration.
  A cut vertex `w` of a 4-regular `𝕄` has a side `C₁` attached by exactly two bonds at `w` (parity), and the β-cut
  pieces are the pieces on `C₁ ∪ {w}` and on the complement of `C₁`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- G6's Prop 10.3 at a fixed `L`. -/
def Prop103At (d : ℕ) (L γ δ η C1 : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    (∀ x, M.atom x ≠ M.atom (M.mate x)) → (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → MoleProp.TwoThreeProfile M →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ κ, Adm κ → MoleProp.LargeGap M L γ η 0 κ) →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(min γ (1 - γ) + η / 2)))

theorem prop103At_of_G6 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ min γ (1 - γ) / 200) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      Prop103At.{u, v} d L γ δ η C1 := by
  obtain ⟨Cs, hCs, h⟩ := MoleProp.proposition_three_normalized_bound d hd γ hγ η hη hηsmall
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h C1 hC1 δ hδ
  exact ⟨R, fun L hL V D _ _ _ M => hR L hL M⟩

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Case 0: only single bonds** — the second alternative, by Prop 10.3. -/
theorem case_simple {d : ℕ} {L γ δ η C1 : ℝ} (h103 : Prop103At.{u, v} d L γ δ η C1) {M : Molecule V D}
    (hM : IsCore M) (e : D) (hs : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) (ε₁ : ℝ) :
    SplitBound M e d L γ δ η C1 ε₁ (L ^ (-(min γ (1 - γ) + η / 2))) := by
  refine splitBound_of_second M e fun P _ => ?_
  refine h103 _ (hM.eraseBond_isMolecule e) (hM.eraseBond_loop e)
    (fun a b hab => (bondsBetween_eraseBond_le' M e a b).trans (hs a b hab)) (hM.eraseBond_conn e) ?_ _ P
    (fun κ h => h.1)
  refine ⟨M.atom e, M.atom_mem e, M.atom (M.mate e), M.atom_mem _, hM.loop e, hM.eraseBond_deg_p e,
    hM.eraseBond_deg_q e, fun z hz h1 h2 => ?_⟩
  rw [deg_eraseBond_of_ne M e (Ne.symm h1) (Ne.symm h2)]
  exact hM.reg z hz

omit [DecidableEq D] in
/-- Crossing darts of `S ∪ {w}` when every dart leaving `S` goes to `w`. -/
theorem card_cross_insert (M : Molecule V D) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {S : Finset V} {w : V}
    (hw : w ∉ S) (hcl : ∀ x ∈ crossDarts M S, M.atom (M.mate x) = w) :
    (crossDarts M (insert w S)).card + (crossDarts M S).card = M.deg w := by
  classical
  have h1 : crossDarts M (insert w S) = (M.dartsAt w).filter fun x => M.atom (M.mate x) ∉ S := by
    ext x
    simp only [mem_crossDarts, mem_insert, Molecule.dartsAt, mem_filter, mem_univ, true_and, not_or]
    constructor
    · rintro ⟨hx | hx, hm1, hm2⟩
      · exact ⟨hx, hm2⟩
      · exact absurd (hcl x (mem_crossDarts.mpr ⟨hx, hm2⟩)) hm1
    · rintro ⟨hx, hm⟩
      exact ⟨Or.inl hx, fun h => hloop x (hx.trans h.symm), hm⟩
  have h2 : (crossDarts M S).card = ((M.dartsAt w).filter fun x => M.atom (M.mate x) ∈ S).card := by
    refine card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      obtain ⟨h1, _⟩ := mem_crossDarts.mp hx
      simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
      exact ⟨hcl x hx, by rw [M.mate_mate]; exact h1⟩
    · intro x _ y _ h; have := congrArg M.mate h; rwa [M.mate_mate, M.mate_mate] at this
    · intro x hx
      simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx
      refine ⟨M.mate x, mem_crossDarts.mpr ⟨hx.2, by rw [M.mate_mate, hx.1]; exact hw⟩, M.mate_mate x⟩
  rw [h1, h2, add_comm, card_filter_add_card_filter_not]
  rfl

/-- **Case A: a cut vertex** — the first alternative, by the β-cut input and Prop 10.2 on both sides. -/
theorem case_cut {d : ℕ} {L γ δ η C1 K B : ℝ} (hL : 0 < L) (hbeta : BetaCutAt.{u, v} d L γ δ η C1 K B)
    {m : ℕ} (h102 : Prop102At.{u, v} d L γ δ η C1 m) {M : Molecule V D}
    (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) (hM : IsCore M) (e : D)
    {w a b : V} (hw : w ∈ M.atoms) (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (haw : a ≠ w) (hbw : b ≠ w)
    (hab : ¬ (Degen.eraseAtoms M {w}).SameComponent a b) (ε₂ : ℝ) :
    SplitBound M e d L γ δ η C1
      (K * Real.log L ^ B * (M.atoms.card + 1) * (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ)))))
      ε₂ := by
  classical
  have ha' : a ∈ M.atoms \ {w} := mem_sdiff.mpr ⟨ha, by simpa using haw⟩
  have hb' : b ∈ M.atoms \ {w} := mem_sdiff.mpr ⟨hb, by simpa using hbw⟩
  obtain ⟨C₁, C₂, h1, h2, ha1, hb2, hdisj, hcl1, _, hcard⟩ := erase_disconnected_cross M {w} ha' hb' hab
  rw [card_cross_singleton M hM.loop, hM.reg w hw] at hcard
  have hC₁ : C₁ ⊆ M.atoms := h1.trans sdiff_subset
  have hC₂ : C₂ ⊆ M.atoms := h2.trans sdiff_subset
  have hwC₁ : w ∉ C₁ := fun h => (mem_sdiff.mp (h1 h)).2 (mem_singleton_self w)
  have hk := two_le_cross_of_reg M hM.reg hM.conn
  have k1 := hk C₁ hC₁ a ha1 w hw hwC₁
  have k2 := hk C₂ hC₂ b hb2 w hw (fun h => (mem_sdiff.mp (h2 h)).2 (mem_singleton_self w))
  have hc2 : (crossDarts M C₁).card = 2 := by omega
  have hto : ∀ x ∈ crossDarts M C₁, M.atom (M.mate x) = w := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_crossDarts.mp hx
    by_contra hne
    exact hx2 (hcl1 x hx1 (by simpa using hne))
  have hins := card_cross_insert M hM.loop hwC₁ hto
  rw [hM.reg w hw, hc2] at hins
  have hinsC : insert w C₁ ⊆ M.atoms := insert_subset hw hC₁
  have hcomp : M.atoms \ C₁ ⊆ M.atoms := sdiff_subset
  have hcc : (crossDarts M (M.atoms \ C₁)).card = 2 := by rw [card_crossDarts_compl, hc2]
  -- the two pieces are connected (fewer than four crossing darts)
  have hconn1 := piece_connected_of_cross M hk hinsC (by omega : (crossDarts M (insert w C₁)).card < 2 * 2)
  have hconn2 := piece_connected_of_cross M hk hcomp (by omega : (crossDarts M (M.atoms \ C₁)).card < 2 * 2)
  -- bond counts
  have hE1 : ((piece M (insert w C₁)).bonds.card : ℤ) = 2 * (insert w C₁).card - 1 := by
    have h := two_mul_piece_bonds M hinsC
    rw [sum_congr rfl fun v hv => hM.reg v (hinsC hv), sum_const, smul_eq_mul] at h
    omega
  have hE2 : ((piece M (M.atoms \ C₁)).bonds.card : ℤ) = 2 * (M.atoms \ C₁).card - 1 := by
    have h := two_mul_piece_bonds M hcomp
    rw [sum_congr rfl fun v hv => hM.reg v (hcomp hv), sum_const, smul_eq_mul] at h
    omega
  -- low-degree atoms
  obtain ⟨x₁, hx₁⟩ : (crossDarts M (insert w C₁)).Nonempty := card_pos.mp (by omega)
  obtain ⟨x₂, hx₂⟩ : (crossDarts M (M.atoms \ C₁)).Nonempty := card_pos.mp (by omega)
  have hz1 := piece_deg_lt M hx₁
  have hz2 := piece_deg_lt M hx₂
  rw [hM.reg _ (M.atom_mem _)] at hz1 hz2
  have hA1 := afreeSup_piece_le h102 M hsz hinsC hM.cap hM.le2 hconn1 (mem_crossDarts.mp hx₁).1 (by omega) hE1
  have hA2 := afreeSup_piece_le h102 M hsz hcomp hM.cap hM.le2 hconn2 (mem_crossDarts.mp hx₂).1 (by omega) hE2
  refine splitBound_of_first M e fun P hP => ?_
  have hmain := hbeta M hM.cap hM.loop w C₁ hw hC₁ hwC₁ hc2 hto hM.conn hconn1 hconn2 P hP
  refine hmain.trans ((mul_le_mul' (mul_le_mul' le_rfl hA1) hA2).trans ?_)
  have hpos : 0 ≤ L ^ (-(3 / 5 * min γ (1 - γ))) := Real.rpow_nonneg hL.le _
  rw [mul_assoc, ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul' (mul_nonneg hpos hpos)]

end WaveTurbulence.MoleProp4
