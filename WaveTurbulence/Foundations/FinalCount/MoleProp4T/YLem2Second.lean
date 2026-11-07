/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2SecondCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2SecondRung
import Mathlib.Tactic

/-! # DH23 Lemma `ylem2`, second statement (L1950, proof L1956)

Let `𝕄′` come from `𝕄` by one (Y) sequence ending in (Y2), with new bond `ℓ′`, and let `ℓ` be a bond removed by the
sequence (an end of `ℓ` is a chain atom). Then `𝔄(𝕄 ∖ {ℓ}) ≲ (log L)^C 𝔄(𝕄′ ∖ {ℓ′})`.

`𝕄′ ∖ {ℓ′} = 𝕄 ∖ chain`. The proof distinguishes the position of `ℓ` (exit, copy of the triple bond, copy of a rung,
rail) and uses only the (Y1) case 2 bound, operation (b) and, for a rung copy, the first statement on the pairs below
`ℓ`; see `YLem2SecondCases`, `YLem2SecondRung`. This is the counting order of DH23 L1956 (start at the atom of `ℓ`,
then propagate), as the referee's reading 3.3(b) requires; no fixed exit labels are used.

Hypothesis beyond DH23: `𝕄 ∖ {ℓ}` is connected (Theorem A's setting: `𝕄` is 4-regular and connected, so has no bridge).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- `𝕄′ ∖ {ℓ′} ≅ 𝕄 ∖ Y`: removing the new bond from the post molecule. -/
def eraseNewEquiv : Degen.RetainedDart N T.Y ≃ MoleProp.WithoutBondDart T.post (Sum.inr true) where
  toFun w := ⟨Sum.inl w, Sum.inl_ne_inr, Sum.inl_ne_inr⟩
  invFun z := match z with
    | ⟨Sum.inl w, _⟩ => w
    | ⟨Sum.inr bo, h⟩ => absurd (by cases bo <;> [exact h.2 rfl; exact (h.1 rfl).elim]) id
  left_inv w := rfl
  right_inv z := by
    obtain ⟨w | bo, h⟩ := z
    · rfl
    · cases bo
      · exact (h.2 rfl).elim
      · exact (h.1 rfl).elim

theorem afreeSup_le_post_minus_new {d : ℕ} (L γ δ η C1 : ℝ) :
    AFreeSup (Degen.eraseAtoms N T.Y) d L γ δ η C1 ≤
      AFreeSup (MoleProp.eraseBond T.post (Sum.inr true)) d L γ δ η C1 :=
  afreeSup_le_of_dart_equiv _ _ T.eraseNewEquiv (by change N.atoms \ T.Y = T.post.atoms; rw [T.post_atoms])
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) L γ δ η C1

end TwoExit

theorem one_le_ylem2Const {L : ℝ} (hlog : 1 ≤ Real.log L) :
    1 ≤ 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 := by
  have h1 : (1 : ℝ) ≤ (scaleSet L).card := by
    exact_mod_cast card_pos.mpr ⟨0, by simp [scaleSet]⟩
  have h2 : (1 : ℝ) ≤ Real.log L ^ 2 := one_le_pow₀ hlog
  have h3 : (1 : ℝ) ≤ (Real.log L ^ 2) ^ 6 := one_le_pow₀ h2
  have h4 : (1 : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := one_le_pow₀ h1
  nlinarith

/-- **DH23 Lemma `ylem2`, second statement**: `𝔄(𝕄 ∖ {ℓ}) ≲ (log L)^C 𝔄(𝕄′ ∖ {ℓ′})` for `ℓ` removed by a (Y)
sequence ending in (Y2). Constant `110 |scaleSet L|² (log L)^{12}`; LG parameter `η` on the left, `η/2` on the right. -/
theorem ylem2_second (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (E : Y2End C) (e : D),
      (M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set) →
      (∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
        AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            AFreeSup (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)) d L γ δ (η / 2) C1 := by
  have hη2 : 0 < η / 2 := by linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by linarith
  obtain ⟨Cs1, hCs1, h1⟩ := ylem2_Y1c2 d hd γ hγ η hη hηmax
  obtain ⟨Cs2, hCs2, h2⟩ := ylem2_Y2 d hd γ hγ η hη hηmax
  obtain ⟨Cs3, hCs3, h3⟩ := ladder_peel d hd γ hγ η hη hηmax
  obtain ⟨Cs4, hCs4, h4⟩ := ladder_peel d hd γ hγ (η / 2) hη2 hη2max
  refine ⟨max (max Cs1 Cs2) (max Cs3 Cs4), hCs1.trans ((le_max_left _ _).trans (le_max_left _ _)),
    fun C1 hC1 δ hδ => ?_⟩
  have hm := le_max_left (max Cs1 Cs2) (max Cs3 Cs4)
  have hm' := le_max_right (max Cs1 Cs2) (max Cs3 Cs4)
  have e1 : C1 ≥ 2 * Cs1 := by linarith [le_max_left Cs1 Cs2, le_max_right Cs1 Cs2]
  have e2 : C1 ≥ 2 * Cs2 := by linarith [le_max_right Cs1 Cs2]
  have e3 : C1 ≥ Cs3 := by linarith [le_max_left Cs3 Cs4, le_max_left Cs1 Cs2]
  have e4 : C1 ≥ Cs4 := by linarith [le_max_right Cs3 Cs4, le_max_left Cs1 Cs2]
  obtain ⟨R1, hR1⟩ := h1 C1 e1 δ hδ
  obtain ⟨R2, hR2⟩ := h2 C1 e2 δ hδ
  obtain ⟨R3, hR3⟩ := h3 C1 e3 δ hδ
  obtain ⟨R4, hR4⟩ := h4 C1 e4 δ hδ
  refine ⟨max (max (max R1 R2) (max R3 R4)) (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ M hcap C E e hYe hconn P hP
  classical
  have hL' := (le_max_left _ _).trans hL
  have hLR1 : R1 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL'
  have hLR2 : R2 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL'
  have hLR3 : R3 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL'
  have hLR4 : R4 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL'
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  set K := 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6
  have hK : 1 ≤ K := one_le_ylem2Const hlog
  have hcapN := caps_eraseBond M e hcap
  -- `𝕄 ∖ {ℓ}` is a molecule
  have hmolN : (MoleProp.eraseBond M e).IsMolecule := by
    obtain ⟨z, hz, hzY⟩ : ∃ z, (M.atom e = z ∨ M.atom (M.mate e) = z) ∧ z ∈ C.set := by
      rcases hYe with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    refine isMolecule_of_connected (MoleProp.eraseBond M e) hcapN hconn (C.set_sub hzY) ?_
    have := deg_eraseBond_add M e z
    rw [E.deg_four z hzY] at this
    rcases hz with h | h
    · rw [ite_of_pos h] at this; omega
    · rw [ite_of_pos h] at this; omega
  -- the general bounds at this `L`
  have hY1 : ∀ (C' : YChain (MoleProp.eraseBond M e)), Y1End2 C' → AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) C'.set) d L γ δ η C1 P :=
    fun C' E' => hR1 L hLR1 (MoleProp.eraseBond M e) hcapN C' E' P hP
  have hpeelN : ∀ Lad : Ladder3 (MoleProp.eraseBond M e), AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Lad.set) d L γ δ η C1 P :=
    fun Lad => hR3 L hLR3 (MoleProp.eraseBond M e) hmolN Lad P hP
  have hpeelE : ∀ (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y)),
      AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) d L γ δ η C1 P ≤
        AFree (Degen.eraseAtoms (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) Lad.set) d L γ δ η C1 P :=
    fun Y Lad => hR3 L hLR3 _ (Degen.isMolecule_eraseAtoms (MoleProp.eraseBond M e) hmolN Y) Lad P (nonneg_erase hP Y)
  -- the cases give `𝔄(𝕄 ∖ {ℓ}) ≤ 𝔄(𝕄 ∖ chain)` or the rung bound
  have hcellsE : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms M C.set), 0 ≤ P S := by
    intro S hS
    rw [← ladderCells_eraseBond_erase M e C.set hYe] at hS
    exact nonneg_erase hP _ S hS
  have hfinish : AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms M C.set) d L γ δ η C1 P →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ ENNReal.ofReal K * AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1 := by
    intro h
    refine h.trans ((afree_mono_eta (η := η) (η' := η / 2) _ hL1 (by linarith) P).trans ((afree_le_afreeSup _ P hcellsE).trans ?_))
    calc AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1
        = 1 * AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1 := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK) le_rfl
  have hmain : AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤ ENNReal.ofReal K * AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1 := by
    by_cases hu : M.atom e ∈ C.set <;> by_cases hw : M.atom (M.mate e) ∈ C.set
    · -- an internal bond
      obtain ⟨i, hi, hai | hbi⟩ := C.mem_set.mp hu
      · have hnb := E.mate_mem_nbA hi hai hw
        rcases Y2End.mem_nbA_iff.mp hnb with h | ⟨h0, h⟩ | ⟨h0, h⟩
        · have he : M.ends e = s(C.a i, C.b i) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hai, h]
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact hfinish (E.triple_case e he P hpeelN)
          · exact E.rung_case hpos hi e he hcapN hconn P (fun C' E' hg => hR2 L hLR2 (MoleProp.eraseBond M e) hcapN C' E' hg P hP)
              (fun N2 hN2 Lad P' hP' => hR4 L hLR4 N2 hN2 Lad P' hP')
        · have he : M.ends e = s(C.a (i - 1), C.a (i - 1 + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _
            rw [hai, h, Nat.sub_add_cancel h0]; exact Sym2.eq_swap
          exact hfinish (E.rail_a_case (k := i - 1) (by omega) e he P hY1 hpeelE)
        · have he : M.ends e = s(C.a i, C.a (i + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hai, h]
          exact hfinish (E.rail_a_case h0 e he P hY1 hpeelE)
      · have hnb := E.mate_mem_nbB hi hbi hw
        rcases Y2End.mem_nbB_iff.mp hnb with h | ⟨h0, h⟩ | ⟨h0, h⟩
        · have he : M.ends e = s(C.a i, C.b i) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hbi, h]; exact Sym2.eq_swap
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact hfinish (E.triple_case e he P hpeelN)
          · exact E.rung_case hpos hi e he hcapN hconn P (fun C' E' hg => hR2 L hLR2 (MoleProp.eraseBond M e) hcapN C' E' hg P hP)
              (fun N2 hN2 Lad P' hP' => hR4 L hLR4 N2 hN2 Lad P' hP')
        · have he : M.ends e = s(C.b (i - 1), C.b (i - 1 + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _
            rw [hbi, h, Nat.sub_add_cancel h0]; exact Sym2.eq_swap
          exact hfinish (E.rail_b_case (k := i - 1) (by omega) e he P hY1 hpeelE)
        · have he : M.ends e = s(C.b i, C.b (i + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hbi, h]
          exact hfinish (E.rail_b_case h0 e he P hY1 hpeelE)
    · -- `e` leaves the chain: an exit
      have hc : e ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hu, hw⟩
      rw [E.cross_eq] at hc
      rcases mem_insert.mp hc with h | h
      · exact hfinish (E.exit_case e (by rw [h]) P hY1)
      · have he : M.ends e = M.ends E.y := by rw [mem_singleton.mp h]
        have h' := E.swap.exit_case (C := C.swap) e he P hY1
        rw [C.swap_set] at h'
        exact hfinish h'
    · -- `mate e` leaves the chain: `ℓ` is an exit
      have hc : M.mate e ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hw, by rw [M.mate_mate]; exact hu⟩
      rw [E.cross_eq] at hc
      rcases mem_insert.mp hc with h | h
      · have he : M.ends e = M.ends E.x := by rw [← h, ends_mate]
        exact hfinish (E.exit_case e he P hY1)
      · have he : M.ends e = M.ends E.y := by rw [← mem_singleton.mp h, ends_mate]
        have h' := E.swap.exit_case (C := C.swap) e he P hY1
        rw [C.swap_set] at h'
        exact hfinish h'
    · exact absurd hYe (by tauto)
  refine hmain.trans (mul_le_mul' le_rfl ?_)
  have hY := E.toTwoExit_Y hcap
  have := (E.toTwoExit hcap).afreeSup_le_post_minus_new (d := d) L γ δ (η / 2) C1
  calc AFreeSup (Degen.eraseAtoms M C.set) d L γ δ (η / 2) C1
      = AFreeSup (Degen.eraseAtoms M (E.toTwoExit hcap).Y) d L γ δ (η / 2) C1 := by rw [hY]
    _ ≤ _ := this

end WaveTurbulence.MoleProp4
