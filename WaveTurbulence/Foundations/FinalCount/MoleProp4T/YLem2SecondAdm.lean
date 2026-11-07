/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Second
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2SecondRungAdm
import Mathlib.Tactic

/-! # DH23 `ylem2`, second statement, for any admissibility

`𝔄(𝕄 ∖ {ℓ}; Adm) ≲ (log L)^C · sup_{P'} 𝔄(𝕄 ∖ chain; lgAdm ∧ Φ)` for every `Adm ⊆ lgAdm` and every condition `Φ` that
holds for the restriction of each `Adm`-decoration to the darts away from the chain. This lets the decoration split of
Prop 10.4(2)′ be pulled back through a (Y) sequence.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

theorem ylem2_second_adm (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (_hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (_E : Y2End C) (e : D),
      (M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set) →
      (∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      ∀ (hYe : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set),
      ∀ Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
        (∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      ∀ Φ : (Degen.RetainedDart M C.set → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → Φ (resY M e C.set hYe κ)) →
        MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            AFreeSupAdm (Degen.eraseAtoms M C.set) d L γ δ C1
              (fun P' τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P' τ ∧ Φ τ) := by
  have hη2 : 0 < η / 2 := by linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by linarith
  obtain ⟨Cs1, hCs1, h1⟩ := oneExit_bound_adm d hd γ hγ η hη hηmax
  obtain ⟨Cs2, hCs2, h2⟩ := twoExit_bound_adm d hd γ hγ η hη hηmax
  obtain ⟨Cs3, hCs3, h3⟩ := ladder_peel_adm d hd γ hγ η hη hηmax
  obtain ⟨Cs4, hCs4, h4⟩ := ladder_peel_adm d hd γ hγ (η / 2) hη2 hη2max
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
  refine ⟨max (max (max (max R1 R2) (max R3 R4)) (Real.exp 1)) ((11 : ℝ) ^ (2 / η)), fun L hL0 => ?_⟩
  have hL := (le_max_left _ _).trans hL0
  have hL11' : (11 : ℝ) ^ (2 / η) ≤ L := (le_max_right _ _).trans hL0
  intro V D _ _ _ M hcap C E e hYe0 hconn P hP hYe Adm hAdm Φ hΦ
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
  have hL11 : 11 ≤ L ^ (η / 2) := by
    calc (11 : ℝ) = ((11 : ℝ) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ L ^ (η / 2) := Real.rpow_le_rpow (by positivity) hL11' (by positivity)
  have hY1 := fun (C' : YChain (MoleProp.eraseBond M e)) (E' : Y1End2 C') Adm' hAdm' =>
    hR1 L hLR1 (MoleProp.eraseBond M e) hcapN E'.toOneExit C'.piece_connected P hP Adm' hAdm'
  have hpeelN := fun (Lad : Ladder3 (MoleProp.eraseBond M e)) Adm' hAdm' =>
    hR3 L hLR3 (MoleProp.eraseBond M e) hmolN Lad P hP Adm' hAdm'
  have hpeelE := fun (Y : Finset V) (Lad : Ladder3 (Degen.eraseAtoms (MoleProp.eraseBond M e) Y)) Adm' hAdm' =>
    hR3 L hLR3 _ (Degen.isMolecule_eraseAtoms (MoleProp.eraseBond M e) hmolN Y) Lad P (nonneg_erase hP Y) Adm' hAdm'
  have hY2 : ∀ (C' : YChain (MoleProp.eraseBond M e)) (E' : Y2End C'),
      (∀ S ∈ MoleProp.ladderCells (E'.toTwoExit hcapN).post, (E'.toTwoExit hcapN).c ∈ S →
        GoodCell (E'.toTwoExit hcapN).post S) →
      ∀ Adm' : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm' κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm' P ≤
        ENNReal.ofReal K * ⨆ g ∈ Finset.Icc (0 : ℤ) 4, AFreeSupAdm (E'.toTwoExit hcapN).post d L γ δ C1
          fun P' => (E'.toTwoExit hcapN).postAdm Adm' (fun _ _ => True) L γ (η / 2) P' g := by
    intro C' E' hg Adm' hAdm'
    have hYt := E'.toTwoExit_Y hcapN
    exact hR2 L hLR2 _ hcapN (E'.toTwoExit hcapN) (by rw [hYt]; exact E'.deg_four) (by rw [hYt]; exact C'.piece_connected)
      hg P hP Adm' hAdm' (fun _ _ => True) (fun κ hκ hsym => by
        obtain ⟨g, hg, hLG⟩ := (E'.toTwoExit hcapN).exists_post_largeGap hL1 hL11 hsym hcapN (hAdm' κ hκ).1
        exact ⟨g, hg, hLG, trivial⟩)
  -- the cases give `𝔄(𝕄 ∖ {ℓ}) ≤ 𝔄(𝕄 ∖ chain)` or the rung bound
  have hcellsE : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms M C.set), 0 ≤ P S := by
    intro S hS
    rw [← ladderCells_eraseBond_erase M e C.set hYe] at hS
    exact nonneg_erase hP _ S hS
  set Tgt := AFreeSupAdm (Degen.eraseAtoms M C.set) d L γ δ C1
    (fun P' τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P' τ ∧ Φ τ)
  have hfinish : MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree (Degen.eraseAtoms M C.set) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M C.set) L γ η P τ ∧ Φ τ) P →
      MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal K * Tgt := by
    intro h
    have hmono : MoleProp.countAFree (Degen.eraseAtoms M C.set) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (Degen.eraseAtoms M C.set) L γ η P τ ∧ Φ τ) P ≤
        MoleProp.countAFree (Degen.eraseAtoms M C.set) L γ δ C1 (0 : Mom d)
          (fun τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P τ ∧ Φ τ) P := by
      unfold MoleProp.countAFree
      exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono (MoleProp.countEFree_mono _ L γ δ 0
        fun κ h => ⟨lgAdm_mono _ hL1 (by linarith) h.1, h.2⟩)) bot_le
    refine h.trans (hmono.trans ?_)
    calc MoleProp.countAFree (Degen.eraseAtoms M C.set) L γ δ C1 (0 : Mom d)
          (fun τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P τ ∧ Φ τ) P
        ≤ 1 * Tgt := by
          rw [one_mul]
          exact le_iSup₂_of_le (f := fun P' (_ : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms M C.set), 0 ≤ P' S) =>
            MoleProp.countAFree (Degen.eraseAtoms M C.set) L γ δ C1 (0 : Mom d)
              (fun τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P' τ ∧ Φ τ) P') P hcellsE le_rfl
      _ ≤ _ := mul_le_mul' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK) le_rfl
  have hmain : MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal K * Tgt := by
    by_cases hu : M.atom e ∈ C.set <;> by_cases hw : M.atom (M.mate e) ∈ C.set
    · -- an internal bond
      obtain ⟨i, hi, hai | hbi⟩ := C.mem_set.mp hu
      · have hnb := E.mate_mem_nbA hi hai hw
        rcases Y2End.mem_nbA_iff.mp hnb with h | ⟨h0, h⟩ | ⟨h0, h⟩
        · have he : M.ends e = s(C.a i, C.b i) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hai, h]
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact hfinish (E.triple_case_adm e he P C.set rfl hYe Adm hAdm Φ hΦ hpeelN)
          · exact E.rung_case_adm hpos hi e he hcapN hconn P C.set rfl hYe Adm hAdm Φ hΦ hY2
              (fun N2 hN2 Lad P' hP' Adm2 hAdm2 => hR4 L hLR4 N2 hN2 Lad P' hP' Adm2 hAdm2)
        · have he : M.ends e = s(C.a (i - 1), C.a (i - 1 + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _
            rw [hai, h, Nat.sub_add_cancel h0]; exact Sym2.eq_swap
          exact hfinish (E.rail_a_case_adm (k := i - 1) (by omega) e he P C.set rfl hYe Adm hAdm Φ hΦ hY1 hpeelE)
        · have he : M.ends e = s(C.a i, C.a (i + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hai, h]
          exact hfinish (E.rail_a_case_adm h0 e he P C.set rfl hYe Adm hAdm Φ hΦ hY1 hpeelE)
      · have hnb := E.mate_mem_nbB hi hbi hw
        rcases Y2End.mem_nbB_iff.mp hnb with h | ⟨h0, h⟩ | ⟨h0, h⟩
        · have he : M.ends e = s(C.a i, C.b i) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hbi, h]; exact Sym2.eq_swap
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact hfinish (E.triple_case_adm e he P C.set rfl hYe Adm hAdm Φ hΦ hpeelN)
          · exact E.rung_case_adm hpos hi e he hcapN hconn P C.set rfl hYe Adm hAdm Φ hΦ hY2
              (fun N2 hN2 Lad P' hP' Adm2 hAdm2 => hR4 L hLR4 N2 hN2 Lad P' hP' Adm2 hAdm2)
        · have he : M.ends e = s(C.b (i - 1), C.b (i - 1 + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _
            rw [hbi, h, Nat.sub_add_cancel h0]; exact Sym2.eq_swap
          exact hfinish (E.rail_b_case_adm (k := i - 1) (by omega) e he P C.set rfl hYe Adm hAdm Φ hΦ hY1 hpeelE)
        · have he : M.ends e = s(C.b i, C.b (i + 1)) := by
            change s(M.atom e, M.atom (M.mate e)) = _; rw [hbi, h]
          exact hfinish (E.rail_b_case_adm h0 e he P C.set rfl hYe Adm hAdm Φ hΦ hY1 hpeelE)
    · -- `e` leaves the chain: an exit
      have hc : e ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hu, hw⟩
      rw [E.cross_eq] at hc
      rcases mem_insert.mp hc with h | h
      · exact hfinish (E.exit_case_adm e (by rw [h]) P C.set rfl hYe Adm hAdm Φ hΦ hY1)
      · have he : M.ends e = M.ends E.y := by rw [mem_singleton.mp h]
        exact hfinish (E.swap.exit_case_adm (C := C.swap) e he P C.set C.swap_set hYe Adm hAdm Φ hΦ hY1)
    · -- `mate e` leaves the chain: `ℓ` is an exit
      have hc : M.mate e ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hw, by rw [M.mate_mate]; exact hu⟩
      rw [E.cross_eq] at hc
      rcases mem_insert.mp hc with h | h
      · have he : M.ends e = M.ends E.x := by rw [← h, ends_mate]
        exact hfinish (E.exit_case_adm e he P C.set rfl hYe Adm hAdm Φ hΦ hY1)
      · have he : M.ends e = M.ends E.y := by rw [← mem_singleton.mp h, ends_mate]
        exact hfinish (E.swap.exit_case_adm (C := C.swap) e he P C.set C.swap_set hYe Adm hAdm Φ hΦ hY1)
    · exact absurd hYe (by tauto)
  exact hmain

end WaveTurbulence.MoleProp4
