/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Peel
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExitBound
import Mathlib.Tactic

/-! # The no-loss removals for any admissibility below `lgAdm`

Operation (b) ladder peels and the (Y1) case 2 removal, with `N`'s decorations restricted by any `Adm ⊆ lgAdm`; the
erased molecule's decorations are then the restrictions (`erasedFreeAdmissibility`) of `Adm`-decorations.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem erasedFree_sub_lgAdm (N : Molecule V D) (Y : Finset V) {d : ℕ} {L γ η : ℝ} {P : Finset V → ℝ}
    {Adm : (D → (Fin d → ℤ)) → Prop} (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ) (κ' : Degen.RetainedDart N Y → (Fin d → ℤ))
    (h : MoleProp.erasedFreeAdmissibility N Y Adm κ') : lgAdm (Degen.eraseAtoms N Y) L γ η P κ' := by
  obtain ⟨κ0, h0, _, rfl⟩ := h
  exact ⟨MoleProp.largeGap_erase N L γ η 0 _ (hAdm κ0 h0).1,
    MoleProp.cellGapRestriction_erase N L 0 _ P _ (hAdm κ0 h0).2⟩

/-- **Peeling a `Ladder3` by operation (b), for any admissibility below `lgAdm`.** -/
theorem ladder_peel_adm (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D), N.IsMolecule →
      ∀ Lad : Ladder3 N, ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm N L γ η P κ) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          MoleProp.countAFree (Degen.eraseAtoms N Lad.set) L γ δ C1 (0 : Mom d)
            (MoleProp.erasedFreeAdmissibility N Lad.set Adm) P := by
  obtain ⟨Cstar, hCstar, hB⟩ := MoleProp.operation_b_normalized_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hB C1 hC1 δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hN Lad P hP Adm hAdm
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have key : ∀ k : ℕ, ∀ {D : Type _} [Fintype D] [DecidableEq D] (N : Molecule V D), N.IsMolecule →
      ∀ Lad : Ladder3 N, Lad.m = k → ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm N L γ η P κ) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          MoleProp.countAFree (Degen.eraseAtoms N Lad.set) L γ δ C1 (0 : Mom d)
            (MoleProp.erasedFreeAdmissibility N Lad.set Adm) P := by
    intro k
    induction k with
    | zero =>
      intro D _ _ N hN Lad hk P hP Adm hAdm
      rw [Lad.set_zero hk]
      exact hR L hLR hlog N hN _ (Lad.mem 0 (Nat.zero_le _)).1 _ (Lad.mem 0 (Nat.zero_le _)).2
        (Lad.ne_ab 0 (Nat.zero_le _) 0 (Nat.zero_le _)) Lad.deg0.1 (Or.inl Lad.deg0.2) (Lad.rung 0 (Nat.zero_le _))
        Adm P (fun κ h => (hAdm κ h).1) (fun κ h => (hAdm κ h).2) hP
    | succ k ih =>
      intro D _ _ N hN Lad hk P hP Adm hAdm
      have hm : 0 < Lad.m := by omega
      have h1 := hR L hLR hlog N hN _ (Lad.mem 0 (Nat.zero_le _)).1 _ (Lad.mem 0 (Nat.zero_le _)).2
        (Lad.ne_ab 0 (Nat.zero_le _) 0 (Nat.zero_le _)) Lad.deg0.1 (Or.inl Lad.deg0.2) (Lad.rung 0 (Nat.zero_le _))
        Adm P (fun κ h => (hAdm κ h).1) (fun κ h => (hAdm κ h).2) hP
      have h2 := ih (Degen.eraseAtoms N {Lad.a 0, Lad.b 0}) (Degen.isMolecule_eraseAtoms N hN _) (Lad.shift hm)
        (by change Lad.m - 1 = k; omega) P (nonneg_erase hP _) _ (erasedFree_sub_lgAdm N _ hAdm)
      rw [Lad.set_eq_shift hm]
      exact h1.trans (h2.trans (MoleProp.countAFree_erase_twice_le_union N _ _ L γ δ C1 0 Adm P))
  exact key Lad.m N hN Lad rfl P hP Adm hAdm

/-- **The one-exit removal bound, for any admissibility below `lgAdm`.** -/
theorem oneExit_bound_adm (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D),
      (∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) → ∀ T : OneExit N,
      (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm N L γ η P κ) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
            (MoleProp.erasedFreeAdmissibility N T.Y Adm) P := by
  obtain ⟨Cstar, hCstar, h101⟩ := MoleProp.molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h101 (C1 / 2) (by linarith) δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hcap T hconn P hP Adm hAdm
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have hxdeg : (piece N T.Y).deg (N.atom T.x) ≠ 4 := by
    have h := deg_eraseAtoms_add (N := N) (N.atoms \ T.Y) (fun h => (mem_sdiff.mp h).2 T.atom_x)
    have hx : T.x ∈ Degen.removedDartsAt N (N.atoms \ T.Y) (N.atom T.x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
        Finset.mem_sdiff.mpr ⟨N.atom_mem _, T.c_notMem⟩⟩
    have hpos := card_pos.mpr ⟨_, hx⟩
    have h4 := hcap _ (N.atom_mem T.x)
    have hsum := Mole.outdeg_add_indeg N (N.atom T.x)
    change (Degen.eraseAtoms N (N.atoms \ T.Y)).deg (N.atom T.x) ≠ 4
    omega
  have hmol := piece_isMolecule T.sub hcap hconn T.atom_x hxdeg
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := fun S hS => by
    have := (mem_filter.mp hS).2
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N
      ((isLadderCell_piece_iff S).mp this).1), ((isLadderCell_piece_iff S).mp this).1⟩)
  have hPerase := nonneg_erase hP T.Y
  have hpiece := hR L hLR (piece N T.Y) hmol (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P
    (fun κ h => (erasedFree_sub_lgAdm N _ hAdm κ h).1) (fun κ h => (erasedFree_sub_lgAdm N _ hAdm κ h).2) hPpiece
  have hcount := T.countEFree_le (d := d) (γ := γ) (δ := δ) hLp Adm
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one (piece N T.Y)
    (by rw [piece_atoms T.sub]; exact ⟨N.atom T.x, T.atom_x⟩) (by rw [piece_atoms T.sub]; exact hconn)
  have hrank := T.circuitRank_identity
  have hFle := T.erase_numComponents_le
  have np := MoleProp.freeNormalization_pos (piece N T.Y) (d := d) (γ := γ) hLp hδ.1 (by linarith : (0 : ℝ) < C1 / 2)
    hlog0 P hPpiece
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms N T.Y) (d := d) (γ := γ) hLp hδ.1
    (by linarith : (0 : ℝ) < C1) hlog0 P hPerase
  have hcells := T.ladderCells_eq_union
  have hratio : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ (C1 / 2) P *
        MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
          ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1) := by
    unfold MoleProp.freeNormalization
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    refine norm_ratio hL1 (by linarith [hγ.2]) hδ.1 hδ.2 (by linarith) (by linarith)
      (by rw [hFp] at hrank; omega) (MoleProp.circuitRank_nonneg _)
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPpiece).le
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le zero_le_one ?_
    rw [hcells, mul_one]
  have hhalf : (1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1 ≤ 1 := by
    rw [mul_one]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (MoleProp.circuitRank_nonneg (piece N T.Y))
    rw [hn, zpow_natCast]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) *
          MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N T.Y Adm) : ℕ∞) :
            ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ (C1 / 2) P *
              MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
                ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1)) :=
        mul_le_mul' (ENat.toENNReal_mono hcount) (ENNReal.ofReal_le_ofReal hratio)
    _ = (MoleProp.countAFree (piece N T.Y) L γ δ (C1 / 2) (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P) *
        (MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y Adm) P) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1) := by
        rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization, ENat.toENNReal_mul,
          ENNReal.ofReal_mul (mul_nonneg np.le ne.le), ENNReal.ofReal_mul np.le]
        ring
    _ ≤ 1 * (MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y Adm) P) * 1 :=
        mul_le_mul' (mul_le_mul' hpiece le_rfl) (ENNReal.ofReal_le_one.mpr hhalf)
    _ = _ := by ring

end WaveTurbulence.MoleProp4
