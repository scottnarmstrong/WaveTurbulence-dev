/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitBound
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNormAdm
import Mathlib.Tactic

/-! # The (Y2) bound with constants, for any admissibility below `lgAdm`

`𝔄(N; Adm) ≤ 110 |scaleSet L|² (log L)^{12} · sup_{g, P'} 𝔄(post; postAdm Adm W g P')`, for any `Adm ⊆ lgAdm` and any
"multiplier witness" `W` for which every `Adm`-decoration has a multiplier `g` with large gaps on the post molecule
and `W g`. With `W = ⊤` the witness exists for large `L` (`exists_post_largeGap`).
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

/-- The supremum of `𝔄` over nonnegative scale functions, for an admissibility depending on the scales. -/
noncomputable def AFreeSupAdm {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (d : ℕ)
    (L γ δ C1 : ℝ) (Adm : (Finset V → ℝ) → (D → (Fin d → ℤ)) → Prop) : ℝ≥0∞ :=
  ⨆ (P : Finset V → ℝ) (_ : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S), MoleProp.countAFree M L γ δ C1 (0 : Mom d) (Adm P) P

/-- **The two-exit removal bound for any admissibility below `lgAdm`.** -/
theorem twoExit_bound_adm (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D),
      (∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) → ∀ T : TwoExit N,
      (∀ v ∈ T.Y, N.deg v = 4) → (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      (∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ (Adm : (D → (Fin d → ℤ)) → Prop), (∀ κ, Adm κ → lgAdm N L γ η P κ) →
      ∀ (W : ℤ → (D → (Fin d → ℤ)) → Prop), (∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) →
        ∃ g ∈ Finset.Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ W g κ) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            ⨆ g ∈ Finset.Icc (0 : ℤ) 4, AFreeSupAdm T.post d L γ δ C1 fun P' => T.postAdm Adm W L γ (η / 2) P' g := by
  obtain ⟨Cstar, hCstar, h101⟩ := MoleProp.molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h101 (C1 / 2) (by linarith) δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hcap T hdegY hconn hopen P hP Adm hAdm W hW
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  by_cases hlo : ∃ z : D, N.atom z = N.atom (N.mate z)
  · obtain ⟨z, hz⟩ := hlo
    rw [MoleProp.countAFree_eq_zero_of_loop N hLp γ δ C1 η 0 _ (fun κ h => (hAdm κ h).1) P z hz]
    exact bot_le
  have hloop : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z h => hlo ⟨z, h⟩
  have hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4 := fun a ha => by
    have h := hcap a ha
    have hsum := Mole.outdeg_add_indeg N a
    omega
  have hxdeg : (piece N T.Y).deg (N.atom T.x) ≠ 4 := by
    have h := deg_eraseAtoms_add (N := N) (N.atoms \ T.Y) (fun h => (mem_sdiff.mp h).2 T.atom_x)
    have hx : T.x ∈ Degen.removedDartsAt N (N.atoms \ T.Y) (N.atom T.x) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
        Finset.mem_sdiff.mpr ⟨N.atom_mem _, T.c_notMem⟩⟩
    have hpos := card_pos.mpr ⟨_, hx⟩
    have h4 := hdegY _ T.atom_x
    change (Degen.eraseAtoms N (N.atoms \ T.Y)).deg (N.atom T.x) ≠ 4
    omega
  have hmol := piece_isMolecule T.sub hcap hconn T.atom_x hxdeg
  have hpiece := hR L hLR (piece N T.Y) hmol (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P
    (fun κ h => by
      obtain ⟨κ0, h0, _, rfl⟩ := h; exact MoleProp.largeGap_erase N L γ η 0 _ (hAdm κ0 h0).1)
    (fun κ h => by
      obtain ⟨κ0, h0, _, rfl⟩ := h
      exact MoleProp.cellGapRestriction_erase N L 0 _ P _ (hAdm κ0 h0).2)
    (fun S hS => by rw [TwoExit.ladderCells_piece_eq] at hS; exact hP S (mem_filter.mp hS).1)
  refine (T.countAFree_le_of_piece_adm hloop hdeg hdegY hconn hopen (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [hγ.2]) hL1 hlog hδ.1 hδ.2 (by linarith) (by linarith) P hP Adm hAdm W hW hpiece).trans
    (mul_le_mul' le_rfl (iSup₂_mono fun g _ => iSup₂_le fun P' hP' => ?_))
  have hnn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
    have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N hcell.1), hcell.1⟩))
  exact le_iSup₂_of_le (f := fun P'' (_ : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P'' S) =>
    MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P'' g) P'') P' hnn le_rfl

end WaveTurbulence.MoleProp4
