/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNorm
public import WaveTurbulence.Foundations.FinalCount.MoleProp.MoleculeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapLoops
import Mathlib.Tactic

/-! # The two-exit (Y2) bound with constants (DH23 ylem2, L1954)

DH23 Prop 10.1 (G6's `molecule_count_bound`) bounds the removed piece: `𝔄(N[Y]) ≤ 1` with constant `C₁/2`. With it,
for `C₁ ≥ 2 C⋆` and `L` large (depending on `δ, η`):

`𝔄(N) ≤ 110 |scaleSet L|² (log L)^{12} · sup_{P'} 𝔄(post)`,

the left side with large gaps of parameter `η`, the right side with `η/2`. This is the counting core of the first
statement of DH23 Lemma `ylem2` when the (Y) sequence ends in (Y2).
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

/-- **The two-exit removal bound.** -/
theorem twoExit_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D),
      (∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) → ∀ T : TwoExit N,
      (∀ v ∈ T.Y, N.deg v = 4) → (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      (∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) (lgAdm N L γ η P) P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            ⨆ P' ∈ T.scaleFamily L P,
              MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (lgAdm T.post L γ (η / 2) P') P' := by
  obtain ⟨Cstar, hCstar, h101⟩ := MoleProp.molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h101 (C1 / 2) (by linarith) δ hδ
  refine ⟨max R (max (Real.exp 1) ((11 : ℝ) ^ (2 / η))), fun L hL => ?_⟩
  intro V D _ _ _ N hcap T hdegY hconn hopen P hP
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (2 / η) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11 : 11 ≤ L ^ (η / 2) := by
    calc (11 : ℝ) = ((11 : ℝ) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ L ^ (η / 2) := Real.rpow_le_rpow (by positivity) hL11' (by positivity)
  -- loops make the count vanish
  by_cases hlo : ∃ z : D, N.atom z = N.atom (N.mate z)
  · obtain ⟨z, hz⟩ := hlo
    rw [MoleProp.countAFree_eq_zero_of_loop N hLp γ δ C1 η 0 _ (fun κ h => h.1) P z hz]
    exact bot_le
  have hloop : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z h => hlo ⟨z, h⟩
  have hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4 := fun a ha => by
    have h := hcap a ha
    have hsum := Mole.outdeg_add_indeg N a
    omega
  -- the piece is a molecule, bounded by Prop 10.1
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
  have hpiece := hR L hLR (piece N T.Y) hmol
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) (lgAdm (d := d) N L γ η P)) P
    (fun κ h => by obtain ⟨κ0, ⟨hLG, _⟩, _, rfl⟩ := h; exact MoleProp.largeGap_erase N L γ η 0 _ hLG)
    (fun κ h => by
      obtain ⟨κ0, ⟨_, hC⟩, _, rfl⟩ := h
      exact MoleProp.cellGapRestriction_erase N L 0 _ P _ hC)
    (fun S hS => by rw [TwoExit.ladderCells_piece_eq] at hS; exact hP S (mem_filter.mp hS).1)
  exact T.countAFree_le_of_piece hcap hloop hdeg hdegY hconn hopen (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [hγ.2]) hL1 hlog hL11 hδ.1 hδ.2 (by linarith) (by linarith) P hP hpiece

end WaveTurbulence.MoleProp4
