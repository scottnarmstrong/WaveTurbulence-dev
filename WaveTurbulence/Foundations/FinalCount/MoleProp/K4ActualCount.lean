/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFinal
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4SourceEncoding
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
import Mathlib.Tactic

/-! # The actual arbitrary-charge K4 counting problem

DH23 A.3(5) is applied after producing the actual graph enumeration and
integer parameters from each old decoration fiber, not as hypotheses.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem K4_countEFree_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ x, M.atom x ≠ M.atom (M.mate x)) →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
      M.atoms.Nonempty → (∀ a ∈ M.atoms, 3 ≤ M.deg a) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → M.circuitRank = 3 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*min γ (1-γ))⌉₊ : ℕ∞) := by
  classical
  obtain ⟨C,hC,hB⟩ := k4_canonical_count_bound d hd γ hγ
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨R,hR⟩ := hB δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL V D _ _ _ M hM hloop hsimple hne hmin hconn hrank Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _hk0 => ?_
  obtain ⟨e,b,a,b0,c0,_he,henc⟩ :=
    exists_K4_source_fiber_encoding_of_simple_rank_three M hM hloop hsimple hne hmin hconn hrank hLp.ne' γ δ c β k0 Adm
  obtain ⟨hf,hcard⟩ := hR L hLR (fun r => k0 (b r).val) a b0 c0 ![β (e 0).val,β (e 1).val,β (e 2).val]
  have hnat : (k4CanonicalSet L (fun r => k0 (b r).val) a b0 c0
      ![β (e 0).val,β (e 1).val,β (e 2).val] (δ⁻¹*L^(-2*γ))).ncard ≤
      ⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*min γ (1-γ))⌉₊ := by
    exact_mod_cast hcard.trans (Nat.le_ceil _)
  apply henc.trans
  rw [← hf.cast_ncard_eq]
  exact_mod_cast hnat

end WaveTurbulence.MoleProp
