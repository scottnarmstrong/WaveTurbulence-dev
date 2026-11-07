/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarTriple
public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarOrdering
import Mathlib.Tactic

/-! # The unconditional three-label deletion bound of DH23 Proposition 10.1

All local counting and post-parameter transport are proved for actual source
objects; no fiber cardinality or normalized operation estimate is a premise.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 10.1 operation(a), three free labels, before circuit normalization.
The actual orientation cap supplies the local ordering and the fixed-deleted
fiber theorem supplies the legitimate post-removal parameter supremum. -/
theorem degree_three_deletion_bound (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms, M.deg v = 3 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {v}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := star_three_count_bound d hdim γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V' D' _ _ _ M hM v hv hd Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  obtain ⟨e,b,h0,h1,h2⟩ := exists_alternating_star_order M hM hv hd
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hL0 γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let S := hf.toFinset
  have hS (κ) (hκ : κ ∈ S) : M.IsDecoration L (0 : Mom d) c κ ∧
      M.IsRestricted L γ δ (0 : Mom d) β k0 κ := by
    have ha := hf.mem_toFinset.mp hκ
    exact ⟨ha.1,ha.2.1⟩
  have hsBound := hB L hLR hL0 δ hδ M v hv e b h0 h1 h2 c β k0 S hS
  have hdBound := card_deletedLabels_image_le_starLabels_image M v S
    (fun κ hκ => (hS κ hκ).1.1)
  have hQeq : (deletedLabels M {v} '' A).ncard = (S.image (deletedLabels M {v})).card := by
    have he : deletedLabels M {v} '' A = (S.image (deletedLabels M {v}) : Set _) := by
      rw [Finset.coe_image,hf.coe_toFinset]
    rw [he,Set.ncard_coe_finset]
  have hQreal : ((deletedLabels M {v} '' A).ncard : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
    rw [hQeq]
    have hdelR : ((S.image (deletedLabels M {v})).card : ℝ) ≤ (S.image (starLabels M v)).card := by
      exact_mod_cast hdBound
    exact hdelR.trans hsBound
  have hQnat : (deletedLabels M {v} '' A).ncard ≤ ⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))⌉₊ := by
    exact_mod_cast hQreal.trans (Nat.le_ceil _)
  have hQ : ((deletedLabels M {v} '' A).ncard : ℕ∞) ≤ (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))⌉₊ : ℕ∞) := by
    exact_mod_cast hQnat
  exact (encard_le_deletedImage_mul_post M {v} hL0 γ δ (0 : Mom d) Adm c β k0 hk0).trans
    (mul_le_mul_of_nonneg_right hQ bot_le)

end WaveTurbulence.MoleProp
