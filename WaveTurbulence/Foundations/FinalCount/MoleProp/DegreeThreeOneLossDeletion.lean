/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FixedThirdPair
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeBoundaryPatterns
public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarLabels
import Mathlib.Tactic

/-! # DH23 Proposition 10.1: the three-valent one-circuit-loss branch

Two newly bounded components at a degree-three atom force an actual
singleton crossing cut. Its label is fixed within each old parameter
fiber, so the remaining pair supplies the large-gap saving.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 Proposition 10.1 operation(a), degree three and one circuit loss.
A structural singleton cut supplies the fixed label internally. The old
charges remain arbitrary, and the post problem is the actual inherited
admissibility problem with its genuine parameter supremum. -/
theorem degree_three_one_loss_deletion_bound (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms, M.deg v = 3 →
    (newComponents M {v}).card = 2 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℕ∞) *
          countEFree (eraseAtoms M {v}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := star_three_fixed_incident_count_bound
    d hdim γ hγ η hη hηmax
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V' D' _ _ _ M _hM v hv hdeg hcomponents Adm hAdm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  obtain ⟨T,hT,hTcard⟩ := exists_single_boundary_of_degree_three_card_two M hdeg hcomponents
  obtain ⟨x,hx,hboundary⟩ := exists_incident_dart_of_single_boundary M hT hTcard
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hL0 γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let S := hf.toFinset
  have hS (κ) (hκ : κ ∈ S) : M.IsDecoration L (0 : Mom d) c κ ∧
      M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ LargeGap M L γ η (0 : Mom d) κ := by
    have ha := hf.mem_toFinset.mp hκ
    exact ⟨ha.1,ha.2.1,hAdm κ ha.2.2⟩
  have hsBound : ((S.image (starLabels M v)).card : ℝ) ≤ C*δ⁻¹*L^((d : ℝ)-γ-η) := by
    by_cases hne : S.Nonempty
    · obtain ⟨κ0,hκ0⟩ := hne
      apply hB L hLR δ hδ M v hv hdeg x hx c β k0 (κ0 x) S
      intro κ hκ
      obtain ⟨hd,hr,hg⟩ := hS κ hκ
      have hfixed : κ x = κ0 x := incident_label_unique_of_single_boundary M hL0.ne'
        hd (hS κ0 hκ0).1 hboundary
      exact ⟨hd,hr,hg,hfixed⟩
    · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hne
      rw [he,image_empty,card_empty,Nat.cast_zero]
      exact mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hL0.le _)
  have hdBound := card_deletedLabels_image_le_starLabels_image M v S
    (fun κ hκ => (hS κ hκ).1.1)
  have hQeq : (deletedLabels M {v} '' A).ncard = (S.image (deletedLabels M {v})).card := by
    have he : deletedLabels M {v} '' A = (S.image (deletedLabels M {v}) : Set _) := by
      rw [Finset.coe_image,hf.coe_toFinset]
    rw [he,Set.ncard_coe_finset]
  have hQreal : ((deletedLabels M {v} '' A).ncard : ℝ) ≤ C*δ⁻¹*L^((d : ℝ)-γ-η) := by
    rw [hQeq]
    have hdelR : ((S.image (deletedLabels M {v})).card : ℝ) ≤ (S.image (starLabels M v)).card := by
      exact_mod_cast hdBound
    exact hdelR.trans hsBound
  have hQnat : (deletedLabels M {v} '' A).ncard ≤ ⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ := by
    exact_mod_cast hQreal.trans (Nat.le_ceil _)
  have hQ : ((deletedLabels M {v} '' A).ncard : ℕ∞) ≤ (⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℕ∞) := by
    exact_mod_cast hQnat
  exact (encard_le_deletedImage_mul_post M {v} hL0 γ δ (0 : Mom d) Adm c β k0 hk0).trans
    (mul_le_mul_of_nonneg_right hQ bot_le)

end WaveTurbulence.MoleProp
