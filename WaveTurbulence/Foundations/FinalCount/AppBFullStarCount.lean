/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOrderedStarFrame
public import WaveTurbulence.Foundations.FinalCount.AppBStarChoices
import Mathlib.Tactic

/-! # Actual five-bond group counts from the source degree caps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_full_star_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P), M.IsMolecule →
    ∀ v1 ∈ r.removedAtoms, ∀ v2 ∈ r.removedAtoms,
    ∀ (e : Fin 5 ↪ Fin P.edges.length), Function.Surjective e →
    ∀ (t1 : AppbTripleFrame r v1) (t2 : AppbTripleFrame r v2),
      (∀ j,t1.index j = e (![0,1,2] j)) → (∀ j,t2.index j = e (![0,3,4] j)) →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin P.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_star_projection_bound (V := V) (D := D) d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro L hL hLp M P r hM v1 hv1 v2 hv2 e he t1 t2 h1 h2 w Adm
  obtain ⟨o⟩ := appb_overlap_order_exists
    (fun j => appbIncidenceSign M v1 (r.edge (t1.index j)).val)
    (fun j => appbIncidenceSign M v2 (r.edge (t2.index j)).val)
    (r.not_all_positive_frame_signs hM t1.index (r.removedAtoms_subset hv1))
    (r.not_all_negative_frame_signs hM t1.index (r.removedAtoms_subset hv1) t1.incidence)
    (r.not_all_positive_frame_signs hM t2.index (r.removedAtoms_subset hv2))
    (r.not_all_negative_frame_signs hM t2.index (r.removedAtoms_subset hv2) t2.incidence)
  let t := appbOrderedStarFrame e t1 t2 h1 h2 o
  have hva : (if o.swap then v2 else v1) ∈ r.removedAtoms := by split_ifs <;> assumption
  have hvb : (if o.swap then v1 else v2) ∈ r.removedAtoms := by split_ifs <;> assumption
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ L hL hLp M P r _ hva _ hvb t p w Adm
  have ht : Function.Surjective t.index := by
    let E := Equiv.ofBijective e ⟨e.injective,he⟩
    have hs := Finite.surjective_of_injective (E.symm.injective.comp t.index.injective)
    intro i
    obtain ⟨j,hj⟩ := hs (E.symm i)
    exact ⟨j,E.symm.injective hj⟩
  have hinj : Function.Injective (t.project (K := Fin d → ℤ)) := by
    intro u u' hh
    funext i
    obtain ⟨j,rfl⟩ := ht i
    exact congrFun hh j
  rw [card_image_of_injective _ hinj] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole
