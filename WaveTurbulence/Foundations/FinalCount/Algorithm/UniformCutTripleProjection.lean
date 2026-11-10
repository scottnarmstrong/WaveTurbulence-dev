/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutSameSign
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFixedThirdFine
import Mathlib.Tactic

/-! # Same-sign cut counting for a triple projection, without full reconstruction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_cut_triple_projection_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P)
      (S : Finset V) (cut : AppbCutPair r S),
      appbCutSign M S (r.edge cut.first).val = appbCutSign M S (r.edge cut.second).val →
      (S.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v, cut.first = t.index 2 →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
        ∀ κ,κ ∈ p.decorations L γ δ w Adm →
        L^(-γ+η) ≤ ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
          Molecule.kvec L w κ (r.edge (t.index 1)).val‖) →
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤
        L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨Lb,hLb⟩ := uniform_cut_same_sign_projection_bound d hd γ hγ δ hδ m
  obtain ⟨Li,hLi⟩ := uniform_triple_fixed_third_fine_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max Lb (max Li 1),?_⟩
  intro V D instV instF instD L hL hLp M P r S cut hsame hcard v hv t hthird p w Adm hgap
  let Q := r.localChoices p hLp γ δ w Adm
  let f := fun q : Fin P.edges.length → (Fin d → ℤ) => (q cut.first,q cut.second)
  let T := fun z => Q.filter (fun q => f q = z)
  let R := fun z => (T z).image t.project
  have hL1 : 1 ≤ L := (le_max_right Li 1).trans ((le_max_right Lb _).trans hL)
  have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M P r S cut hsame hcard p w Adm
  have hfiber (z : (Fin d → ℤ) × (Fin d → ℤ)) : ((R z).card : ℝ) ≤ L^((d : ℝ)-γ) := by
    have hT : T z ⊆ Q := filter_subset _ _
    have hz : ∀ q ∈ T z,q (t.index 2) = z.1 := by
      intro q hq
      rw [← hthird]
      exact congrArg Prod.fst (mem_filter.mp hq).2
    have hh := hLi V D L ((le_max_left Li _).trans ((le_max_right Lb _).trans hL)) hLp M P r v hv t p w Adm z.1 (T z) hT hz hgap
    have hzR : ∀ u ∈ R z,u (2 : Fin 3) = z.1 := by
      intro u hu
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hu
      exact hz q hq
    have hi : Set.InjOn (fun u : Fin 3 → (Fin d → ℤ) => (u 0,u 1)) (R z : Set _) := by
      intro u hu u' hu' he
      funext j
      fin_cases j
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
      · exact (hzR u hu).trans (hzR u' hu').symm
    have he : (T z).image (fun q => (q (t.index 0),q (t.index 1))) =
        (R z).image (fun u => (u 0,u 1)) := by
      dsimp only [R]
      rw [Finset.image_image]
      rfl
    rw [he,Finset.card_image_of_injOn hi] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη]))
  have hcover : Q.image t.project ⊆ (Q.image f).biUnion R := by
    intro u hu
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hu
    exact mem_biUnion.mpr ⟨f q,mem_image_of_mem _ hq,mem_image.mpr ⟨q,mem_filter.mpr ⟨hq,rfl⟩,rfl⟩⟩
  have hc : (Q.image t.project).card ≤ ∑ z ∈ Q.image f,(R z).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcount : ((Q.image t.project).card : ℝ) ≤ (Q.image f).card*L^((d : ℝ)-γ) := by
    calc
      _ ≤ ∑ z ∈ Q.image f,((R z).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _z ∈ Q.image f,L^((d : ℝ)-γ) := sum_le_sum (fun z _ => hfiber z)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  calc
    _ ≤ (Q.image f).card*L^((d : ℝ)-γ) := hcount
    _ ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48)*L^((d : ℝ)-γ) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring

end WaveTurbulence.Mole.AppbAlgorithm
