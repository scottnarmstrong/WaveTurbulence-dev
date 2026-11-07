/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleProjection
public import WaveTurbulence.Foundations.FinalCount.AppBD336FirstTriple
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336TailRankFive
import Mathlib.Tactic

/-! # Actual nine-bond count in the four-circuit branch of 3D3-6G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d336_literal_rank_five_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33new.pattern),
      M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin AppbPatternKind.d33new.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*δ⁻¹*L^(5*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,Lp,hC,hLp0⟩ := uniform_tripleFrame_projection_bound d hd γ hγ
  obtain ⟨Lt,hLt⟩ := uniform_d336_tail_rank_five_fiber_bound d hd δ γ hδ hγ
  refine ⟨C,max Lp (max Lt 1),hC,?_⟩
  intro V D instV instF instD L hL hLp M r hM w Adm
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let Q := r.localChoices p hLp γ δ w Adm
  let f := (appbD336FirstTriple r).project (K := Fin d → ℤ)
  have hproj := hLp0 V D L ((le_max_left _ _).trans hL) hLp δ hδ M _ r hM (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33new.pattern.removed by decide))
    (appbD336FirstTriple r) p w Adm
  have hfiber (z : Fin 3 → (Fin d → ℤ)) : ((Q.filter (fun q => f q = z)).card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
    have hh := hLt V D L ((le_max_left Lt _).trans ((le_max_right Lp _).trans hL)) hLp M r hM p w Adm
      (Q.filter (fun q => f q = z)) (filter_subset _ _) z (fun q hq => (mem_filter.mp hq).2)
    exact hh
  have hcount : (Q.card : ℝ) ≤ ((Q.image f).card : ℝ)*L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
    have hh := card_eq_sum_card_image f Q
    calc
      _ = ∑ z ∈ Q.image f,((Q.filter (fun q => f q = z)).card : ℝ) := by exact_mod_cast hh
      _ ≤ ∑ _z ∈ Q.image f,L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := sum_le_sum (fun z _ => hfiber z)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hraw : (Q.card : ℝ) ≤ C*δ⁻¹*L^(5*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
    calc
      _ ≤ ((Q.image f).card : ℝ)*L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := hcount
      _ ≤ (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) :=
        mul_le_mul_of_nonneg_right hproj (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hLp]; congr 1; congr 1; ring
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hraw' : (Q.card : ℝ≥0∞) ≤ ENNReal.ofReal (C*δ⁻¹*L^(5*((d : ℝ)-γ)-3*min γ (1-γ)/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hraw
  exact hcast.trans (mul_le_mul_left hraw' _)

end WaveTurbulence.Mole.AppbAlgorithm
