/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33Count
public import WaveTurbulence.Foundations.FinalCount.AppBS33GraphEffects
public import WaveTurbulence.Foundations.FinalCount.AppBGoodDeletionTransfer
import Mathlib.Tactic

/-! # Good deviation for the four double-bond scenarios of 3S3-5G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

/-- DH23 3S3-5G, scenarios 3--6 of Figure 3S3New. Their actual graph
remains connected, hence the five-bond count loses exactly three circuits. -/
theorem uniform_s33_double_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (k : AppbPatternKind)
      (hk : k ∈ ([AppbPatternKind.s33new3,.s33new4,.s33new5,.s33new6] : List _))
      (r : AppbRealization M k.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := uniform_s33_five_bond_countE_bound d hd γ hγ δ hδ
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual 1 (3/4) (min γ (1-γ)) 8 (by norm_num) hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hconn hbridge w Adm scales hscale
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  have hkall : k ∈ appbS33Kinds := by
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp M k hkall r hM w Adm
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+(3 : ℕ) := by
    have hh := (appb_s33new_double_graph_effect M k hk r hconn hbridge).2.1
    omega
  have hcard : 4*r.removedAtoms.card ≤ 8 := by
    have hn : k.pattern.removed.card = 2 := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    change 4*(k.pattern.removed.image r.vertex).card ≤ 8
    have hh := card_image_le (f := r.vertex) (s := k.pattern.removed)
    omega
  apply appb_good_deletion_of_raw_and_rank r hM L γ δ C1 (3/4) (min γ (1-γ)) 1
    w Adm q scales 3 8 hL1 hlog hδ hC1 (by norm_num) hscale hcard hchi
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL)))
  have he : ((d : ℝ)-γ)*(3 : ℝ)-(3/4)*min γ (1-γ) =
      3*((d : ℝ)-γ)-3*min γ (1-γ)/4 := by ring
  simpa only [Nat.cast_ofNat,one_mul,he] using hraw

end WaveTurbulence.Mole.AppbAlgorithm
