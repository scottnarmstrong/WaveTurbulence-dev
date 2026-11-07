/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33SharedGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33DoubleGood
import Mathlib.Tactic

/-! # DH23 3S3-5G: all six transcribed figure configurations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
open scoped ENNReal
universe u v

theorem uniform_s33_new_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (k : AppbPatternKind)
      (hk : k ∈ ([AppbPatternKind.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _))
      (r : AppbRealization M k.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) → (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨Ls,hLs⟩ := uniform_s33_shared_good_bound d hd γ hγ η hη hηγ m δ hδ
  obtain ⟨Ld,hLd⟩ := uniform_s33_double_good_bound d hd γ hγ δ hδ
  refine ⟨max Ls Ld,?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hconn hbridge hsize w Adm scales hscale hLG
  by_cases hs : k ∈ appbS33SharedKinds
  · exact hLs V D C1 hC1 L ((le_max_left _ _).trans hL) M k hs r hM hconn hbridge hsize w Adm scales hscale hLG
  · have hdbl : k ∈ ([AppbPatternKind.s33new3,.s33new4,.s33new5,.s33new6] : List _) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      have hh : k ≠ .s33new1 ∧ k ≠ .s33new2 := by
        simpa only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false,not_or] using hs
      rcases hk with h | h | h | h | h | h
      · exact False.elim (hh.1 h)
      · exact False.elim (hh.2 h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    exact hLd V D C1 hC1 L ((le_max_right _ _).trans hL) M k hdbl r hM hconn hbridge w Adm scales hscale

end WaveTurbulence.Mole.AppbAlgorithm
