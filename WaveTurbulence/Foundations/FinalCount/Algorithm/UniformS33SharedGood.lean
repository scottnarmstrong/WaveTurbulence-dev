/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33SharedSplitGood
import Mathlib.Tactic

/-! # Full good deviation for the first two 3S3New configurations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
open scoped ENNReal
universe u v

/-- DH23 3S3-5G, Figure 3S3New scenarios 1--2, covering both possible
residual component counts. The split case uses LG at the common neighbour. -/
theorem uniform_s33_shared_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds) (r : AppbRealization M k.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) → (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨Ls,hLs⟩ := uniform_s33_shared_split_good_bound d hd γ hγ η hη hηγ m δ hδ
  obtain ⟨Lc,hLc⟩ := uniform_s33_connected_post_good_bound d hd γ hγ δ hδ
  refine ⟨max Ls Lc,?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hconn hbridge hsize w Adm scales hscale hLG
  by_cases h34 : r.post.SameComponent (r.vertex 3) (r.vertex 4)
  · exact hLc V D C1 hC1 L ((le_max_right _ _).trans hL) M k (appb_s33_shared_mem k hk) r hM hconn
      (appb_s33_shared_connected_of_common M k hk r hconn hbridge h34) w Adm scales hscale
  · exact hLs V D C1 hC1 L ((le_max_left _ _).trans hL) M k hk r hM hconn hbridge h34 hsize w Adm scales hscale hLG

end WaveTurbulence.Mole.AppbAlgorithm
