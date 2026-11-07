/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33SharedCount
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33ConnectedGood
public import WaveTurbulence.Foundations.FinalCount.AppBGoodDeletionTransfer
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
import Mathlib.Tactic

/-! # Good deviation for the degree-three/two removal 3S3-5G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

/-- DH23 3S3-5G, with the first two shared-neighbour figures in the split case and the standing LG premise. -/
theorem uniform_s33_shared_split_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds) (r : AppbRealization M k.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → (¬r.post.SameComponent (r.vertex 3) (r.vertex 4)) →
      (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) →
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨C,hC,L₀,hL₀⟩ := uniform_s33_shared_split_countE_bound d hd γ hγ δ η hδ hη hηγ m
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual C (31/48) (min γ (1-γ)) 8 hC.le hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hconn hbridge h34 hsize w Adm scales hscale hgap
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp M k hk r hM hbridge h34 hsize w Adm hgap
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+(2 : ℕ) := by
    have hcase := appb_s33_remove_graph_effect M k (appb_s33_shared_mem k hk) r hconn hbridge
    rcases hcase with hcase | hcase
    · have hh := hcase.1
      have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by
        have ht : ∀ k ∈ appbS33SharedKinds,1 ∈ k.pattern.vertices := by decide
        exact ht k hk)⟩ hconn
      have hn : r.post.numComponents = 1 := hh.trans hm
      have ht : ∀ k ∈ appbS33SharedKinds,3 ∈ k.pattern.vertices ∧ 4 ∈ k.pattern.vertices ∧
          3 ∉ k.pattern.removed ∧ 4 ∉ k.pattern.removed := by decide
      exact False.elim (h34 (appb_connected_of_numComponents_eq_one r.post hn
        (r.vertex_mem_post 3 (ht k hk).1 (ht k hk).2.2.1)
        (r.vertex_mem_post 4 (ht k hk).2.1 (ht k hk).2.2.2)))
    · have hh := hcase.2.1
      omega
  have hcard : 4*r.removedAtoms.card ≤ 8 := by
    change 4*(k.pattern.removed.image r.vertex).card ≤ 8
    have hh := card_image_le (f := r.vertex) (s := k.pattern.removed)
    have hn : k.pattern.removed.card = 2 := by
      have ht : ∀ k ∈ appbS33SharedKinds,k.pattern.removed.card = 2 := by decide
      exact ht k hk
    omega
  apply appb_good_deletion_of_raw_and_rank r hM L γ δ C1 (31/48) (min γ (1-γ)) C
    w Adm q scales 2 8 hL1 hlog hδ hC1 hC.le hscale hcard hchi
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL)))
  have he : ((d : ℝ)-γ)*(2 : ℝ)-(31/48)*min γ (1-γ) =
      2*((d : ℝ)-γ)-31*min γ (1-γ)/48 := by ring
  simpa only [Nat.cast_ofNat,he] using hraw

end WaveTurbulence.Mole.AppbAlgorithm
