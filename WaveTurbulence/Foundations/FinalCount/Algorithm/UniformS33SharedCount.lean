/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SharedTopology
public import WaveTurbulence.Foundations.FinalCount.AppBS33SharedReconstruction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCommonCutCount
public import WaveTurbulence.Foundations.FinalCount.AppBInsideEndpointSign
public import WaveTurbulence.Foundations.FinalCount.AppBFrameProjectionReindex
import Mathlib.Tactic

/-! # Actual good count for the split common-neighbour 3S3New groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_s33_shared_split_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds)
      (r : AppbRealization M k.pattern), M.IsMolecule →
      (∀ e : D,¬Degen.IsBridge M e) → (¬r.post.SameComponent (r.vertex 3) (r.vertex 4)) →
      (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,hC,L₀,hL₀⟩ := uniform_triple_common_cut_countE_of_projection_injective
    d hd γ hγ δ η hδ hη hηγ m
  refine ⟨C,hC,L₀,?_⟩
  intro V D instV instF instD L hL hLp M k hk r hM hbridge h34 hsize w Adm hLG
  have hside := appb_s33_shared_side_of_not_connected M k hk r hbridge h34
  let cut := appbS33SharedCutPair k hk r hside
  let t := (appbS33SharedFrame k hk r).reindex (Equiv.swap 1 2)
  let e := appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk))
  have ht : ∀ k ∈ appbS33SharedKinds,1 ∈ k.pattern.removed ∧ 3 ∈ k.pattern.vertices ∧ 2 ∈ k.pattern.vertices := by decide
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (ht k hk).1
  have hcutsize : ((Degen.residualComponent M r.removedAtoms (r.vertex 3)).card : ℝ) ≤ (1+Real.log L)^m := by
    have hh : ((Degen.residualComponent M r.removedAtoms (r.vertex 3)).card : ℝ) ≤ M.atoms.card := by
      exact_mod_cast Finset.card_le_card cut.subset_atoms
    exact hh.trans hsize
  have hsign (j : Fin 2) :
      appbCutSign M (Degen.residualComponent M r.removedAtoms (r.vertex 3)) (r.edge (e (![1,3] j))).val =
        appbIncidenceSign M (r.vertex 3) (r.edge (e (![1,3] j))).val := by
    have he : M.ends (r.edge (e (![1,3] j))).val = s(r.vertex (![1,2] j),r.vertex 3) := by
      rw [r.endpoints]
      simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      all_goals fin_cases j <;> rfl
    have ha : r.vertex (![1,2] j) ∉ Degen.residualComponent M r.removedAtoms (r.vertex 3) := by
      have hmem : (![1,2] j : ℕ) ∈ k.pattern.vertices := by fin_cases j; exact mem_union_left _ (ht k hk).1; exact (ht k hk).2.2
      rw [hside _ hmem]
      fin_cases j <;> decide
    have hb := (hside 3 (ht k hk).2.1).mpr rfl
    exact appb_cutSign_eq_inside_second M _ _ _ _ he ha hb
  have hinc (j : Fin 2) : appbIncidence M (r.vertex 3) (r.edge (e (![1,3] j))).val = 1 := by
    rw [r.edge_incidence _ 3 (ht k hk).2.1]
    simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals fin_cases j <;> norm_num [e,appbFiveEmbedding,AppbPatternKind.pattern,finCongr]
  apply hL₀ V D L hL hLp M _ r hM (r.vertex 1) hv t _ cut rfl hcutsize
    (r.vertex 3) (r.vertex_mem 3 (ht k hk).2.1) (hinc 0) (hinc 1) (hsign 0) (hsign 1) w Adm
  · intro p
    exact (appbS33SharedFrame k hk r).reindex_project_injOn (Equiv.swap 1 2) _
      (appb_s33_shared_projection_injective k hk r hside p hLp γ δ w Adm)
  · exact hLG

end WaveTurbulence.Mole.AppbAlgorithm
