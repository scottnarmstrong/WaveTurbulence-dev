/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33TopologySigns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleCount
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
public import WaveTurbulence.Foundations.FinalCount.AppBFrameProjectionReindex
import Mathlib.Tactic

/-! # Good count when the split single-pair boundary direction test fails -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_s33_mismatch_countE_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern),
      AppbS33SplitTopology M r → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
      (¬(AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val ∧
        AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val)) →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_cut_triple_card_bound_of_projection_injective
    d hd γ hγ δ η hδ hη hηγ m
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r htop hsize hmismatch w Adm hLG
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33.pattern.removed by decide)
  have hcase (S : Finset V) (cut : AppbCutPair r S) (π : Equiv.Perm (Fin 3))
      (hfirst : cut.first = ((appbS33Frame r).reindex π).index 2)
      (hsame : appbCutSign M S (r.edge cut.first).val = appbCutSign M S (r.edge cut.second).val) :
      ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤ L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    have hc0 : (S.card : ℝ) ≤ M.atoms.card := by exact_mod_cast Finset.card_le_card cut.subset_atoms
    apply hL₀ V D L hL hLp M _ r S cut hsame (hc0.trans hsize) (r.vertex 1) hv
      ((appbS33Frame r).reindex π) hfirst p w Adm
      ((appbS33Frame r).reindex_project_injOn π _ (appb_s33_topology_projection_injective r htop p hLp γ δ w Adm))
    intro hsign κ hκ
    exact appb_tripleFrame_pair_gap r ((appbS33Frame r).reindex π) hv L w κ _ hκ.1.1
      (hLG κ hκ.2.2) 0 1 (by decide) hsign
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤ L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    by_cases ho1 : AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val
    · have ho2 : ¬AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val :=
        fun h => hmismatch ⟨ho1,h⟩
      have hs : appbCutSign M (appbS33TopologyOtherSide r) (r.edge ⟨2,by decide⟩).val =
          appbCutSign M (appbS33TopologyOtherSide r) (r.edge ⟨4,by decide⟩).val :=
        not_ne_iff.mp (fun h => ho2 ((appb_s33_topology_second_signs_iff M r htop).mp h))
      exact hcase _ (appbS33TopologyOtherCutPair r htop) (Equiv.refl _) rfl hs
    · have hs : appbCutSign M (appbS33Side r) (r.edge ⟨1,by decide⟩).val =
          appbCutSign M (appbS33Side r) (r.edge ⟨3,by decide⟩).val :=
        not_ne_iff.mp (fun h => ho1 ((appb_s33_topology_first_signs_iff M r htop).mp h))
      exact hcase _ (appbS33TopologyCutPair r htop) (Equiv.swap 1 2) rfl hs
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
