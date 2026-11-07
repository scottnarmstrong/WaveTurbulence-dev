/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32DirectCount
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32IndirectCount
public import WaveTurbulence.Foundations.FinalCount.AppBR32Incidence
import Mathlib.Tactic

/-! # Actual combined count for the direct-entry and equal-sign branches -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_r32_rank_four_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
      M.IsMolecule → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → s.post.numComponents = 2 →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE (r.combinedRemoval s v0).post L γ δ w
            ((r.combinedRemoval s v0).conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,Ld,hC,hdirect⟩ := uniform_r32_direct_or_positive_countE_bound d hd γ hγ δ η hδ hη hηγ m
  obtain ⟨Ci,Li,hCi,hindirect⟩ := uniform_r32_indirect_countE_bound d hd γ hγ δ η hδ hη hηγ m
  refine ⟨max C Ci,max Ld Li,hC.trans_le (le_max_left _ _),?_⟩
  intro V D instV instF instD L hL hLp M r s v0 hM hsize hc hb hF w Adm hLG
  obtain ⟨S,j,hS,hlabels,hcross⟩ := appb_r32_split_side_exists M r s hc hb hF
  obtain ⟨which,ha,ho,hcomp,hocomp⟩ := appb_r32_choose_special_end s S hlabels
  have hbridge : appbIncidence M (s.specialAtom which) (s.edge ⟨0,by decide⟩).val.val = 1 := by
    have hh := (s.specialFrame which).incidence 0
    rw [(s.specialFrame_indices which).1] at hh
    exact hh
  have lift_bound (c : ℝ) (hc : c ≤ max C Ci)
      (hh : ∃ q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ),
        (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (c*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE (r.combinedRemoval s v0).post L γ δ w
            ((r.combinedRemoval s v0).conditionedPostAdmissibility Adm q) : ℝ≥0∞)) : ∃ q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ),
        (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal ((max C Ci)*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE (r.combinedRemoval s v0).post L γ δ w
            ((r.combinedRemoval s v0).conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
    obtain ⟨q,hq⟩ := hh
    refine ⟨q,hq.trans ?_⟩
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLp.le _)
  by_cases hopp : appbCutSign M S (r.edge j).val ≠ appbCutSign M S (s.edge ⟨0,by decide⟩).val.val
  · by_cases hi : appbIncidence M (s.specialAtom which) (r.edge j).val = 1
    · apply lift_bound C (le_max_left _ _)
      exact hdirect V D L ((le_max_left _ _).trans hL) hLp M r s v0 hM hsize S hS j hcross
        (fun _ => ⟨s.specialAtom which,ha,hi,hbridge⟩) w Adm hLG
    · have hz : appbIncidence M (s.specialAtom which) (r.edge j).val = 0 := by
        have hh := appb_r3_incidence_le_one r _ (s.special_atoms_mem which).1 j
        omega
      apply lift_bound Ci (le_max_right _ _)
      exact hindirect V D L ((le_max_right _ _).trans hL) hLp M r s v0 hM hsize S hS j which hcross
        ha hcomp ho hz hopp w Adm hLG
  · apply lift_bound C (le_max_left _ _)
    exact hdirect V D L ((le_max_left _ _).trans hL) hLp M r s v0 hM hsize S hS j hcross
      (fun h => (hopp h).elim) w Adm hLG

end WaveTurbulence.Mole.AppbAlgorithm
