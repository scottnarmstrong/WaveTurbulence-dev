/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCutGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleSmallGap
public import WaveTurbulence.Foundations.FinalCount.AppBD33Reconstruction
import Mathlib.Tactic

/-! # Carrier-uniform failed-label double-pair count -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v
/-- The conserved boundary difference is fixed on each actual old source
fiber. Thus the source disjunction is resolved before counting; no global
choice of a branch on all admissible decorations is assumed. -/
theorem uniform_d33_bad_labels_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀,
    ∀ hLp : 0 < L, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      M.IsMolecule → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      ∃ q : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨Cbig,hCbig,hbig⟩ := uniform_triple_cut_good_projection_bound d hd γ hγ 1 le_rfl
  obtain ⟨Csmall,hCsmall,hsmall⟩ := uniform_tripleFrame_small_gap_projection_bound d hd γ hγ
  refine ⟨max Cbig Csmall,hCbig.trans_le (le_max_left _ _),?_⟩
  intro δ hδ
  obtain ⟨Lb,hLb⟩ := hbig δ hδ
  obtain ⟨Ls,hLs⟩ := hsmall δ hδ
  refine ⟨max Lb (max Ls 1),?_⟩
  intro V D instV instF instD L hL hLp M r hM hOpp w Adm hbad
  have hL1 : 1 ≤ L := (le_max_right Ls 1).trans ((le_max_right Lb _).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let cut := appbD33CutPair r
  have hco := appb_d33_cut_signs_opposite M r hOpp
  let R := (((appbCutSign M r.removedAtoms (r.edge cut.first).val)⁻¹ : ℤˣ) : ℤ) •
    (∑ a ∈ r.removedAtoms,p.momentum a)
  have hR (κ : D → (Fin d → ℤ)) (hk : κ ∈ p.decorations L γ δ w Adm) :
      Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val = R :=
    cut.momentum_difference hco L w p.momentum κ hk.1
  have hbound : (((r.localChoices p hLp γ δ w Adm).image (appbD33Frame r).project).card : ℝ) ≤
      max Cbig Csmall*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    by_cases hlarge : L^(-γ) ≤ ‖R‖
    · have hc : r.removedAtoms.card ≤ 2 := by
        change (AppbPatternKind.d33.pattern.removed.image r.vertex).card ≤ 2
        exact card_image_le.trans (by decide)
      have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ r hM (r.vertex 1)
        (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide)) (appbD33Frame r)
        r.removedAtoms cut hco hc 2 rfl p w Adm (by
          intro κ hk
          change (1 : ℝ)⁻¹*L^(-γ) ≤ ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
            Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖
          simpa only [inv_one,one_mul,hR κ hk] using hlarge)
      have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
      have hex : 2*((d : ℝ)-γ)-2*min γ (1-γ)/3 ≤
          2*((d : ℝ)-γ)-31*min γ (1-γ)/48 := by linarith only [hg0]
      exact hb.trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hL1 hex)
        (Real.rpow_nonneg hLp.le _) ((hCbig.trans_le (le_max_left _ _)).le))
    · have hint (κ : D → (Fin d → ℤ)) (hk : κ ∈ p.decorations L γ δ w Adm) :
          AppbOppositeFrom M (r.vertex 1) (r.vertex 1) (r.edge ⟨0,by decide⟩).val (r.edge ⟨1,by decide⟩).val ∧
          ‖Molecule.kvec L w κ (r.edge ⟨0,by decide⟩).val-
            Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val‖ < L^(-γ+2*min γ (1-γ)/3) := by
        have hb : ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
            Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖ ≤ L^(-γ) := by
          rw [hR κ hk]
          exact (lt_of_not_ge hlarge).le
        have hn := hbad κ hk.2.2
        unfold AppbD33LabelConditions at hn
        have hi := not_imp.mp (fun hi => hn ⟨hb,hi⟩)
        exact ⟨hi.1,lt_of_not_ge hi.2⟩
      by_cases hnon : (p.decorations L γ δ w Adm).Nonempty
      · obtain ⟨κ0,hκ0⟩ := hnon
        have h01 := (appb_incidence_sign_opposite M (r.vertex 1) _ _).mpr (hint κ0 hκ0).1
        have hs := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ r
          (r.vertex 1) (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide))
          (appbD33Frame r) h01 p w Adm (fun κ hk => (hint κ hk).2.le)
        exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hLp.le _))
      · have he : r.localChoices p hLp γ δ w Adm = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨κ,hκ,hh⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
          exact hnon ⟨κ,hκ⟩
        rw [he,Finset.image_empty,Finset.card_empty,Nat.cast_zero]
        positivity
  rw [card_image_of_injOn (appb_d33_projection_injective r p hLp γ δ w Adm)] at hbound
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (max Cbig Csmall*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hbound
  exact hcast.trans (mul_le_mul_left hN _)

end WaveTurbulence.Mole.AppbAlgorithm
