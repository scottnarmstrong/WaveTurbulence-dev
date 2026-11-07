/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33CutSigns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCutLog
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleSmallGap02
import Mathlib.Tactic

/-! # Good raw counting for the failed-label-test branch of split 3S3 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- The standing molecule-size bound controls both cut energy windows.
Both boundary differences are fixed by source momentum on each fiber. -/
theorem uniform_s33_bad_labels_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀,
    ∀ hLp : 0 < L, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern),
      M.IsMolecule → AppbS33SplitGeometry M r → (M.atoms.card : ℝ) ≤ 2*(1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → ¬AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      ∃ q : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨Cb,hCb,hbig⟩ := uniform_triple_cut_log_good_projection_bound d hd γ hγ 2 (by norm_num) m
  obtain ⟨Cs,hCs,hsmall⟩ := uniform_tripleFrame_small_gap_02_projection_bound d hd γ hγ
  refine ⟨max Cb Cs,hCb.trans_le (le_max_left _ _),?_⟩
  intro δ hδ
  obtain ⟨Lb,hLb⟩ := hbig δ hδ
  obtain ⟨Ls,hLs⟩ := hsmall δ hδ
  refine ⟨max Lb (max Ls 1),?_⟩
  intro V D instV instF instD L hL hLp M r hM hgeom hsize w Adm hbad
  have hL1 : 1 ≤ L := (le_max_right Ls 1).trans ((le_max_right Lb _).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let cut1 := appbS33CutPair r hgeom
  let cut2 := appbS33OtherCutPair r hgeom
  have ho1 := appb_s33_cut_signs_opposite M r hgeom
  have ho2 := appb_s33_other_cut_signs_opposite M r hgeom
  let R1 := (((appbCutSign M (appbS33Side r) (r.edge cut1.first).val)⁻¹ : ℤˣ) : ℤ) •
    (∑ a ∈ appbS33Side r,p.momentum a)
  let R2 := (((appbCutSign M (appbS33OtherSide r) (r.edge cut2.first).val)⁻¹ : ℤˣ) : ℤ) •
    (∑ a ∈ appbS33OtherSide r,p.momentum a)
  have hR1 (κ : D → (Fin d → ℤ)) (hk : κ ∈ p.decorations L γ δ w Adm) :
      Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val = R1 :=
    cut1.momentum_difference ho1 L w p.momentum κ hk.1
  have hR2 (κ : D → (Fin d → ℤ)) (hk : κ ∈ p.decorations L γ δ w Adm) :
      Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val = R2 :=
    cut2.momentum_difference ho2 L w p.momentum κ hk.1
  have hcase (S : Finset V) (cut : AppbCutPair r S)
      (ho : appbCutSign M S (r.edge cut.first).val ≠ appbCutSign M S (r.edge cut.second).val)
      (j0 : Fin 3) (hj : cut.first = (appbS33Frame r).index j0)
      (hg : ∀ κ,κ ∈ p.decorations L γ δ w Adm → (2 : ℝ)⁻¹*L^(-γ) ≤
        ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖) :
      (((r.localChoices p hLp γ δ w Adm).image (appbS33Frame r).project).card : ℝ) ≤
        max Cb Cs*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    have hc0 : (S.card : ℝ) ≤ M.atoms.card := by exact_mod_cast Finset.card_le_card cut.subset_atoms
    have hc : (S.card : ℝ) ≤ 2*(1+Real.log L)^m := hc0.trans hsize
    have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ r hM (r.vertex 1)
      (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33.pattern.removed by decide)) (appbS33Frame r)
      S cut ho hc j0 hj p w Adm hg
    have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
    have hex : 2*((d : ℝ)-γ)-2*min γ (1-γ)/3 ≤
        2*((d : ℝ)-γ)-31*min γ (1-γ)/48 := by linarith only [hg0]
    exact hb.trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hL1 hex)
      (Real.rpow_nonneg hLp.le _) ((hCb.trans_le (le_max_left _ _)).le))
  have hbound : (((r.localChoices p hLp γ δ w Adm).image (appbS33Frame r).project).card : ℝ) ≤
      max Cb Cs*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    by_cases hg1 : (2 : ℝ)⁻¹*L^(-γ) ≤ ‖R1‖
    · apply hcase _ cut1 ho1 1 rfl
      intro κ hk
      change (2 : ℝ)⁻¹*L^(-γ) ≤ ‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖
      rw [hR1 κ hk]
      exact hg1
    by_cases hg2 : (2 : ℝ)⁻¹*L^(-γ) ≤ ‖R2‖
    · apply hcase _ cut2 ho2 2 rfl
      intro κ hk
      change (2 : ℝ)⁻¹*L^(-γ) ≤ ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val‖
      rw [hR2 κ hk]
      exact hg2
    have hint (κ : D → (Fin d → ℤ)) (hk : κ ∈ p.decorations L γ δ w Adm) :
        AppbOppositeFrom M (r.vertex 1) (r.vertex 1) (r.edge ⟨0,by decide⟩).val (r.edge ⟨2,by decide⟩).val ∧
        ‖Molecule.kvec L w κ (r.edge ⟨0,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖ < L^(-γ+2*min γ (1-γ)/3) := by
      have hb : ‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖+
          ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val‖ ≤ L^(-γ) := by
        rw [hR1 κ hk,hR2 κ hk]
        have hh1 := lt_of_not_ge hg1
        have hh2 := lt_of_not_ge hg2
        norm_num at hh1 hh2
        linarith only [hh1,hh2]
      have hn := hbad κ hk.2.2
      unfold AppbS33LabelConditions at hn
      have hi := not_imp.mp (fun hi => hn ⟨hb,hi⟩)
      exact ⟨hi.1,lt_of_not_ge hi.2⟩
    by_cases hnon : (p.decorations L γ δ w Adm).Nonempty
    · obtain ⟨κ0,hκ0⟩ := hnon
      have h02 := (appb_incidence_sign_opposite M (r.vertex 1) _ _).mpr (hint κ0 hκ0).1
      have hs := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ r
        (r.vertex 1) (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33.pattern.removed by decide))
        (appbS33Frame r) h02 p w Adm (fun κ hk => (hint κ hk).2.le)
      exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hLp.le _))
    · have he : r.localChoices p hLp γ δ w Adm = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨κ,hκ,hh⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
        exact hnon ⟨κ,hκ⟩
      rw [he,Finset.image_empty,Finset.card_empty,Nat.cast_zero]
      positivity
  rw [card_image_of_injOn (appb_s33_split_projection_injective r hgeom p hLp γ δ w Adm)] at hbound
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (max Cb Cs*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hbound
  exact hcast.trans (mul_le_mul_left hN _)

end WaveTurbulence.Mole.AppbAlgorithm
