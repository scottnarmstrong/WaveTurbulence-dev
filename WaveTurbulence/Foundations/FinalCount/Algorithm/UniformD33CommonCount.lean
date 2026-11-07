/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCutGood

public import WaveTurbulence.Foundations.FinalCount.AppBD33CommonReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBCutExternalSign
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCutGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleCount
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
import Mathlib.Tactic

/-! # The common-neighbour double-pair good count, in both orientations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d33_common_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33same.pattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin AppbPatternKind.d33same.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨Cb,hCb,hbig⟩ := uniform_triple_cut_good_projection_bound d hd γ hγ 1 le_rfl
  obtain ⟨Lb,hLb⟩ := hbig δ hδ.1
  obtain ⟨Ls,hLs⟩ := uniform_cut_triple_card_bound_of_projection_injective
    d (by omega) γ hγ δ η hδ hη hηγ 1
  refine ⟨max Cb 1,hCb.trans_le (le_max_left _ _),max Lb (max Ls (Real.exp 1)),?_⟩
  intro V D instV instF instD L hL hLp M r hM w Adm hLG
  have hexp : Real.exp 1 ≤ L := (le_max_right Ls _).trans ((le_max_right Lb _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let cut := appbD33CommonCutPair r
  let t := appbD33CommonFrame r
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33same.pattern.removed by decide)
  have hcard : r.removedAtoms.card ≤ 2 := by
    change (AppbPatternKind.d33same.pattern.removed.image r.vertex).card ≤ 2
    exact card_image_le.trans (by decide)
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤
      max Cb 1*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    by_cases ho : appbCutSign M r.removedAtoms (r.edge cut.first).val ≠ appbCutSign M r.removedAtoms (r.edge cut.second).val
    · have hg : ∀ κ,κ ∈ p.decorations L γ δ w Adm → (1 : ℝ)⁻¹*L^(-γ) ≤
          ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖ := by
        intro κ hκ
        have h3 : r.vertex 3 ∉ r.removedAtoms :=
          fun hh => (show 3 ∉ AppbPatternKind.d33same.pattern.removed by decide)
            ((r.vertex_mem_removed_iff 3 (by decide)).mp hh)
        have hs2 := appb_cutSign_eq_neg_external M r.removedAtoms (r.edge ⟨2,by decide⟩).val
          (r.vertex 1) (r.vertex 3) (r.endpoints ⟨2,by decide⟩) hv h3
        have hv2 : r.vertex 2 ∈ r.removedAtoms := mem_image_of_mem _ (show 2 ∈ AppbPatternKind.d33same.pattern.removed by decide)
        have hs3 := appb_cutSign_eq_neg_external M r.removedAtoms (r.edge ⟨3,by decide⟩).val
          (r.vertex 2) (r.vertex 3) (r.endpoints ⟨3,by decide⟩) hv2 h3
        have hsign : appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val ≠
            appbIncidenceSign M (r.vertex 3) (r.edge ⟨3,by decide⟩).val := by
          intro he
          apply ho
          change appbCutSign M r.removedAtoms (r.edge ⟨2,by decide⟩).val = appbCutSign M r.removedAtoms (r.edge ⟨3,by decide⟩).val
          rw [hs2,hs3,he]
        have hinc (i : Fin 4) (hi : i = 2 ∨ i = 3) : appbIncidence M (r.vertex 3) (r.edge i).val = 1 := by
          rw [r.edge_incidence i 3 (by decide)]
          rcases hi with rfl | rfl <;> decide
        have hout (i : Fin 4) : M.out (r.edge i).val = true :=
          (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
        have hne : (r.edge ⟨2,by decide⟩).val ≠ (r.edge ⟨3,by decide⟩).val := by
          intro he
          have hh := r.edge.injective (Subtype.ext he)
          have hf := congrArg (fun j : Fin 4 => j.val) hh
          norm_num at hf
        have hh := appb_incidence_large_gap M L w κ _ hκ.1.1 (hLG κ hκ.2.2)
          (r.vertex_mem 3 (by decide)) (hinc 2 (Or.inl rfl)) (hinc 3 (Or.inr rfl)) (hout 2) (hout 3) hne hsign
        have hpw : L^(-γ) ≤ L^(-γ+η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
        change (1 : ℝ)⁻¹*L^(-γ) ≤ ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖
        have hh' : L^(-γ+η) ≤ ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
            Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖ := hh
        simpa only [inv_one,one_mul] using hpw.trans hh' 
      have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ r hM (r.vertex 1) hv t
        r.removedAtoms cut ho hcard 2 rfl p w Adm hg
      rw [card_image_of_injOn (appb_d33_common_projection_injective r p hLp γ δ w Adm)] at hb
      have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
      exact hb.trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hg0]))
        (Real.rpow_nonneg hLp.le _) ((hCb.trans_le (le_max_left _ _)).le))
    · have hc : (r.removedAtoms.card : ℝ) ≤ (1+Real.log L)^1 := by
        have hc' : (r.removedAtoms.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        simpa only [pow_one] using hc'.trans (by linarith only [hlog])
      have hb := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ r r.removedAtoms cut
        (not_ne_iff.mp ho) hc (r.vertex 1) hv t rfl p w Adm
        (appb_d33_common_projection_injective r p hLp γ δ w Adm) (by
          intro hsign κ hκ
          exact appb_tripleFrame_pair_gap r t hv L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
      exact hb.trans ((le_mul_of_one_le_left (Real.rpow_nonneg hLp.le _) (le_max_right Cb 1)))
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (max Cb 1*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
