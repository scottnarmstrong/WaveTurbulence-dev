/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalPairCut
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCutGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleCount
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
import Mathlib.Tactic

/-! # A triple and a degree-two equation sharing one physical label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- Conditional reconstruction helper for basiccount(3). Source figure
exports separately prove the actual triple-projection injectivity. -/
theorem uniform_triple_pair_countE_of_projection_injective (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P), M.IsMolecule →
    ∀ v ∈ r.removedAtoms, ∀ u ∈ r.removedAtoms,
    ∀ (t : AppbTripleFrame r v) (pair : AppbLocalPair r u), pair.first = t.index 2 →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ p : AppbCountParameters M d,Set.InjOn (t.project (K := Fin d → ℤ)) (r.localChoices p hLp γ δ w Adm : Set _)) →
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin P.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨Cb,hCb,hbig⟩ := uniform_triple_cut_good_projection_bound d hd γ hγ 1 le_rfl
  obtain ⟨Lb,hLb⟩ := hbig δ hδ.1
  obtain ⟨Ls,hLs⟩ := uniform_cut_triple_card_bound_of_projection_injective
    d (by omega) γ hγ δ η hδ hη hηγ 0
  refine ⟨max Cb 1,hCb.trans_le (le_max_left _ _),max Lb (max Ls 1),?_⟩
  intro V D instV instF instD L hL hLp M P r hM v hv u hu t pair hfirst w Adm hinj hLG
  have hL1 : 1 ≤ L := (le_max_right Ls 1).trans ((le_max_right Lb _).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let cut := pair.singletonCut hu
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤
      max Cb 1*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    by_cases ho : appbIncidenceSign M u (r.edge pair.first).val ≠ appbIncidenceSign M u (r.edge pair.second).val
    · have hco : appbCutSign M {u} (r.edge cut.first).val ≠ appbCutSign M {u} (r.edge cut.second).val := by
        simpa only [cut,AppbLocalPair.singletonCut,appb_cutSign_singleton] using ho
      have hg : ∀ κ,κ ∈ p.decorations L γ δ w Adm → (1 : ℝ)⁻¹*L^(-γ) ≤
          ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖ := by
        intro κ hκ
        have hout (i : Fin P.edges.length) : M.out (r.edge i).val = true :=
          (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
        have hne : (r.edge pair.first).val ≠ (r.edge pair.second).val :=
          fun he => pair.distinct (r.edge.injective (Subtype.ext he))
        have hh := appb_incidence_large_gap M L w κ _ hκ.1.1 (hLG κ hκ.2.2)
          (r.removedAtoms_subset hu) pair.incidence_first pair.incidence_second (hout _) (hout _) hne ho
        have hpw : L^(-γ) ≤ L^(-γ+η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
        change (1 : ℝ)⁻¹*L^(-γ) ≤ ‖Molecule.kvec L w κ (r.edge pair.first).val-Molecule.kvec L w κ (r.edge pair.second).val‖
        simpa only [inv_one,one_mul] using hpw.trans hh
      have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ r hM v hv t
        {u} cut hco (by simp) 2 hfirst p w Adm hg
      rw [card_image_of_injOn (hinj p)] at hb
      have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
      exact hb.trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hg0]))
        (Real.rpow_nonneg hLp.le _) ((hCb.trans_le (le_max_left _ _)).le))
    · have hco : appbCutSign M {u} (r.edge cut.first).val = appbCutSign M {u} (r.edge cut.second).val := by
        simpa only [cut,AppbLocalPair.singletonCut,appb_cutSign_singleton] using not_ne_iff.mp ho
      have hb := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ r {u} cut
        hco (by simp) v hv t hfirst p w Adm (hinj p) (by
          intro hsign κ hκ
          exact appb_tripleFrame_pair_gap r t hv L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
      exact hb.trans (le_mul_of_one_le_left (Real.rpow_nonneg hLp.le _) (le_max_right Cb 1))
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (max Cb 1*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
