/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformPolylogTripleCut
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleProjection

public import WaveTurbulence.Foundations.FinalCount.AppBD336FirstTriple
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformPolylogTripleCut
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleProjection
import Mathlib.Tactic

/-! # Good first-triple gain in the four-circuit branch of 3D3-6G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_d336_split_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33new.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) → r.post.numComponents = 2 →
      (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      (((r.localChoices p hLp γ δ w Adm).image (appbD336FirstTriple r).project).card : ℝ) ≤
        C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  obtain ⟨C,hC,hbase⟩ := uniform_triple_cut_polylog_projection_bound d hd γ hγ 1 le_rfl m
  obtain ⟨Lb,hLb⟩ := hbase δ hδ.1
  obtain ⟨Ls,hLs⟩ := uniform_cut_triple_projection_bound d (by omega) γ hγ δ η hδ hη hηγ m
  refine ⟨max C 1,max Lb (max Ls 1),hC.trans_le (le_max_left _ _),?_⟩
  intro V D instV instF instD L hL hLp M r hM hc hF hsize p w Adm hLG
  have hL1 : 1 ≤ L := (le_max_right Ls 1).trans ((le_max_right Lb _).trans hL)
  have hlog := Real.log_nonneg hL1
  let cut := appbD336CutPair r hc hF
  let t := appbD336FirstTriple r
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (by decide)
  have hcard : ((appbD336SplitSide r).card : ℝ) ≤ (1+Real.log L)^m := by
    have hh := Finset.card_le_card cut.subset_atoms
    exact (show ((appbD336SplitSide r).card : ℝ) ≤ (M.atoms.card : ℝ) by exact_mod_cast hh).trans hsize
  by_cases ho : appbCutSign M (appbD336SplitSide r) (r.edge cut.first).val ≠
      appbCutSign M (appbD336SplitSide r) (r.edge cut.second).val
  · have hg : ∀ κ,κ ∈ p.decorations L γ δ w Adm → (1 : ℝ)⁻¹*L^(-γ) ≤
        ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖ := by
      intro κ hκ
      have hh := appb_d336_cut_large_gap r hc hF ho L w κ _ hκ.1.1 (hLG κ hκ.2.2)
      have hpw : L^(-γ) ≤ L^(-γ+η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
      simpa only [cut,appbD336CutPair,inv_one,one_mul] using hpw.trans hh
    have hcard2 : ((appbD336SplitSide r).card : ℝ) ≤ 2*(1+Real.log L)^m :=
      hcard.trans (by
        have hp : 0 ≤ (1+Real.log L)^m := by positivity
        linarith only [hp])
    have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ r hM (r.vertex 1) hv t
      (appbD336SplitSide r) cut ho hcard2 2 rfl p w Adm hg
    have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
    exact hb.trans (mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hg0]))
      (Real.rpow_nonneg hLp.le _) ((hC.trans_le (le_max_left _ _)).le))
  · have hb := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ r
      (appbD336SplitSide r) cut (not_ne_iff.mp ho) hcard (r.vertex 1) hv t rfl p w Adm (by
        intro hsign κ hκ
        exact appb_tripleFrame_pair_gap r t hv L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
    exact hb.trans (le_mul_of_one_le_left (Real.rpow_nonneg hLp.le _) (le_max_right C 1))

end WaveTurbulence.Mole.AppbAlgorithm
