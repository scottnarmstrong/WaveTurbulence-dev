/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32Frame
public import WaveTurbulence.Foundations.FinalCount.AppBR32CutPair
public import WaveTurbulence.Foundations.FinalCount.AppBCutSignAt
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformPolylogTripleCut
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleProjection
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
import Mathlib.Tactic

/-! # First-triple gain for direct-entry or equal-sign cuts in 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

/-- Graph-conditional helper for the direct-entry case. The final source
export chooses the cut and discharges the common-endpoint condition. -/
theorem uniform_r32_direct_or_positive_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
      M.IsMolecule → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3)
      (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val}),
      (appbCutSign M S (r.edge j).val ≠ appbCutSign M S (s.edge ⟨0,by decide⟩).val.val →
        ∃ a ∈ S,appbIncidence M a (r.edge j).val = 1 ∧ appbIncidence M a (s.edge ⟨0,by decide⟩).val.val = 1) →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ((((r.combinedRemoval s v0).localChoices p hLp γ δ w Adm).image
        (appbR32Frame r s v0 (Equiv.swap j 2)).project).card : ℝ) ≤
        C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  obtain ⟨C,hC,hbase⟩ := uniform_triple_cut_polylog_projection_bound d hd γ hγ 1 le_rfl m
  obtain ⟨Lb,hLb⟩ := hbase δ hδ.1
  obtain ⟨Ls,hLs⟩ := uniform_cut_triple_projection_bound d (by omega) γ hγ δ η hδ hη hηγ m
  refine ⟨max C 1,max Lb (max Ls 1),hC.trans_le (le_max_left _ _),?_⟩
  intro V D instV instF instD L hL hLp M r s v0 hM hsize S hS j hcross hshared p w Adm hLG
  have hL1 : 1 ≤ L := (le_max_right Ls 1).trans ((le_max_right Lb _).trans hL)
  have hlog := Real.log_nonneg hL1
  let b := r.combinedRemoval s v0
  let cut := appbR32CutPair r s v0 S hS j hcross
  let π : Equiv.Perm (Fin 3) := Equiv.swap j 2
  let t := appbR32Frame r s v0 π
  have hv := appb_r32_center_removed r s v0
  have hcard : (S.card : ℝ) ≤ (1+Real.log L)^m := by
    have hh := Finset.card_le_card cut.subset_atoms
    exact (show (S.card : ℝ) ≤ (M.atoms.card : ℝ) by exact_mod_cast hh).trans hsize
  have hthird : cut.first = t.index 2 := by
    change r.combinedLeftIndex s j = (appbR32Frame r s v0 π).index 2
    rw [appb_r32_frame_index,show π 2 = j from Equiv.swap_apply_right j 2]
  have heL : (b.edge (r.combinedLeftIndex s j)).val = (r.edge j).val := r.combined_edge_left s v0 j
  have heR : (b.edge (r.combinedRightIndex s ⟨0,by decide⟩)).val = (s.edge ⟨0,by decide⟩).val.val :=
    r.combined_edge_right s v0 ⟨0,by decide⟩
  by_cases ho : appbCutSign M S (b.edge cut.first).val ≠ appbCutSign M S (b.edge cut.second).val
  · have hoOld := ho
    change appbCutSign M S (b.edge (r.combinedLeftIndex s j)).val ≠
      appbCutSign M S (b.edge (r.combinedRightIndex s ⟨0,by decide⟩)).val at hoOld
    rw [heL,heR] at hoOld
    obtain ⟨a,ha,hia,hja⟩ := hshared hoOld
    have hi : appbIncidence M a (b.edge cut.first).val = 1 := by
      change appbIncidence M a (b.edge (r.combinedLeftIndex s j)).val = 1
      rw [heL]
      exact hia
    have hj : appbIncidence M a (b.edge cut.second).val = 1 := by
      change appbIncidence M a (b.edge (r.combinedRightIndex s ⟨0,by decide⟩)).val = 1
      rw [heR]
      exact hja
    have hg : ∀ κ,κ ∈ p.decorations L γ δ w Adm → (1 : ℝ)⁻¹*L^(-γ) ≤
        ‖Molecule.kvec L w κ (b.edge cut.first).val-Molecule.kvec L w κ (b.edge cut.second).val‖ := by
      intro κ hκ
      have hh := cut.large_gap_at a ha hi hj ho L w κ _ hκ.1.1 (hLG κ hκ.2.2)
      have hpw : L^(-γ) ≤ L^(-γ+η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
      simpa only [inv_one,one_mul] using hpw.trans hh
    have hcard2 : (S.card : ℝ) ≤ 2*(1+Real.log L)^m := hcard.trans (by
      have hp : 0 ≤ (1+Real.log L)^m := by positivity
      linarith only [hp])
    have hb := hLb V D L ((le_max_left _ _).trans hL) hLp M _ b hM (r.vertex 1) hv t S cut ho hcard2 2 hthird p w Adm hg
    have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
    exact hb.trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hg0]))
      (Real.rpow_nonneg hLp.le _) ((hC.trans_le (le_max_left _ _)).le))
  · have hb := hLs V D L ((le_max_left Ls _).trans ((le_max_right Lb _).trans hL)) hLp M _ b S cut
      (not_ne_iff.mp ho) hcard (r.vertex 1) hv t hthird p w Adm (by
        intro hsign κ hκ
        exact appb_tripleFrame_pair_gap b t hv L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
    exact hb.trans (le_mul_of_one_le_left (Real.rpow_nonneg hLp.le _) (le_max_right C 1))

end WaveTurbulence.Mole.AppbAlgorithm
