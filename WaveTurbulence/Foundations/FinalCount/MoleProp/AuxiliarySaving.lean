/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.WeakSearch
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103AuxGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaRank
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneCircuitGain
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedAdmissibility
import Mathlib.Tactic

/-! # One auxiliary saving on any actual simple positive-rank molecule

The size condition occurs only inside the final large/small graph split.
After one degree-two or beta saving the baseline count suffices; no false
minimum-degree preservation assertion is needed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem auxiliary_small_graph_saving (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ min γ (1-γ)/200) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ x, M.atom x ≠ M.atom (M.mate x)) →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → 0 < M.circuitRank →
      (M.atoms.card : ℝ) ≤ Real.log L →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L^(-(3*η/4))) := by
  classical
  have hg : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hηmax : η ≤ min γ (1-γ)/2 := by linarith only [hηsmall,hg]
  have hweak : 3*η/4 < min γ (1-γ) := by linarith only [hηsmall,hg]
  obtain ⟨Cw,Cs,hCw,hCs,hW⟩ := weak_search_normalized_bound d hd γ hγ η hη hηmax
  obtain ⟨Cb,hCb,hB⟩ := simple_molecule_count_bound d hd γ hγ η hη hηmax
  obtain ⟨Ci,hCi,hI⟩ := countAFree_le_induced_component d hd γ hγ η hη hηmax
  refine ⟨max Cs (max Cb Ci),hCs.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  have hC1s : Cs ≤ C1 := (le_max_left _ _).trans hC1
  have hC1b : Cb ≤ C1 := (le_max_left _ _).trans ((le_max_right _ _).trans hC1)
  have hC1i : Ci ≤ C1 := (le_max_right _ _).trans ((le_max_right _ _).trans hC1)
  have hC1one : 1 ≤ C1 := hCs.trans hC1s
  have hδp : 0 < δ := hδ.1
  obtain ⟨Rw,hRw⟩ := hW C1 hC1s δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 hC1b δ hδ
  obtain ⟨Ri,hRi⟩ := hI C1 hC1i δ hδ
  obtain ⟨Rtwo,hRtwo⟩ := countAFree_erase_one_circuit_gain d hd γ hγ η hη hηmax δ hδ
  obtain ⟨Rbeta,hRbeta⟩ := split_quad_normalized_bound d hd γ hγ η hη hηmax δ hδ
  obtain ⟨Rwa,hRwa⟩ := eventually_log_size_power_gain
    (show 0 ≤ Cw*(δ⁻¹)^3 by positivity) hweak 2
  obtain ⟨Rba,hRba⟩ := eventually_log_size_power_gain (show (0 : ℝ) ≤ 1 by norm_num)
    (show 3*η/4 < η by linarith only [hη]) 2
  let R := max Rw (max Rb (max Ri (max Rtwo (max Rbeta (max Rwa Rba)))))
  refine ⟨max R 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hloop hsimp hχ hsize Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hRall : Rw ≤ L ∧ Rb ≤ L ∧ Ri ≤ L ∧ Rtwo ≤ L ∧ Rbeta ≤ L ∧ Rwa ≤ L ∧ Rba ≤ L := by
    simpa only [R,max_le_iff] using (le_max_left R 1).trans hL
  rcases hRall with ⟨hLw,hLb,hLi,hLtwo,hLbeta,hLwa,hLba⟩
  obtain ⟨a,ha,hQ⟩ := exists_aux_core_component M hM hloop hsimp hχ
  let Q := Mole.induced (bridgeCore M) (Degen.componentSet (bridgeCore M) a)
  rcases hQ with ⟨hQM,hQl,hQs,hQne,hQc,hQmin,hQbridge,hQχ,hQcard⟩
  let A := inducedFreeAdmissibility (bridgeCore M) (Degen.componentSet (bridgeCore M) a)
    (bridgeCoreAdmissibility M Adm)
  have hALG : ∀ κ, A κ → LargeGap Q L γ η (0 : Mom d) κ :=
    inducedFreeAdmissibility_largeGap _ _ L γ η (0 : Mom d) _
      (bridgeCoreAdmissibility_largeGap M L γ η (0 : Mom d) Adm hAdm)
  have hQsize : (Q.atoms.card : ℝ) ≤ Real.log L := by
    have hh : (Q.atoms.card : ℝ) ≤ M.atoms.card := by exact_mod_cast hQcard
    exact hh.trans hsize
  have hneutral : countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ countAFree Q L γ δ C1 (0 : Mom d) A P :=
    (countAFree_le_bridgeCore M hsimp hLp.ne' γ δ C1 (0 : Mom d) Adm P).trans
      (hRi L hLi hlog (bridgeCore M) (bridgeCore_isMolecule M hM) (simple_bridgeCore M hsimp) a _ P
        (bridgeCoreAdmissibility_largeGap M L γ η (0 : Mom d) Adm hAdm))
  apply hneutral.trans
  by_cases htwo : ∃ v ∈ Q.atoms, Q.deg v=2
  · obtain ⟨v,hv,hv2⟩ := htwo
    have hχv := circuitRank_erase_two_of_no_incident_bridges Q hQl hv hv2 (fun e _ => hQbridge e)
    have hstep := hRtwo L hLtwo hlog C1 hC1one Q hQM v hv (Or.inl hv2)
      (no_operation_b_of_simple Q hQs) hχv A P hALG
      (by rw [ladderCells_eq_empty_of_simple Q hQs]; simp)
    have hbase := hRb L hLb (Degen.eraseAtoms Q {v}) (Degen.isMolecule_eraseAtoms Q hQM {v})
      (simple_eraseAtoms Q {v} hQs) (erasedFreeAdmissibility Q {v} A) P
      (projected_largeGap Q L γ η (0 : Mom d) {v} A hALG)
    have he := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ ENNReal.ofReal (L^(-(η-η/4))) from bot_le)
    have hs : -(η-η/4)=-(3*η/4) := by ring
    exact hstep.trans (by simpa only [mul_one,hs] using he)
  by_cases hbeta : AdmitsBetaSplit Q
  · obtain ⟨v,x,y,hdcut,hv4,hnb,hdisc⟩ := hbeta
    have hx : Q.atom x=v := Option.some.inj hdcut.2.2.1
    have hy : Q.atom y=v := Option.some.inj hdcut.2.2.2.1
    have hv : v ∈ Q.atoms := hx ▸ Q.atom_mem x
    obtain ⟨r,s,hr,hs,hro,hso,hxy,hxr,hxs,hyr,hys,hrs,hstar⟩ :=
      exists_remaining_mixed_pair Q hQM hv hv4 hx hy hdcut.2.2.2.2.2.1 hdcut.2.2.2.2.2.2
    obtain ⟨U,hU,hcut,_⟩ := exists_old_cut_of_beta_split Q hQl hx hy hdisc
    have hUold : U ⊆ Q.atoms := fun z hz => (mem_sdiff.mp (hU hz)).1
    have hsn : s ∉ ({x,y,r} : Finset _) := by
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨Ne.symm hxs,Ne.symm hys,Ne.symm hrs⟩
    have hχv := circuitRank_erase_beta_joint Q hQM hQl hdcut hv4 hnb hdisc
    have hstep := hRbeta L hLbeta hlog C1 hC1one Q hQs v hv x y r s hxy hxr hyr hsn hstar
      hdcut.2.2.2.2.2.1 hdcut.2.2.2.2.2.2 hro hso U hUold hcut hχv A P hALG
    have hbase := hRb L hLb (Degen.eraseAtoms Q {v}) (Degen.isMolecule_eraseAtoms Q hQM {v})
      (simple_eraseAtoms Q {v} hQs) (erasedFreeAdmissibility Q {v} A) P
      (projected_largeGap Q L γ η (0 : Mom d) {v} A hALG)
    have hscalar : ((U.card : ℝ)+1)^2*L^(-η) ≤ L^(-(3*η/4)) := by
      have hcard : (U.card : ℝ) ≤ Q.atoms.card := by exact_mod_cast card_le_card hUold
      have hadd : (U.card : ℝ)+1 ≤ (Q.atoms.card : ℝ)+1 := by linarith only [hcard]
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (U.card : ℝ)+1) hadd 2
      have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hLp.le (-η))
      have habs := hRba L hLba Q.atoms.card hQsize
      simp only [one_mul] at habs
      exact hh.trans habs
    have hh := hstep.trans (by
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left hbase
          (show 0 ≤ ENNReal.ofReal (((U.card : ℝ)+1)^2*L^(-η)) from bot_le)))
    exact hh.trans (ENNReal.ofReal_le_ofReal hscalar)
  · have hSearch := searchInput_of_min_two_no_two_no_beta Q hQM hQl hQs hQne hQc hQmin hQbridge htwo hbeta
    have hw := hRw L hLw hlog Q hSearch A P hALG
    have habs := hRwa L hLwa Q.atoms.card hQsize
    have hscalar : Cw*((Q.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ)) ≤ L^(-(3*η/4)) := by
      convert habs using 1; ring
    exact hw.trans (ENNReal.ofReal_le_ofReal hscalar)

end WaveTurbulence.MoleProp
