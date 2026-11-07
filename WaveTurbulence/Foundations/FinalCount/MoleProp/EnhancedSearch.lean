/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.AuxiliarySaving
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4Normalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.EmptyMolecule
import Mathlib.Tactic

/-! # The enhanced actual search on the internal small-graph branch -/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.MoleProp

theorem enhanced_small_search_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ min γ (1-γ)/200) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), SearchInput M → (M.atoms.card : ℝ) ≤ Real.log L →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L^(-(min γ (1-γ)+η/2))) := by
  classical
  have hg : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hηmax : η ≤ min γ (1-γ)/2 := by linarith only [hηsmall,hg]
  obtain ⟨C,Rg,hC,hG⟩ := actual_good_configuration_normalized_bound d hd γ hγ η hη hηmax
  obtain ⟨Ca,hCa,hA⟩ := auxiliary_small_graph_saving d hd γ hγ η hη hηsmall
  obtain ⟨Cb,hCb,hB⟩ := simple_molecule_count_bound d hd γ hγ η hη hηmax
  obtain ⟨Co,hCo,hO⟩ := countAFree_le_ordinaryDescendant d hd γ hγ η hη hηmax
  refine ⟨max Ca (max Cb Co),hCa.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  have hC1a : Ca ≤ C1 := (le_max_left _ _).trans hC1
  have hC1b : Cb ≤ C1 := (le_max_left _ _).trans ((le_max_right _ _).trans hC1)
  have hC1o : Co ≤ C1 := (le_max_right _ _).trans ((le_max_right _ _).trans hC1)
  have hC1one : 1 ≤ C1 := hCa.trans hC1a
  have hδp : 0 < δ := hδ.1
  obtain ⟨Ra,hRa⟩ := hA C1 hC1a δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 hC1b δ hδ
  obtain ⟨Ro,hRo⟩ := hO C1 hC1o δ hδ
  obtain ⟨Rk,hRk⟩ := K4_normalized_bound d hd γ hγ η hη hηsmall δ hδ
  obtain ⟨R3,hR3⟩ := eventually_log_size_power_gain
    (show 0 ≤ C*(δ⁻¹)^3 by positivity)
    (show min γ (1-γ)+η/2 < min γ (1-γ)+3*η/4 by linarith only [hη]) 2
  obtain ⟨R4,hR4⟩ := eventually_log_size_power_gain
    (show 0 ≤ C*(δ⁻¹)^3 by positivity)
    (show min γ (1-γ)+η/2 < min γ (1-γ)+η by linarith only [hη]) 2
  let R := max Rg (max Ra (max Rb (max Ro (max Rk (max R3 R4)))))
  refine ⟨max R 1,?_⟩
  intro L hL hlog V D _ _ _ M hI hsize Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hRall : Rg ≤ L ∧ Ra ≤ L ∧ Rb ≤ L ∧ Ro ≤ L ∧ Rk ≤ L ∧ R3 ≤ L ∧ R4 ≤ L := by
    simpa only [R,max_le_iff] using (le_max_left R 1).trans hL
  rcases hRall with ⟨hLg,hLa,hLb,hLo,hLk,hL3,hL4⟩
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card=n → SearchInput N → (N.atoms.card : ℝ) ≤ Real.log L →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGap N L γ η (0 : Mom d) κ) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤ ENNReal.ofReal (L^(-(min γ (1-γ)+η/2))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN hsmall A hALG
      obtain ⟨a,ha,ha3,hstep⟩ := actual_search_progress N hN
      rcases hstep with hgood | ⟨b,hb,hnext,hlt⟩
      · have hcfg := select_actual_good_configuration N hN ha ha3 hgood
        obtain ⟨b,hb,hab,hlocal⟩ := hG L hLg hlog C1 hC1one δ hδ N hN.molecule hN.simple a ha hcfg A P hALG
        let Q := Degen.eraseAtoms N {a,b}
        let AQ := erasedFreeAdmissibility N {a,b} A
        have hQM : Q.IsMolecule := Degen.isMolecule_eraseAtoms N hN.molecule {a,b}
        have hQs := simple_eraseAtoms N {a,b} hN.simple
        have hQlg := projected_largeGap N L γ η (0 : Mom d) {a,b} A hALG
        have hQsmall : (Q.atoms.card : ℝ) ≤ Real.log L := by
          have hh : (Q.atoms.card : ℝ) ≤ N.atoms.card := by exact_mod_cast (card_le_card (sdiff_subset : Q.atoms ⊆ N.atoms))
          exact hh.trans hsmall
        rcases hlocal with ⟨hloss,hbound⟩ | ⟨hloss,hbound⟩
        · by_cases hχQ : 0 < Q.circuitRank
          · have haux := hRa L hLa hlog Q hQM (fun x => hN.loopless x.val) hQs hχQ hQsmall AQ P hQlg
            have hh := hbound.trans (mul_le_mul_of_nonneg_left haux (show 0 ≤ ENNReal.ofReal (C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ))) from bot_le))
            have hfactor : C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ))*L^(-(3*η/4)) ≤ L^(-(min γ (1-γ)+η/2)) := by
              have he : L^(-min γ (1-γ))*L^(-(3*η/4))=L^(-(min γ (1-γ)+3*η/4)) := by
                rw [← Real.rpow_add hLp]; congr 1; ring
              calc
                _ = C*(δ⁻¹)^3*((N.atoms.card : ℝ)+1)^2*(L^(-min γ (1-γ))*L^(-(3*η/4))) := by ring
                _ ≤ _ := by rw [he]; exact hR3 L hL3 N.atoms.card hsmall
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ)))] at hh
            exact hh.trans (ENNReal.ofReal_le_ofReal hfactor)
          · have hz : Q.circuitRank=0 := by have hnon := circuitRank_nonneg Q; omega
            have hχN : N.circuitRank=3 := by change N.circuitRank-Q.circuitRank=3 at hloss; omega
            have hk := hRk L hLk C1 hC1one N hN.molecule hN.loopless hN.simple hN.nonempty hN.minDegree hN.connected hχN A P
            have hp : L^(-min γ (1-γ)-η) ≤ L^(-(min γ (1-γ)+η/2)) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
            exact hk.trans (ENNReal.ofReal_le_ofReal hp)
        · have hb0 := hRb L hLb Q hQM hQs AQ P hQlg
          have hh := hbound.trans (by
              simpa only [mul_one] using (mul_le_mul_of_nonneg_left hb0
                (show 0 ≤ ENNReal.ofReal (C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-(min γ (1-γ)+η))) from bot_le)))
          have hs := hR4 L hL4 N.atoms.card hsmall
          have hs' : C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-(min γ (1-γ)+η)) ≤ L^(-(min γ (1-γ)+η/2)) := by
            convert hs using 1; ring
          exact hh.trans (ENNReal.ofReal_le_ofReal hs')
      · have hneutral := hRo L hLo hlog N hN a ha ha3 b A P hALG
        have hcard : (ordinaryDescendant N a b).atoms.card = (Degen.componentSet (bridgeCore (Degen.eraseAtoms N {a})) b).card := rfl
        have hsmall' : (ordinaryDescendant N a b).atoms.card < n := by simpa only [hcard,hn] using hlt
        have hsize' : ((ordinaryDescendant N a b).atoms.card : ℝ) ≤ Real.log L := by
          have hh : ((ordinaryDescendant N a b).atoms.card : ℝ) ≤ N.atoms.card := by rw [hcard]; exact_mod_cast hlt.le
          exact hh.trans hsmall
        exact hneutral.trans (ih _ hsmall' (ordinaryDescendant N a b) rfl hnext hsize'
          (ordinaryDescendantAdmissibility N a b A) (ordinaryDescendantAdmissibility_largeGap N a b L γ η A hALG))
  exact aux _ M rfl hI hsize Adm hAdm

end WaveTurbulence.MoleProp
