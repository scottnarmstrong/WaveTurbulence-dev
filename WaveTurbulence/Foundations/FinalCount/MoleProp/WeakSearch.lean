/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualGoodCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodSelector
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OrdinarySearchCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleSourceCount
import Mathlib.Tactic

/-! # Actual finite ordinary search with one gamma-zero saving

The finite search is proved by induction on atom cardinality. Its raw
polynomial loss is retained, so there is no size assumption in this phase.
-/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.MoleProp

theorem weak_search_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C Cstar : ℝ, 0 < C ∧ 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), SearchInput M →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (C*((M.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ))) := by
  classical
  obtain ⟨C,Rg,hC,hG⟩ := actual_good_configuration_normalized_bound d hd γ hγ η hη hηmax
  obtain ⟨Cb,hCb,hB⟩ := simple_molecule_count_bound d hd γ hγ η hη hηmax
  obtain ⟨Co,hCo,hO⟩ := countAFree_le_ordinaryDescendant d hd γ hγ η hη hηmax
  refine ⟨C,max Cb Co,hC,hCb.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Ro,hRo⟩ := hO C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max Rg (max Rb Ro)) 1,?_⟩
  intro L hL hlog V D _ _ _ M hI Adm P hAdm
  have hδp : 0 < δ := hδ.1
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLg : Rg ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLb : Rb ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLo : Ro ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hC1' : 1 ≤ C1 := hCb.trans ((le_max_left _ _).trans hC1)
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card=n → SearchInput N →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGap N L γ η (0 : Mom d) κ) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤
        ENNReal.ofReal (C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN A hALG
      obtain ⟨a,ha,ha3,hstep⟩ := actual_search_progress N hN
      rcases hstep with hgood | ⟨b,hb,hnext,hlt⟩
      · have hcfg := select_actual_good_configuration N hN ha ha3 hgood
        obtain ⟨b,hb,hab,hlocal⟩ := hG L hLg hlog C1 hC1' δ hδ N hN.molecule hN.simple a ha hcfg A P hALG
        have hbase := hRb L hLb (Degen.eraseAtoms N {a,b})
          (Degen.isMolecule_eraseAtoms N hN.molecule {a,b}) (simple_eraseAtoms N {a,b} hN.simple)
          (erasedFreeAdmissibility N {a,b} A) P
          (projected_largeGap N L γ η (0 : Mom d) {a,b} A hALG)
        rcases hlocal with ⟨_hloss,hbound⟩ | ⟨_hloss,hbound⟩
        · exact hbound.trans (by
            simpa only [mul_one] using (mul_le_mul_of_nonneg_left hbase
              (show 0 ≤ ENNReal.ofReal (C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ))) from bot_le)))
        · have hp : L^(-(min γ (1-γ)+η)) ≤ L^(-min γ (1-γ)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη])
          have hc := mul_le_mul_of_nonneg_left hp
            (by positivity : 0 ≤ C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3)
          have hb0 := hbound.trans (by
              simpa only [mul_one] using (mul_le_mul_of_nonneg_left hbase
                (show 0 ≤ ENNReal.ofReal (C*((N.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-(min γ (1-γ)+η))) from bot_le)))
          exact hb0.trans (ENNReal.ofReal_le_ofReal hc)
      · have hneutral := hRo L hLo hlog N hN a ha ha3 b A P hALG
        have hcard : (ordinaryDescendant N a b).atoms.card = (Degen.componentSet (bridgeCore (Degen.eraseAtoms N {a})) b).card := rfl
        have hsmall : (ordinaryDescendant N a b).atoms.card < n := by simpa only [hcard,hn] using hlt
        have hIH := ih _ hsmall (ordinaryDescendant N a b) rfl hnext
          (ordinaryDescendantAdmissibility N a b A)
          (ordinaryDescendantAdmissibility_largeGap N a b L γ η A hALG)
        have hsize : ((ordinaryDescendant N a b).atoms.card : ℝ)+1 ≤ (N.atoms.card : ℝ)+1 := by
          have hh : ((ordinaryDescendant N a b).atoms.card : ℝ) ≤ N.atoms.card := by rw [hcard]; exact_mod_cast hlt.le
          linarith only [hh]
        have hcoef := good_coefficient_le (gain := min γ (1-γ)) hC.le (le_refl C)
          (by positivity : 0 ≤ ((ordinaryDescendant N a b).atoms.card : ℝ)+1) hsize hδ.1.le (zero_le_one.trans hL1)
        exact hneutral.trans (hIH.trans (ENNReal.ofReal_le_ofReal hcoef))
  exact aux _ M rfl hI Adm hAdm

end WaveTurbulence.MoleProp
