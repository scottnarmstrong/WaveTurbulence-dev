/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamExpandInduct
public import WaveTurbulenceVineParam.VineParamRealizationBondModel
public import WaveTurbulenceVineParam.VineParamBondDegrees
public import WaveTurbulenceVineParam.VineParamRealizedDegrees
public import WaveTurbulenceVineParam.Contract
public import WaveTurbulenceVineParam.VineParamCurrentBlocks
import Mathlib.Tactic

/-! # VINEPARAM from the expanded-template induction -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

theorem vineparam_of_base (hBase : ∀ X : VineType,BaseChartStatement X) :
    VineParamContract.VINEPARAM := by
  intro V D _ _ M hM X S a b hV
  classical
  obtain ⟨hBl0,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hBl := degreeBlock_of_isBlock M hBl0
  obtain ⟨e,hshape,_⟩ := exists_realized_directed_model hM R hBl
  let Q := realizationBondModel R e
  have hdeg := realization_directed_degrees M hM R hBl
  have hshadow : (univ : Finset (Fin (X.expand R.k).bonds.length)).val.map
      (fun j => s((Q.ends j).1.1,(Q.ends j).2.1)) = bondSym (X.expand R.k).bonds := by
    have h1 : (univ : Finset (Fin (X.expand R.k).bonds.length)).val.map
        (fun j => s((Q.ends j).1.1,(Q.ends j).2.1)) =
        ((List.ofFn (realizedEnds R e) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun p => s(p.1,p.2)) := by
      rw [Multiset.map_coe,List.map_ofFn,← Fin.univ_val_map]
      rfl
    rw [h1,hshape]
    rfl
  have hbal : ∀ v,(∑ j,-energySign Q.ends v j) = 0 := by
    intro v
    have hq := hdeg v
    have ht := tail_count M S e (R.atomAt v).1
    have hh := head_count M S e (R.atomAt v).1
    have hc1 : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter fun j => (Q.ends j).1 = v).card =
        ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
          fun i => M.atom (e i).1 = (R.atomAt v).1).card := by
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [← Q.atom_val_eq_iff,← Q.tail j]
      rfl
    have hc2 : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter fun j => (Q.ends j).2 = v).card =
        ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
          fun i => M.atom (M.mate (e i).1) = (R.atomAt v).1).card := by
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [← Q.atom_val_eq_iff,← Q.head j]
      rfl
    simp only [energySign,neg_sub]
    rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole,hc1,hc2,ht,hh,hq.1,hq.2]
    simp
  have hab := hBl.2.2.2.1
  have hj := R.joints_eq
  have hfa : R.f a ∈ ({0,1} : Finset ℕ) := hj ▸ Finset.mem_insert_self _ _
  have hfb : R.f b ∈ ({0,1} : Finset ℕ) := hj ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hne : R.f a ≠ R.f b := fun h => hab (R.injOn hBl.2.1 hBl.2.2.1 h)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hfa hfb
  let D' : ExpData X R.k Q.ends := { lab := Equiv.refl _,shadow := hshadow,balanced := hbal }
  let a' : Fin (X.expand R.k).n := (realizationAtomEquiv R).symm ⟨a,hBl.2.1⟩
  let b' : Fin (X.expand R.k).n := (realizationAtomEquiv R).symm ⟨b,hBl.2.2.1⟩
  have hjb : R.f b < 2 := by omega
  obtain ⟨P,-,-⟩ := exists_physical_expanded X (hBase X) _ R.k rfl R.length_eq
    (Fin (X.expand R.k).n) (Fin (X.expand R.k).bonds.length) Q.ends D' a' b' ⟨R.f b,hjb⟩
    (by change R.f a = 1-R.f b; omega) rfl
  have e1 : (Q.atom a').1 = a := by
    change ((realizationAtomEquiv R) ((realizationAtomEquiv R).symm ⟨a,hBl.2.1⟩)).1 = a
    rw [Equiv.apply_symm_apply]
  have e2 : (Q.atom b').1 = b := by
    change ((realizationAtomEquiv R) ((realizationAtomEquiv R).symm ⟨b,hBl.2.2.1⟩)).1 = b
    rw [Equiv.apply_symm_apply]
  have F := Q.pullFullChart P.full P.distinct
  rw [e1,e2] at F
  exact ⟨F⟩

end WaveTurbulence.Vine.Param
