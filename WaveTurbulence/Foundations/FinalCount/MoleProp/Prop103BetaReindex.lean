/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaState
import Mathlib.Tactic

/-! # Source beta data is invariant under actual dart relabeling -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
universe u v
variable {V : Type u} {D E : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- Actual graph isomorphism transports the source beta operation; it does
not assume any counting or removal-state conclusion. -/
theorem admitsBetaSplit_of_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ z, N.atom (f z) = M.atom z)
    (hm : ∀ z, N.mate (f z) = f (M.mate z)) (ho : ∀ z, N.out (f z) = M.out z) :
    AdmitsBetaSplit N → AdmitsBetaSplit M := by
  classical
  rintro ⟨v,p,q,hd,h4,hnb,hdisc⟩
  let x := f.symm p
  let y := f.symm q
  have hfx : f x = p := f.apply_symm_apply p
  have hfy : f y = q := f.apply_symm_apply q
  have hvN : v ∈ N.atoms := by
    obtain ⟨a,ha,hav⟩ := mem_map.mp hd.1
    change some a = some v at hav
    exact Option.some.inj hav ▸ ha
  have hv : v ∈ M.atoms := hA.symm ▸ hvN
  have hpx : N.atom p = v := Option.some.inj hd.2.2.1
  have hqy : N.atom q = v := Option.some.inj hd.2.2.2.1
  have hx : M.atom x = v := (ha x).symm.trans (hfx.symm ▸ hpx)
  have hy : M.atom y = v := (ha y).symm.trans (hfy.symm ▸ hqy)
  have hxo : M.out x = false := (ho x).symm.trans (hfx.symm ▸ hd.2.2.2.2.2.1)
  have hyo : M.out y = true := (ho y).symm.trans (hfy.symm ▸ hd.2.2.2.2.2.2)
  have hdeg : M.deg v = N.deg v := by
    apply card_bij (fun z _ => f z)
    · intro z hz
      exact (Mole.mem_dartsAt N v _).mpr ((ha z).trans ((Mole.mem_dartsAt M v z).mp hz))
    · intro z _ w _ h
      exact f.injective h
    · intro z hz
      refine ⟨f.symm z,?_,f.apply_symm_apply z⟩
      apply (Mole.mem_dartsAt M v _).mpr
      have hh := ha (f.symm z)
      rw [f.apply_symm_apply] at hh
      exact hh.symm.trans ((Mole.mem_dartsAt N v z).mp hz)
  have hxy : y ≠ M.mate x := by
    intro h
    apply hd.2.2.2.2.1
    change q = N.mate p
    rw [← hfy, ← hfx, hm, h]
  have hd0 := isCutData_withFreshAtom M hv hx hy hxy hxo hyo
  refine ⟨v,x,y,hd0,hdeg.trans h4,?_,?_⟩
  · intro z hz hb
    exact hnb (f z) ((ha z).trans hz) ((isBridge_dart_equiv_iff M N f ha hm z).mpr hb)
  · intro hp
    apply hdisc
    let CM := (withFreshAtom M).cut (some v) none x y
    let CN := (withFreshAtom N).cut (some v) none p q
    have hca (z : D) : CN.atom (f z) = CM.atom z := by
      change (if some (N.atom (f z)) = some v ∧ f z ≠ p ∧ f z ≠ q then none else some (N.atom (f z))) =
        (if some (M.atom z) = some v ∧ z ≠ x ∧ z ≠ y then none else some (M.atom z))
      rw [ha z]
      have hxp : (f z ≠ p) ↔ z ≠ x := by rw [← hfx]; exact not_congr f.injective.eq_iff
      have hyq : (f z ≠ q) ↔ z ≠ y := by rw [← hfy]; exact not_congr f.injective.eq_iff
      simp only [hxp,hyq]
    exact Relation.EqvGen.mono (fun a b ⟨z,hza,hzb⟩ =>
      ⟨f z,(hca z).trans hza,by
        change CN.atom (N.mate (f z)) = b
        rw [hm,hca]
        exact hzb⟩) (some v) none hp

end WaveTurbulence.MoleProp
