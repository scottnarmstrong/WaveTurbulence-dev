/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertLargeGap
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
import Mathlib.Tactic

/-! # Large-gap transport for the source choice of output direction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_directed_reinsert_largeGap (M : Molecule V D) (Y : Finset V)
    (a b u v : V) (ha : a ∈ M.atoms \ Y) (hb : b ∈ M.atoms \ Y)
    (hu : u ∈ Y) (hv : v ∈ Y) (x y : D)
    (hx : M.ends x = s(a,u)) (hy : M.ends y = s(b,v))
    (hox : M.out x = true) (hoy : M.out y = true)
    (ho : AppbOppositeFrom M a b x y)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hm : ∀ z,κ (M.mate z) = κ z) (g ε : ℝ) (hε : 0 ≤ ε)
    (hgap : AppbLargeGap M L w κ g)
    (hclose : ‖Molecule.kvec L w κ x-Molecule.kvec L w κ y‖ ≤ ε) :
    AppbLargeGap (if M.atom x = a then addBond (Degen.eraseAtoms M Y) a b
      else addBond (Degen.eraseAtoms M Y) b a) L w
      (Sum.elim (fun z : Degen.RetainedDart M Y => κ z.val) (fun _ : Bool => κ x)) (g-ε) := by
  classical
  have hau : a ≠ u := fun he => (mem_sdiff.mp ha).2 (he.symm ▸ hu)
  have hbv : b ≠ v := fun he => (mem_sdiff.mp hb).2 (he.symm ▸ hv)
  have hxcase := Sym2.eq_iff.mp hx
  have hycase := Sym2.eq_iff.mp hy
  by_cases hxa : M.atom x = a
  · rw [if_pos hxa]
    have hxmate : M.atom (M.mate x) = u := by
      rcases hxcase with h | h
      · exact h.2
      · exact (hau (hxa.symm.trans h.1)).elim
    have hyb : M.atom y ≠ b := ho.mp hxa
    have hyv : M.atom y = v ∧ M.atom (M.mate y) = b := by
      rcases hycase with h | h
      · exact (hyb h.1).elim
      · exact h
    let ref : Bool → D := fun t => if t then x else M.mate y
    apply appb_reinsert_largeGap M Y a b ha hb ref
    · intro t
      cases t <;> simp only [ref,Bool.false_eq_true,ite_false,ite_true,hyv.2,hxa]
    · intro t
      cases t <;> simp only [ref,Bool.false_eq_true,ite_false,ite_true,M.out_mate,hox,hoy,Bool.not_true]
    · intro t
      cases t
      · simpa only [ref,Bool.false_eq_true,ite_false,M.mate_mate,hyv.1] using hv
      · simpa only [ref,ite_true,hxmate] using hu
    · exact hε
    · exact hgap
    · intro t
      cases t
      · simpa only [ref,Bool.false_eq_true,ite_false,Molecule.kvec,hm,norm_sub_rev] using hclose
      · simpa only [ref,ite_true,Molecule.kvec,sub_self,norm_zero] using hε
  · rw [if_neg hxa]
    have hxua : M.atom x = u ∧ M.atom (M.mate x) = a := by
      rcases hxcase with h | h
      · exact (hxa h.1).elim
      · exact h
    have hyb : M.atom y = b := by
      by_contra hn
      exact hxa (ho.mpr hn)
    have hymate : M.atom (M.mate y) = v := by
      rcases hycase with h | h
      · exact h.2
      · exact (hbv (hyb.symm.trans h.1)).elim
    let ref : Bool → D := fun t => if t then y else M.mate x
    apply appb_reinsert_largeGap M Y b a hb ha ref
    · intro t
      cases t <;> simp only [ref,Bool.false_eq_true,ite_false,ite_true,hxua.2,hyb]
    · intro t
      cases t <;> simp only [ref,Bool.false_eq_true,ite_false,ite_true,M.out_mate,hox,hoy,Bool.not_true]
    · intro t
      cases t
      · simpa only [ref,Bool.false_eq_true,ite_false,M.mate_mate,hxua.1] using hu
      · simpa only [ref,ite_true,hymate] using hv
    · exact hε
    · exact hgap
    · intro t
      cases t
      · simpa only [ref,Bool.false_eq_true,ite_false,Molecule.kvec,hm,sub_self,norm_zero] using hε
      · simpa only [ref,ite_true,Molecule.kvec,norm_sub_rev] using hclose

end WaveTurbulence.Mole
