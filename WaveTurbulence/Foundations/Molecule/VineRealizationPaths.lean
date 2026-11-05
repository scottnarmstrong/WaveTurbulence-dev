/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionConnected
public import WaveTurbulence.Foundations.Molecule.VineGroupAdjacency
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Actual vine groups are connected (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The undirected template realization lifts paths to the actual induced
half-edge molecule. No connectivity premise is added to the draft. -/
theorem isVine_connected {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) :
    ∀ u ∈ S, ∀ v ∈ S, (Mole.induced M S).SameComponent u v := by
  classical
  obtain ⟨hB,k,hk,f,hf,himage,_hj,he⟩ := h
  let : Nonempty S := ⟨⟨a,hB.2.1⟩⟩
  let fS : S → ℕ := fun v => f v.1
  have hinj : Function.Injective fS := by
    intro u v huv
    exact Subtype.ext (hf u.2 v.2 huv)
  let g : ℕ → S := Function.invFun fS
  have hgf (v : V) (hv : v ∈ S) : (g (f v)).1=v :=
    congrArg Subtype.val (Function.leftInverse_invFun hinj ⟨v,hv⟩)
  have hedge {p q : ℕ} (hpq : EdgeAdj (X.expand k).bonds p q) :
      (Mole.induced M S).Adj (g p).1 (g q).1 := by
    have hm : s(p,q) ∈ ((X.expand k).bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)) := by
      rcases hpq with hpq | hpq
      · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨(p,q),hpq,rfl⟩)
      · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨(q,p),hpq,Sym2.eq_swap⟩)
    rw [← he] at hm
    simp only [Molecule.groupBonds,Multiset.map_map,Multiset.mem_map,
      Finset.mem_val,mem_filter,mem_univ,true_and,Function.comp_apply] at hm
    obtain ⟨x,⟨_hx,hg⟩,hx⟩ := hm
    have heq := Sym2.eq_iff.mp hx
    change (f (M.atom x)=p ∧ f (M.atom (M.mate x))=q) ∨
      (f (M.atom x)=q ∧ f (M.atom (M.mate x))=p) at heq
    apply (Mole.induced_adj_iff M S _ _).mpr
    refine ⟨?_,(g p).2,(g q).2⟩
    rcases heq with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · exact ⟨x,by rw [← hp,hgf _ hg.1],by rw [← hq,hgf _ hg.2]⟩
    · exact ⟨M.mate x,by rw [← hp,hgf _ hg.2],by rw [M.mate_mate,← hq,hgf _ hg.1]⟩
  have lift {p q : ℕ} (hp : Relation.EqvGen (EdgeAdj (X.expand k).bonds) p q) :
      (Mole.induced M S).SameComponent (g p).1 (g q).1 := by
    induction hp with
    | rel u v huv => exact Relation.EqvGen.rel _ _ (hedge huv)
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro u hu v hv
  have hfu : f u < (X.expand k).n := mem_range.mp (himage ▸ mem_image_of_mem f hu)
  have hfv : f v < (X.expand k).n := mem_range.mp (himage ▸ mem_image_of_mem f hv)
  have hp := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (expand_connected X k hk (f u) hfu))
    (expand_connected X k hk (f v) hfv)
  simpa only [hgf u hu,hgf v hv] using lift hp

end WaveTurbulence.Vine
