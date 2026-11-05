/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailReversal
public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineGroupAdjacency
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # Transfer vertex connectivity from explicit finite label graphs -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An injective finite labeling transfers literal edges to actual edges
when its complete internal bond multiset is known. -/
theorem adj_of_label_bonds {M : Molecule V D} {A : Finset V}
    (f : V → ℕ) (hinj : Set.InjOn f A) (es : List (ℕ×ℕ))
    (hb : (M.groupBonds A).map (Sym2.map f)=rawBondMultiset es)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (he : EdgeAdj es (f u) (f v)) : M.Adj u v := by
  have hm : s(f u,f v) ∈ rawBondMultiset es := by
    rcases he with he | he
    · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_,he,rfl⟩)
    · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_,he,Sym2.eq_swap⟩)
  rw [← hb] at hm
  simp only [Molecule.groupBonds,Multiset.map_map,Multiset.mem_map,
    Finset.mem_val,mem_filter,mem_univ,true_and,Function.comp_apply] at hm
  obtain ⟨x,⟨_hx,hg⟩,hx⟩ := hm
  have heq := Sym2.eq_iff.mp hx
  change (f (M.atom x)=f u ∧ f (M.atom (M.mate x))=f v) ∨
    (f (M.atom x)=f v ∧ f (M.atom (M.mate x))=f u) at heq
  rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨x,hinj hg.1 hu h1,hinj hg.2 hv h2⟩
  · exact ⟨M.mate x,hinj hg.2 hu h2,by rw [M.mate_mate]; exact hinj hg.1 hv h1⟩

omit [Fintype D] in
/-- Finite label paths avoiding each deleted label prove actual connectivity
following any one-atom deletion. All graph data are supplied explicitly. -/
theorem erase_connected_of_label_paths {M : Molecule V D} {A : Finset V}
    (a : V) (ha : a ∈ A) (f : V → ℕ) (hinj : Set.InjOn f A)
    (W : Finset ℕ) (himage : A.image f=W) (es : List (ℕ×ℕ))
    (hend : ∀ e ∈ es,e.1 ∈ W ∧ e.2 ∈ W)
    (hedge : ∀ u ∈ A,∀ v ∈ A,EdgeAdj es (f u) (f v) → M.Adj u v)
    (hconn : GroupConnected M A)
    (hpaths : ∀ z ∈ W,∀ u ∈ W,∀ v ∈ W,u ≠ z → v ≠ z → AvoidPath es z u v)
    (z : V) : GroupConnected M (A.erase z) := by
  classical
  by_cases hz : z ∈ A
  · let g : ℕ → V := fun i => if hi : ∃ v ∈ A,f v=i then Classical.choose hi else a
    have hgm (i : ℕ) : g i ∈ A := by
      dsimp only [g]
      split_ifs with hi
      · exact (Classical.choose_spec hi).1
      · exact ha
    have hgl (i : ℕ) (hi : i ∈ W) : f (g i)=i := by
      have hex : ∃ v ∈ A,f v=i := mem_image.mp (himage.symm ▸ hi)
      dsimp only [g]
      rw [dite_eq_left hex]
      exact (Classical.choose_spec hex).2
    have hgf (v : V) (hv : v ∈ A) : g (f v)=v :=
      hinj (hgm _) hv (hgl _ (himage ▸ mem_image_of_mem f hv))
    have hstep (p q : ℕ) (hpq : AvoidAdj es (f z) p q) :
        (Mole.induced M (A.erase z)).Adj (g p) (g q) := by
      have hw : p ∈ W ∧ q ∈ W := hpq.2.2.elim (fun h => hend _ h) (fun h => (hend _ h).symm)
      have hpz : g p ≠ z := by
        intro he
        exact hpq.1 ((hgl p hw.1).symm.trans (congrArg f he))
      have hqz : g q ≠ z := by
        intro he
        exact hpq.2.1 ((hgl q hw.2).symm.trans (congrArg f he))
      apply (Mole.induced_adj_iff M _ _ _).mpr
      refine ⟨hedge _ (hgm p) _ (hgm q) ?_,mem_erase.mpr ⟨hpz,hgm p⟩,
        mem_erase.mpr ⟨hqz,hgm q⟩⟩
      rw [hgl p hw.1,hgl q hw.2]
      exact hpq.2.2
    have lift {p q : ℕ} (hp : AvoidPath es (f z) p q) :
        (Mole.induced M (A.erase z)).SameComponent (g p) (g q) := by
      induction hp with
      | rel u v huv => exact Relation.EqvGen.rel _ _ (hstep u v huv)
      | refl u => exact Relation.EqvGen.refl _
      | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    intro u hu v hv
    obtain ⟨huz,huA⟩ := mem_erase.mp hu
    obtain ⟨hvz,hvA⟩ := mem_erase.mp hv
    have hp := hpaths (f z) (himage ▸ mem_image_of_mem f hz)
      (f u) (himage ▸ mem_image_of_mem f huA) (f v) (himage ▸ mem_image_of_mem f hvA)
      (fun he => huz (hinj huA hz he)) (fun he => hvz (hinj hvA hz he))
    simpa only [hgf u huA,hgf v hvA] using lift hp
  · rw [Finset.erase_eq_self.mpr hz]
    exact hconn

end WaveTurbulence.Vine
