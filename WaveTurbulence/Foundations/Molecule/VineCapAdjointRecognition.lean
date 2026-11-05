/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapGraphInverse
public import WaveTurbulence.Foundations.Molecule.VineDeletedBondMultiset
public import WaveTurbulence.Foundations.Molecule.VineSideGraphRecognition
import Mathlib.Tactic

/-! # Conditional recognition of a long cap's designated adjoint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Given a literal long-cap realization, deleting the designated added
joint bond gives a pinned type-V vine. This graph-recognition helper keeps
the actual deleted dart, so parallel bonds are never identified or all erased.
The source containment proof must construct the cap realization data. -/
theorem cap_adjoint_isVineV_of_realization {M : Molecule V D} {A : Finset V} {x y : V}
    (e : D) (he : M.ends e=s(x,y)) (hB : (Mole.eraseBond M e).IsBlock A x y)
    (N m : ℕ) (hN : 9 ≤ N) (f : V → ℕ) (hinj : Set.InjOn f A)
    (himage : A.image f=capLabels N ((m+2)+1))
    (hj : s(f x,f y)=s(N+(m+2),N+((m+2)+1)+(m+2)))
    (hbonds : (M.groupBonds A).map (Sym2.map f)=rawBondMultiset (capBonds N ((m+2)+1))) :
    (Mole.eraseBond M e).IsVine .V A x y := by
  let k := m+2
  let g := capToSide N k ∘ f
  have hmem (v : V) (hv : v ∈ A) : f v ∈ capLabels N (k+1) :=
    himage ▸ mem_image_of_mem f hv
  have heA : M.InGroup A e := by
    have he' := Sym2.eq_iff.mp he
    change (M.atom e=x ∧ M.atom (M.mate e)=y) ∨
      (M.atom e=y ∧ M.atom (M.mate e)=x) at he'
    rcases he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1.symm ▸ hB.2.1,h2.symm ▸ hB.2.2.1⟩
    · exact ⟨h1.symm ▸ hB.2.2.1,h2.symm ▸ hB.2.1⟩
  have hdelete := congrArg (Multiset.map (Sym2.map f)) (eraseBond_groupBonds_cons M e A heA)
  rw [Multiset.map_cons,hbonds,he,Sym2.map_mk,hj] at hdelete
  have hcapadj : ((Mole.eraseBond M e).groupBonds A).map (Sym2.map f)=
      rawBondMultiset (capAdjointBonds N k) := by
    apply add_left_cancel (a := ({s(N+k,N+(k+1)+k)} : Multiset (Sym2 ℕ)))
    exact hdelete.trans (capBonds_bondMultiset N k)
  apply side_graph_realization_isVineV hB N m hN g
  · intro u hu v hv hge
    apply hinj hu hv
    have hh := congrArg (sideToCap N k) hge
    simpa only [g,Function.comp_apply,sideToCap_capToSide N k (f u) hN (hmem u hu),
      sideToCap_capToSide N k (f v) hN (hmem v hv)] using hh
  · change A.image (capToSide N k ∘ f)=sideLabels N k
    rw [← Finset.image_image,himage,capToSide_image N k hN]
  · change ({capToSide N k (f x),capToSide N k (f y)} : Finset ℕ)={7,8}
    have hpair := Sym2.eq_iff.mp hj
    rcases hpair with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · rw [hx,hy,capToSide_upper_joint,capToSide_lower_joint]
    · rw [hx,hy,capToSide_upper_joint,capToSide_lower_joint]
      exact pair_comm _ _
  · have hh := congrArg (Multiset.map (Sym2.map (capToSide N k))) hcapadj
    rw [Multiset.map_map,capToSide_bondMultiset N k hN] at hh
    simpa only [g,Function.comp_def,Sym2.map_map] using hh

end WaveTurbulence.Vine
