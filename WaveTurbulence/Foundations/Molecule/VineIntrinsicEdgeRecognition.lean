/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineUndoubledCore
public import WaveTurbulence.Foundations.Molecule.VineRungOldNeighbors
public import WaveTurbulence.Foundations.Molecule.VineActualCoreAdjacency
import Mathlib.Tactic

/-! # Every intrinsic coherence edge stays in one prescribed group -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A doubled pair with a common old nonjoint neighbor cannot be fresh. -/
theorem VineRealization.double_triangle_old (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b u v w : V} (R : VineRealization M X S a b)
    (huold : R.f u<X.template.n) (hu2 : 2 ≤ R.f u)
    (hv : v ∈ S) (T : TwoIncidences M v w) (huv : M.Adj u v) (huw : M.Adj u w) :
    R.f v<X.template.n := by
  by_contra h
  obtain ⟨A,i,hi,hin,he⟩ := R.fresh_slot hv (by omega)
  rcases he with rfl | rfl
  · have hw := A.Q.upper_double_neighbor M hM A.frame.upper_injective i hi hin T
    subst w
    exact A.old_nonjoint_not_both M hM i hi hin huold hu2
      (Mole.adj_symmetric M huv) (Mole.adj_symmetric M huw)
  · have hw := A.Q.lower_double_neighbor M hM A.frame.lower_injective i hi hin T
    subst w
    exact A.old_nonjoint_not_both M hM i hi hin huold hu2
      (Mole.adj_symmetric M huw) (Mole.adj_symmetric M huv)

/-- III's intrinsic triangle attachment belongs to its prescribed group. -/
theorem VineRealization.undoubled_triangle_same_group (M : Molecule V D)
    (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b u v w : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    (hu : CoherenceUndoubled M S a b u) (hd : CoherenceDouble M S a b v w)
    (huv : M.Adj u v) (huw : M.Adj u w) : SameRealizedGroup R u v := by
  obtain ⟨hv,hw,hvw,⟨T⟩⟩ := hd
  have huo := R.undoubled_old M hB hu
  have nonjoint (z : V) (hz : VineInterior S a b z) : 2 ≤ R.f z := by
    have hh := realization_index_lt_two_iff R hB hz.1
    exact Nat.le_of_not_gt (fun h => (hh.mp h).elim hz.2.1 hz.2.2)
  have hu2 := nonjoint u hu.1
  have hvo := R.double_triangle_old M hM huo hu2 hv.1 T huv huw
  have hwo := R.double_triangle_old M hM huo hu2 hw.1 T.mates huw huv
  have hneuv : u ≠ v := by
    intro he; subst v
    exact hu.2 _ ⟨hv,hw,hvw,⟨T⟩⟩
  have hneuw : u ≠ w := by
    intro he; subst w
    exact hu.2 _ ⟨hw,hv,hvw.symm,⟨T.mates⟩⟩
  have hadj : M.Adj v w := ⟨T.dart 0,T.atom_eq 0,T.neighbor_eq 0⟩
  obtain ⟨q,_hsize,hug,hvg,_hwg⟩ := template_triangle_same_group X
    ⟨R.f u,huo⟩ ⟨R.f v,hvo⟩ ⟨R.f w,hwo⟩ hu2 (nonjoint v hv) (nonjoint w hw)
    (fun he => hneuv (R.injOn hu.1.1 hv.1 (congrArg Fin.val he)))
    (fun he => hvw (R.injOn hv.1 hw.1 (congrArg Fin.val he)))
    (fun he => hneuw (R.injOn hu.1.1 hw.1 (congrArg Fin.val he)))
    (R.old_edge_of_adj hu.1.1 hv.1 huo hvo huv)
    (R.old_edge_of_adj hv.1 hw.1 hvo hwo hadj)
    (R.old_edge_of_adj hu.1.1 hw.1 huo hwo huw)
  exact ⟨_,template_group_mem_expand X R.k (List.getElem_mem q.2),hug,hvg⟩

/-- Every graph-defined generating edge stays in a source group for every
realization, including the four-atom Q-block. -/
theorem VineRealization.intrinsic_edge_same_group (M : Molecule V D)
    (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b u v : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    (he : CoherenceEdge M S a b u v) : SameRealizedGroup R u v := by
  rcases he with ⟨hu,hv,hne,⟨T⟩⟩ | ⟨hu,hv⟩ | ⟨hu,w,hd,huv,huw⟩
  · exact R.double_same_group M hM hB hu.1 hv.1 hu.2.1 hu.2.2 hv.2.1 hv.2.2 hne T
  · exact R.undoubled_same_group M hB hu hv
  · exact R.undoubled_triangle_same_group M hM hB hu hd huv huw

end WaveTurbulence.Vine
