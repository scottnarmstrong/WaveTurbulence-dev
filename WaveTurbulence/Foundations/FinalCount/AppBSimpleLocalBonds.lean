/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # Simple local incidence tables exclude lost selected ladder links -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Vertex injectivity transports simplicity of the transcribed edge list
to the actual molecule's removed bond endpoints. -/
theorem endpoints_injective_of_table
    (hP : Function.Injective (fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2))) :
    Function.Injective (fun i => M.ends (r.edge i).val) := by
  have ha (i : Fin P.edges.length) : P.edges[i].1 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hb (i : Fin P.edges.length) : P.edges[i].2 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  intro i j he
  change M.ends (r.edge i).val = M.ends (r.edge j).val at he
  rw [r.endpoints i,r.endpoints j] at he
  apply hP
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp he with h | h
  · exact Or.inl ⟨r.vertex_injective (ha i) (ha j) h.1,r.vertex_injective (hb i) (hb j) h.2⟩
  · exact Or.inr ⟨r.vertex_injective (ha i) (hb j) h.1,r.vertex_injective (hb i) (ha j) h.2⟩

/-- A simple removed incidence table gives at most one actual bond from
any deleted atom to any neighbour, including ambient neighbours. -/
theorem bondsBetween_le_one_of_table
    (hP : Function.Injective (fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2)))
    {a : V} (ha : a ∈ r.removedAtoms) (b : V) : M.bondsBetween a b ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  have hrem (z : D) (hz : z ∈ M.bonds) (he : M.ends z = s(a,b)) :
      z ∈ appbRemovedBonds M r.removedAtoms := by
    apply mem_filter.mpr
    refine ⟨hz,?_⟩
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl (h.1.symm ▸ ha)
    · exact Or.inr (h.2.symm ▸ ha)
  let ix := r.edge.symm ⟨x,hrem x hx'.1 hx'.2⟩
  let iy := r.edge.symm ⟨y,hrem y hy'.1 hy'.2⟩
  have hix : (r.edge ix).val = x := congrArg Subtype.val (r.edge.apply_symm_apply _)
  have hiy : (r.edge iy).val = y := congrArg Subtype.val (r.edge.apply_symm_apply _)
  have he : ix = iy := r.endpoints_injective_of_table hP (by
    change M.ends (r.edge ix).val = M.ends (r.edge iy).val
    rw [hix,hiy,hx'.2,hy'.2])
  exact hix.symm.trans ((congrArg (fun i => (r.edge i).val) he).trans hiy)

/-- No selected source link is lost by deleting a simple local group. -/
theorem linkProduct_eq_of_simple_table
    (hP : Function.Injective (fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2)))
    (L γ δ : ℝ) (scales : Finset V → ℝ) :
    appbLinkProduct r.post L γ δ scales = appbLinkProduct M L γ δ scales := by
  change appbLinkProduct (Degen.eraseAtoms M r.removedAtoms) L γ δ scales = _
  unfold appbLinkProduct
  rw [appbLinks_eraseAtoms_no_double_partner M r.removedAtoms]
  intro a ha b hb hne
  have hh := r.bondsBetween_le_one_of_table hP ha b
  omega

end AppbRealization
end WaveTurbulence.Mole
