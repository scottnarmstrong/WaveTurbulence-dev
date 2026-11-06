/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondCounts
public import WaveTurbulenceVineParam.VineParamSpliceGeometry
import Mathlib.Tactic

/-! # Actual bond multiplicity of the inserted rung -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- The two fresh vertices share precisely the two individually marked
rung bonds; neither the rails nor any old bond contributes. -/
theorem new_rung_bonds : (graphMolecule G.newEnds).bondsBetween (.inr 0) (.inr 1)=2 := by
  have h := (DirectedBondModel.graphModel G.newEnds).bondsBetween_eq_count (.inr 0) (.inr 1)
  change (graphMolecule G.newEnds).bondsBetween (.inr 0) (.inr 1)=_ at h
  rw [h]
  calc
    _=(∑ e : SpliceEdge G.i G.j,
      if s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inr (0 : Fin 2),Sum.inr 1) then (1 : ℕ) else 0) :=
        (sum_boole _ _).symm
    _=2 := by
      change (∑ e : {e : β // e ≠ G.i ∧ e ≠ G.j} ⊕ Fin 6,
        if s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inr (0 : Fin 2),Sum.inr 1) then (1 : ℕ) else 0)=2
      rw [Fintype.sum_sum_type]
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
      cases hp : G.pattern
      all_goals simp [newEnds,rungSpliceEnds,hp,orientPair,RungPattern.signs,
        ]

/-- On an old atom pair avoiding both crossing occurrences, insertion
preserves the actual bond multiplicity, with the cap permutation applied. -/
theorem old_pair_bonds (u v : V)
    (hi : s((G.ends G.i).1,(G.ends G.i).2) ≠ s(u,v))
    (hj : s((G.ends G.j).1,(G.ends G.j).2) ≠ s(u,v)) :
    (graphMolecule G.newEnds).bondsBetween (.inl (G.σ u)) (.inl (G.σ v))=
      (graphMolecule G.ends).bondsBetween u v := by
  have hn := (DirectedBondModel.graphModel G.newEnds).bondsBetween_eq_count
    (.inl (G.σ u)) (.inl (G.σ v))
  have ho := (DirectedBondModel.graphModel G.ends).bondsBetween_eq_count u v
  change (graphMolecule G.newEnds).bondsBetween (.inl (G.σ u)) (.inl (G.σ v))=_ at hn
  change (graphMolecule G.ends).bondsBetween u v=_ at ho
  rw [hn,ho]
  have hns : (∑ e : SpliceEdge G.i G.j,
      if s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inl (G.σ u),Sum.inl (G.σ v)) then (1 : ℕ) else 0)=
      ((univ : Finset (SpliceEdge G.i G.j)).filter (fun e =>
        s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inl (G.σ u),Sum.inl (G.σ v)))).card := sum_boole _ _
  have hos : (∑ e : β,if s((G.ends e).1,(G.ends e).2)=s(u,v) then (1 : ℕ) else 0)=
      ((univ : Finset β).filter (fun e => s((G.ends e).1,(G.ends e).2)=s(u,v))).card := sum_boole _ _
  change ((univ : Finset (SpliceEdge G.i G.j)).filter (fun e =>
    s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inl (G.σ u),Sum.inl (G.σ v)))).card=
    ((univ : Finset β).filter (fun e => s((G.ends e).1,(G.ends e).2)=s(u,v))).card
  rw [← hns,← hos,sum_two_edge_rest G.i G.j G.distinct]
  simp only [ite_eq_right hi,ite_eq_right hj,add_zero]
  change (∑ e : {e : β // e ≠ G.i ∧ e ≠ G.j} ⊕ Fin 6,
    if s((G.newEnds e).1,(G.newEnds e).2)=s(Sum.inl (G.σ u),Sum.inl (G.σ v)) then (1 : ℕ) else 0)=_
  rw [Fintype.sum_sum_type]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases hp : G.pattern
  all_goals simp [newEnds,rungSpliceEnds,hp,orientPair,RungPattern.signs,
    Prod.ext_iff]

omit [Fintype V] in
/-- A crossing occurrence cannot join two atoms on the same cap side. -/
theorem crossing_ne_uniform_pair (e : β) (u v : V)
    (hc : ¬ ((G.ends e).1 ∈ G.cap ↔ (G.ends e).2 ∈ G.cap))
    (huv : u ∈ G.cap ↔ v ∈ G.cap) : s((G.ends e).1,(G.ends e).2) ≠ s(u,v) := by
  intro h
  rcases Sym2.eq_iff.mp h with h | h
  · apply hc
    simpa only [h.1,h.2] using huv
  · apply hc
    simpa only [h.1,h.2] using huv.symm

/-- Every old paired source slot lying on a uniform cap side retains its
actual bond count. In particular the VII junction remains single. -/
theorem old_pair_bonds_of_uniform (u v : V) (huv : u ∈ G.cap ↔ v ∈ G.cap) :
    (graphMolecule G.newEnds).bondsBetween (.inl (G.σ u)) (.inl (G.σ v))=
      (graphMolecule G.ends).bondsBetween u v := by
  have hi : ¬ ((G.ends G.i).1 ∈ G.cap ↔ (G.ends G.i).2 ∈ G.cap) := by
    rw [G.first]
    unfold orientPair
    split <;> simp [G.outer_p,G.inner_c]
  have hj : ¬ ((G.ends G.j).1 ∈ G.cap ↔ (G.ends G.j).2 ∈ G.cap) := by
    rw [G.second]
    unfold orientPair
    split <;> simp [G.outer_q,G.inner_d]
  exact G.old_pair_bonds u v (G.crossing_ne_uniform_pair G.i u v hi huv)
    (G.crossing_ne_uniform_pair G.j u v hj huv)

end WaveTurbulence.Vine.Param.RungSpliceGeometry
