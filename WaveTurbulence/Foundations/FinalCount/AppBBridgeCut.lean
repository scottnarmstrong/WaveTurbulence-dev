/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
public import WaveTurbulence.Foundations.Spine.GardenLatticeCorrespondence
import Mathlib.Tactic

/-! # DH21 Lemma 9.14 applied to an actual Appendix B bridge

The single-boundary cut is constructed from the endpoint's actual residual
component. No cut or fixed-label conclusion is assumed as operation data.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Paths after literal bond erasure are precisely paths avoiding its two darts. -/
theorem appb_eraseBond_path_iff (M : Molecule V D) (e : D) :
    ∀ u v, (eraseBond M e).SameComponent u v ↔ Relation.EqvGen (Degen.AdjWithoutBond M e) u v := by
  intro u v
  constructor
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨x,hx,hy⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨x.val,hx,hy,x.property⟩
    | refl u => exact Relation.EqvGen.refl u
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨x,hx,hy,h1,h2⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨⟨x,h1,h2⟩,hx,hy⟩
    | refl u => exact Relation.EqvGen.refl u
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

noncomputable def appbBridgeSide (M : Molecule V D) (e : D) : Finset V := by
  classical
  exact M.atoms.filter fun v => (eraseBond M e).SameComponent (M.atom e) v

/-- The bridge's endpoint component has exactly one old crossing dart. -/
theorem appb_bridge_boundary (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e) :
    Degen.boundaryDarts M (appbBridgeSide M e) = {e} := by
  classical
  have hnot : ¬ (eraseBond M e).SameComponent (M.atom e) (M.atom (M.mate e)) :=
    fun h => hb ((appb_eraseBond_path_iff M e _ _).mp h)
  have ha : M.atom e ∈ appbBridgeSide M e :=
    mem_filter.mpr ⟨M.atom_mem e,Relation.EqvGen.refl _⟩
  have hbn : M.atom (M.mate e) ∉ appbBridgeSide M e :=
    fun h => hnot (mem_filter.mp h).2
  ext x
  simp only [Degen.boundaryDarts,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨hx,hy⟩
    by_cases he : x = e
    · exact he
    · have hm : x ≠ M.mate e := by
        intro h
        exact hbn (h ▸ hx)
      have hpath := (mem_filter.mp hx).2
      have hstep : (eraseBond M e).Adj (M.atom x) (M.atom (M.mate x)) :=
        ⟨⟨x,he,hm⟩,rfl,rfl⟩
      have hp := Relation.EqvGen.trans _ _ _ hpath (Relation.EqvGen.rel _ _ hstep)
      exact (hy (mem_filter.mpr ⟨M.atom_mem _,hp⟩)).elim
  · rintro rfl
    exact ⟨ha,hbn⟩

/-- The actual integer label of a bridge is fixed within every conservation
parameter fiber, uniformly in all other decoration choices. -/
theorem appb_bridge_label_unique (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {w : Mom d} {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ') :
    κ e = κ' e := by
  classical
  have hp := Degen.single_boundary_momentum_unique M hκ hκ' (appbBridgeSide M e)
    (by intro v hv; exact (mem_filter.mp hv).1) (appb_bridge_boundary M e hb)
  exact kvec_injective hL w hp

end WaveTurbulence.Mole
