/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeShape
public import WaveTurbulence.Foundations.IncohInst.Links.Incoh1

/-! # Integer momentum rows supplied by the actual C2 couple decoration -/

public section
noncomputable section
open scoped BigOperators
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 2} {Q : RegCpl}

/-- The actual integer coefficients of the source C2 node expansion. -/
@[expose] def coupleNodeRow (hQ : Q.Decodes G) (a : GNode G.tree) : MomentumCoordinate Q.links.length → ℤ :=
  fun j => match j with
    | none => 1
    | some (i, b) => if b = 0 then (node_linear hQ a).choose i else (node_linear hQ a).choose_spec.choose i

/-- Row evaluation recovers the actual source decoration, in every coefficient group. -/
theorem coupleNodeRow_eval (hQ : Q.Decodes G) (a : GNode G.tree)
    {V : Type} [AddCommGroup V] (u : MomentumCoordinate Q.links.length → V) :
    momentumRowEval u (coupleNodeRow hQ a) =
      (decOfParams hQ (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).1 a := by
  rw [(node_linear hQ a).choose_spec.choose_spec]
  change (∑ j, coupleNodeRow hQ a j • u j) = _
  simp only [coupleNodeRow, Fintype.sum_option, one_smul, Fintype.sum_prod_type,
    Fin.sum_univ_two, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]

/-- Integer rows are determined by evaluation on the actual coordinate unit vectors. -/
theorem momentumRow_eq_of_eval {n : ℕ} {a b : MomentumCoordinate n → ℤ}
    (h : ∀ u : MomentumCoordinate n → ℤ, momentumRowEval u a = momentumRowEval u b) : a = b := by
  classical
  funext j
  have he := h (Pi.single j 1)
  simpa [momentumRowEval, Pi.single_apply, smul_eq_mul] using he

/-- The actual root node row is exactly the distinguished root coordinate. -/
theorem coupleNodeRow_root (hQ : Q.Decodes G) (i : Fin 2) :
    coupleNodeRow hQ (GNode.root G.tree i) = momentumUnitRow none := by
  apply momentumRow_eq_of_eval
  intro u
  rw [coupleNodeRow_eval, momentumRowEval_unit]
  exact (decOfParams hQ (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.2 i

/-- The source alternating parent relation holds as an exact integer row identity. -/
theorem coupleNodeRow_parent (hQ : Q.Decodes G) (b : GBranch G.tree) :
    coupleNodeRow hQ b.toNode = coupleNodeRow hQ (b.child 0) -
      coupleNodeRow hQ (b.child 1) + coupleNodeRow hQ (b.child 2) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_add, map_sub]
  simp only [coupleNodeRow_eval]
  exact (decOfParams hQ (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.1.1 b

/-- Paired source leaves have exactly the same integer momentum row. -/
theorem coupleNodeRow_pair (hQ : Q.Decodes G) (a : GLeaf G.tree) :
    coupleNodeRow hQ a.toNode = coupleNodeRow hQ (G.pair a).toNode := by
  apply momentumRow_eq_of_eval
  intro u
  simp only [coupleNodeRow_eval]
  exact (decOfParams hQ (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.1.2 a

/-- The chosen source link's first momentum difference is the first free coordinate. -/
theorem coupleNodeRow_link_x (hQ : Q.Decodes G) (hG : IsCouple G) (j : Fin Q.links.length) :
    coupleNodeRow hQ ((chosenBranch hQ j).child 0) - coupleNodeRow hQ (chosenBranch hQ j).toNode =
      momentumUnitRow (some (j, 0)) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_sub, coupleNodeRow_eval, coupleNodeRow_eval, momentumRowEval_unit]
  have he := congrArg (fun θ => (θ j).1) (decParams_decOfParams hQ hG (u none)
    (fun j => (u (some (j, 0)), u (some (j, 1)))))
  change xv (extend _) (chosenBranch hQ j).1 = _ at he
  rw [xv_extend] at he
  exact he

/-- The chosen source link's second momentum difference is the second free coordinate. -/
theorem coupleNodeRow_link_y (hQ : Q.Decodes G) (hG : IsCouple G) (j : Fin Q.links.length) :
    coupleNodeRow hQ (chosenBranch hQ j).toNode - coupleNodeRow hQ ((chosenBranch hQ j).child 2) =
      momentumUnitRow (some (j, 1)) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_sub, coupleNodeRow_eval, coupleNodeRow_eval, momentumRowEval_unit]
  have he := congrArg (fun θ => (θ j).2) (decParams_decOfParams hQ hG (u none)
    (fun j => (u (some (j, 0)), u (some (j, 1)))))
  change yv (extend _) (chosenBranch hQ j).1 = _ at he
  rw [yv_extend] at he
  exact he

end WaveTurbulence.IncohInst
