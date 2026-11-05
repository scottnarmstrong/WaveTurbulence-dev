/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeAddressParameters
public import WaveTurbulence.Foundations.RegAsymp.TreeOrderedSingular

/-! # The original tree singular integral equals its actual chosen-address fold -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links ApproxNT Function Finset IncohInst Incoh

/-- Original tree link coordinates and original chosen addresses carry identical operators. -/
theorem tree_addressAppAlong_map_chosen {d : ℕ} (X : RegChain) (ζ : ℤˣ)
    (Z : Finset (Fin 1 × TTree.Path)) (L : List (Fin (X.treeLinks ζ).length))
    (H : (Fin 1 × TTree.Path → Mom d × Mom d) → ℂ)
    (x y : Fin (X.treeLinks ζ).length → Mom d) :
    addressAppAlong Z (L.map (treeChosen X ζ)) H (treeParamFun X ζ (fun i => (x i,y i))) =
      appAlong (univ.filter (fun j => treeChosen X ζ j ∈ Z)) L
        (fun x y => H (treeParamFun X ζ (fun i => (x i,y i)))) x y := by
  classical
  induction L generalizing x y with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons,addressAppAlong,addressAppStep,appAlong,appStep,
      mem_filter,mem_univ,true_and]
    have hfun : (fun a b => addressAppAlong Z (L.map (treeChosen X ζ)) H
        (update (treeParamFun X ζ (fun i => (x i,y i))) (treeChosen X ζ j) (a,b))) =
        (fun a b => appAlong (univ.filter (fun j => treeChosen X ζ j ∈ Z)) L
          (fun x y => H (treeParamFun X ζ (fun i => (x i,y i)))) (update x j a) (update y j b)) := by
      funext a b
      rw [← treeParamFun_update,← pairArray_update]
      exact ih _ _
    rw [hfun]

/-- The literal original source singular integral is its ordered address fold, at every
order, including the empty tree. This is an identity of the actual operator order. -/
theorem tree_addressAppAlong_source_eq_singInt {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (F : Mom d → ℂ) (Z : Finset (Fin 1 × TTree.Path)) (k : Mom d) :
    addressAppAlong Z ((X.treeLinks (G.sig 0)).map Prod.fst)
      (fun θ => chainLeafProduct F θ X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k)) 0 =
      singInt (univ.filter (fun j => treeChosen X (G.sig 0) j ∈ Z)) (fun x y =>
        (treeCarrier hX).sourceLeafWeight (fun _ => F) k (fun j i => if i=0 then x j else y j)) := by
  have he := tree_addressAppAlong_map_chosen X (G.sig 0) Z (List.finRange _)
    (fun θ => chainLeafProduct F θ X (G.sig 0) ((0:Fin 1),[]) k (fun _ => k))
    (0:Fin (X.treeLinks (G.sig 0)).length → Mom d) (0:Fin (X.treeLinks (G.sig 0)).length → Mom d)
  have hz : treeParamFun X (G.sig 0) (fun _ : Fin (X.treeLinks (G.sig 0)).length =>
      ((0:Mom d),(0:Mom d))) = 0 := treeParamFun_zero X (G.sig 0)
  rw [tree_map_finRange_chosen] at he
  simp only [Pi.zero_apply] at he
  rw [hz] at he
  have hkernel : (fun (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d) =>
      chainLeafProduct F (treeParamFun X (G.sig 0) (fun i => (x i,y i))) X (G.sig 0)
        ((0:Fin 1),[]) k (fun _ => k)) =
      (fun x y => (treeCarrier hX).sourceLeafWeight (fun _ => F) k
        (fun j i => if i=0 then x j else y j)) := by
    funext x y
    have hh := tree_prod_source_input_eq_chainLeafProduct hX F k
      (fun j i => if i=0 then x j else y j)
    simpa only [MomentumTreeData.sourceLeafWeight,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false] using hh.symm
  rw [hkernel] at he
  exact he.trans (tree_appAlong_finRange_eq_singInt _ _)

end WaveTurbulence.RegAsymp
