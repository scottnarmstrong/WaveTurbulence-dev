/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Construct3

/-! # Structural factorization of the literal source leaf products

The input factors are read at the first (positive) endpoint of each actual
code leaf pair, in the constructed source decoration.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- Original leaf-pair product at arbitrary source root addresses. -/
def cplLeafProduct (F : V → ℂ) (θ : Fin w × Path → V × V)
    (Q : RegCpl) (a b : Fin w × Path) (r : V) : ℂ :=
  ((Q.pairsAt a b).map (fun p => F (cplVal θ Q a b r p.1))).prod

/-- The first endpoint of an actual pair belongs to the region of its code. -/
theorem cpl_pair_fst_under (Q : RegCpl) (a b : Fin w × Path)
    (p : (Fin w × Path) × (Fin w × Path)) (hp : p ∈ Q.pairsAt a b) :
    Under a p.1 ∨ Under b p.1 :=
  cpl_endpoints_under Q a b p.1 (Finset.mem_union_right _
    ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩))

theorem cplLeafProduct_triv (F : V → ℂ) (θ : Fin w × Path → V × V)
    (a b : Fin w × Path) (r : V) : cplLeafProduct F θ .triv a b r = F r := by
  simp only [cplLeafProduct,RegCpl.pairsAt,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    cplVal]
  simp

/-- The type1 source leaf kernel factors into its three actual child
kernels at the original child momenta (r+x,r+x-y,r-y). -/
theorem cplLeafProduct_type1 (F : V → ℂ) (θ : Fin w × Path → V × V)
    (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) (a b : Fin w × Path) (r : V) (hab : Indep a b) :
    cplLeafProduct F θ (.type1 c Q₁ Q₂ Q₃) a b r =
      cplLeafProduct F θ Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r (θ a) 0) *
      cplLeafProduct F θ Q₂ (addrExt b [1]) (addrExt a [1]) (childVals r (θ a) 1) *
      cplLeafProduct F θ Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r (θ a) 2) := by
  have h₁ : (Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0])).map
      (fun p => F (cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r p.1)) =
      (Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0])).map
        (fun p => F (cplVal θ Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r (θ a) 0) p.1)) := by
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    exact (type1_dispatch θ c Q₁ Q₂ Q₃ a b r hab p.1).1 (cpl_pair_fst_under Q₁ _ _ p hp)
  have h₂ : (Q₂.pairsAt (addrExt b [1]) (addrExt a [1])).map
      (fun p => F (cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r p.1)) =
      (Q₂.pairsAt (addrExt b [1]) (addrExt a [1])).map
        (fun p => F (cplVal θ Q₂ (addrExt b [1]) (addrExt a [1]) (childVals r (θ a) 1) p.1)) := by
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    exact (type1_dispatch θ c Q₁ Q₂ Q₃ a b r hab p.1).2.1 (cpl_pair_fst_under Q₂ _ _ p hp)
  have h₃ : (Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2])).map
      (fun p => F (cplVal θ (.type1 c Q₁ Q₂ Q₃) a b r p.1)) =
      (Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2])).map
        (fun p => F (cplVal θ Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r (θ a) 2) p.1)) := by
    apply List.map_congr_left
    intro p hp
    apply congrArg F
    exact (type1_dispatch θ c Q₁ Q₂ Q₃ a b r hab p.1).2.2 (cpl_pair_fst_under Q₃ _ _ p hp)
  simp only [cplLeafProduct,RegCpl.pairsAt,List.map_append,List.prod_append,h₁,h₂,h₃]

end WaveTurbulence.RegAsymp
