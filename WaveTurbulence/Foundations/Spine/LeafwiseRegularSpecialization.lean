/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularApp
/-! Verification that individual-leaf B2 recursions specialize to the pinned common-profile definitions. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.LeafApp
open Finset TTree

mutual
 theorem cplMstar_const {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path))
    (Q : RegCpl) (a b : Fin w × Path) :
    cplMstar (fun _ => F) Z Q a b = Q.Mstar F Z a b := by
  funext k
  cases Q <;> simp only [cplMstar, RegCpl.Mstar, cplMstar_const, chainNstar_const]

 theorem chainNstar_const {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path))
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    chainNstar (fun _ => F) Z X ζ a = X.Nstar F Z ζ a := by
  funext k
  cases X <;> simp only [chainNstar, RegChain.Nstar, cplMstar_const, chainNstar_const]
end

theorem couple_const {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (t s : ℝ) (k : Mom d) :
    couple δ r (fun _ => F) Q t s k = Q.app δ r F t s k := by
  simp only [couple, RegCpl.app, cplMstar_const]

theorem tree_const {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) : tree δ r (fun _ => F) X ζ t s k = X.app δ r F ζ t s k := by
  simp only [tree, RegChain.app, chainNstar_const]

end WaveTurbulence.LGSpine.LeafApp
