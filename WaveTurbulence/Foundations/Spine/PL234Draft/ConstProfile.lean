/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceTransport

/-!
# Leafwise leading terms with a constant profile are B2's leading terms

The spine's leafwise momentum factors (`LeafApp.cplMstar`, `LeafApp.chainNstar`) with the same profile `F`
at every leaf are B2's `RegCpl.Mstar F`, `RegChain.Nstar F` (`cplMstar_const`, `chainNstar_const`), so the
leafwise leading terms are B2's `app` (`LeafApp.couple_const`, `LeafApp.tree_const`).
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {d w : ℕ}

mutual
theorem cplMstar_const (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    (Q : RegCpl) → (a b : Fin w × Path) →
      LeafApp.cplMstar (fun _ => F) Z Q a b = Q.Mstar F Z a b
  | .triv, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    simp only [LeafApp.cplMstar, RegCpl.Mstar, cplMstar_const F Z Q₁, cplMstar_const F Z Q₂,
      cplMstar_const F Z Q₃]
  | .type2 Xp Xm Qlp, a, b => by
    simp only [LeafApp.cplMstar, RegCpl.Mstar, cplMstar_const F Z Qlp, chainNstar_const F Z Xp,
      chainNstar_const F Z Xm]
termination_by structural Q => Q

theorem chainNstar_const (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
      LeafApp.chainNstar (fun _ => F) Z X ζ a = X.Nstar F Z ζ a
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, a => by
    simp only [LeafApp.chainNstar, RegChain.Nstar, cplMstar_const F Z Qr, cplMstar_const F Z Qg,
      chainNstar_const F Z inner, chainNstar_const F Z rest]
termination_by structural X => X
end

theorem LeafApp.couple_const (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (t s : ℝ) (k : Mom d) :
    LeafApp.couple δ r (fun _ => F) Q t s k = Q.app δ r F t s k := by
  simp only [LeafApp.couple, RegCpl.app, cplMstar_const]

theorem LeafApp.tree_const (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (t s : ℝ) (k : Mom d) :
    LeafApp.tree δ r (fun _ => F) X ζ t s k = X.app δ r F ζ t s k := by
  simp only [LeafApp.tree, RegChain.app, chainNstar_const]

end WaveTurbulence.PL234
