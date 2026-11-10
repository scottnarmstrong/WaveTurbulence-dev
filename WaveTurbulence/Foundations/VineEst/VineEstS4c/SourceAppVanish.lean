/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
import Mathlib.Tactic

/-!
# V5 Step 4c-AMEND (R35): endpoint vanishing of the source approximants

DRAFT world (the stack of `lg-spine-u`'s `SourceApp`; the proofs use only the bodies of
`RegCpl.JB`, `RegChain.JBchain`, `RegChain.JBtree`, `RegCpl.app`, `RegChain.app`, which are the same
as the frozen ones in `Frozen/Defs/RegCplJBRegChainJBchain.lean`, `RegCplApp.lean`, `RegChainApp.lean`).

For the root-layer endpoint `t = q` (TARGET L1913 (ii), repaired as in R35):
* nonempty positive chain: `∫_q^q = 0`, for the types of `SourceApp.couple` with `q = q'`, `q' < q`, `q < q'`;
* nontrivial type 1 with `q = q'` (for `s ≥ q`) and with `q < q'`;
* trees with a nonempty chain (slice), `q = q'` (for `s ≤ q`) and `q' < q`.

NOT vanishing (finding, see HANDOFF): type 1 with `q' < q` is *constant in `t`* (`SourceApp.couple` uses
`app … (q'+1) s`), and trivial couples/trees give `F`.
-/

@[expose] public section
set_option autoImplicit false

open Finset MeasureTheory

namespace WaveTurbulence.VineEstS4c.SrcVanish

open WaveTurbulence WaveTurbulence.LGSpine.SourceApp WaveTurbulence.Reg WaveTurbulence.Links

theorem JBchain_zero_of_not_nil (r lo : ℝ) (X : RegChain) (hX : X.isNil = false) (G : ℝ → ℝ) :
    X.JBchain r lo lo G = 0 := by
  cases X with
  | nil => simp [RegChain.isNil] at hX
  | pair m Qr Qg inner rest => simp [RegChain.JBchain]

theorem JBtree_zero_of_not_nil (r s : ℝ) (X : RegChain) (hX : X.isNil = false) (hs : s ≤ r) :
    X.JBtree r r s = 0 := by
  unfold RegChain.JBtree
  rw [max_eq_right hs]
  exact JBchain_zero_of_not_nil r r X hX _

theorem chainApp_eq_zero_of_JBtree {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) (h : X.JBtree r t s = 0) : X.app δ r F ζ t s k = 0 := by
  unfold RegChain.app
  split_ifs <;> simp [h]

section Couples

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)

/-- Type 2, `q' < q`, nonempty positive `q`-slice: the factor `∫_q^t` vanishes at `t = q`. -/
theorem couple_type2_lt_zero (Xp Xm : RegChain) (Qlp : RegCpl) (q q' : ℕ) (hq : q' < q)
    (hX : (chainSlice LG (0, []) q Xp).isNil = false) (s : ℝ) (k : Mom d) :
    couple δ F LG (.type2 Xp Xm Qlp) q q' (q : ℝ) s k = 0 := by
  have hne : q ≠ q' := by omega
  have hlt : q' < q := hq
  simp only [couple, hne, hlt, ite_false, ite_true]
  have h0 : (chainSlice LG (0, []) q Xp).app δ (q : ℝ) (F q) 1 (q : ℝ) (q : ℝ) k = 0 :=
    chainApp_eq_zero_of_JBtree _ _ _ _ _ _ _ _
      (JBtree_zero_of_not_nil _ _ _ hX le_rfl)
  rw [h0]; simp

end Couples

section Trees

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)

/-- Tree, `q' < q`, nonempty `q`-slice: the `q`-layer factor `∫_q^t` vanishes at `t = q`. -/
theorem tree_lt_zero (X : RegChain) (q q' : ℕ) (hq : q' < q)
    (hX : (chainSlice LG (0, []) q X).isNil = false) (s : ℝ) (k : Mom d) :
    tree δ F LG X q q' (q : ℝ) s k = 0 := by
  have hne : q ≠ q' := by omega
  simp only [tree, hne, ite_false]
  have h0 : (chainSlice LG (0, []) q X).app δ (q : ℝ) (F q) (LG.garden.sig 0) (q : ℝ) (q : ℝ) k = 0 :=
    chainApp_eq_zero_of_JBtree _ _ _ _ _ _ _ _ (JBtree_zero_of_not_nil _ _ _ hX le_rfl)
  rw [h0]; simp

end Trees

end WaveTurbulence.VineEstS4c.SrcVanish
