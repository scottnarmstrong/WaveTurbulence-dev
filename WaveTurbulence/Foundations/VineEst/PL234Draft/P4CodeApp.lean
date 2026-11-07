/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Split

/-!
# The source approximations of labelled codes, and their factorization

For `q' < q`, SourceApp's couple and tree approximations only read the spine labels (`chainSlice_eq_sliceL`):

* `appC`, `appT`: the approximations of a labelled couple and tree; `sourceCouple_eq_appC`, `sourceTree_eq_appT`;
* `composeC (U, lsU) B` and the join `(appendChain U Z, lsU ++ q'…)`: a labelled code from its upper labelled chain
  and its bottom couple or chain;
* **`appC_compose`**, **`appT_join`**: `appC = Φ(U) · ψ(B)` and `appT = Φ(U) · χ(Z)`. `Φ` is the product of the
  upper slice terms, the same for couples and trees. `ψ`, `χ` are the bottom single-layer terms at `(q'+1, s)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem nil_app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (ζ : ℤˣ) (t s : ℝ) (k : Mom d) :
    RegChain.nil.app δ r F ζ t s k = 1 := by
  have hs : specialSets (RegChain.nil.treeLinks ζ) = {∅} := by
    simp [specialSets, chosenSet, RegChain.treeLinks, RegChain.linksAt, IsSpecialSet]
  simp [RegChain.app, RegChain.dominant, RegChain.size, zetaOfTrees, RegChain.plug, hs, specialWeight,
    RegChain.JBtree, RegChain.JBchain, RegChain.Nstar, TTree.branching]

section App

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) (q q' : ℕ) (t s : ℝ) (k : Mom d)

/-- The approximation of a labelled couple (`q' < q`). -/
noncomputable def appC : RegCpl → List ℕ → ℂ
  | .type2 Xp Xm Qlp, ls =>
    (∏ r ∈ Ioo q' q, (sliceL Xp ls r).app δ r (F r) 1 (r + 1) r k) *
      (sliceL Xp ls q).app δ q (F q) 1 t q k *
      (SourceApp.closeCouple (sliceL Xp ls q') Xm Qlp).app δ q' (F q') (q' + 1) s k
  | Q, _ => Q.app δ q' (F q') (q' + 1) s k

/-- The approximation of a labelled tree of sign `+` (`q' < q`). -/
noncomputable def appT (X : RegChain) (μ : List ℕ) : ℂ :=
  (∏ r ∈ Ioo q' q, (sliceL X μ r).app δ r (F r) 1 (r + 1) r k) *
    (sliceL X μ q).app δ q (F q) 1 t q k *
    (sliceL X μ q').app δ q' (F q') 1 (q' + 1) s k

/-- The upper factor, common to couples and trees. -/
noncomputable def upF (U : RegChain) (lsU : List ℕ) : ℂ :=
  (∏ r ∈ Ioo q' q, (sliceL U lsU r).app δ r (F r) 1 (r + 1) r k) * (sliceL U lsU q).app δ q (F q) 1 t q k

/-- The labels a couple reads off a layering. -/
def cplLabels (LG : LayeredGarden 2) : RegCpl → List ℕ
  | .type2 Xp _ _ => spineLabels LG ((0 : Fin 2), []) Xp
  | _ => []

theorem sourceCouple_eq_appC (hlt : q' < q) (LG : LayeredGarden 2) (Q : RegCpl) :
    SourceApp.couple δ F LG Q q q' t s k = appC δ F q q' t s k Q (cplLabels LG Q) := by
  unfold SourceApp.couple
  rw [ite_eq_right (Nat.ne_of_gt hlt)]
  cases Q with
  | triv => simp only [ite_eq_left hlt]; rfl
  | type1 c Q₁ Q₂ Q₃ => simp only [ite_eq_left hlt]; rfl
  | type2 Xp Xm Qlp =>
    simp only [ite_eq_left hlt, chainSlice_eq_sliceL]
    rfl

theorem sourceTree_eq_appT (hlt : q' < q) (LX : LayeredGarden 1) (X : RegChain) (hs : LX.garden.sig 0 = 1) :
    SourceApp.tree δ F LX X q q' t s k = appT δ F q q' t s k X (spineLabels LX ((0 : Fin 1), []) X) := by
  unfold SourceApp.tree
  rw [ite_eq_right (Nat.ne_of_gt hlt), hs]
  simp only [chainSlice_eq_sliceL]
  rfl

/-- A labelled couple from its upper labelled chain and its bottom couple. -/
def composeC (U : RegChain) (lsU : List ℕ) : RegCpl → RegCpl × List ℕ
  | .type2 Xr Xm Qlp => (.type2 (appendChain U Xr) Xm Qlp, lsU ++ List.replicate (topCount Xr) q')
  | B => if U.isNil then (B, []) else (.type2 U .nil B, lsU)

variable {q q'}

theorem upF_nil : upF δ F q q' t k .nil [] = 1 := by
  simp only [upF, sliceL, nil_app, Finset.prod_const_one, mul_one]

theorem isNil_iff {U : RegChain} : U.isNil = true ↔ U = .nil := by
  cases U <;> simp [RegChain.isNil]

/-- **The couple approximation factorizes.** -/
theorem appC_compose (hlt : q' < q) {U : RegChain} {lsU : List ℕ} {u : ℕ} (hL : LabOK (q' + 1) U lsU u)
    {B : RegCpl} (hB : B.wf = true) :
    appC δ F q q' t s k (composeC q' U lsU B).1 (composeC q' U lsU B).2 =
      upF δ F q q' t k U lsU * B.app δ q' (F q') (q' + 1) s k := by
  have hne : ∀ r ∈ Ioo q' q, r ≠ q' := fun r hr => Nat.ne_of_gt (Finset.mem_Ioo.1 hr).1
  cases B with
  | type2 Xr Xm Qlp =>
    show (∏ r ∈ Ioo q' q, (sliceL (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q') r).app δ r
        (F r) 1 (r + 1) r k) *
      (sliceL (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q') q).app δ q (F q) 1 t q k *
      (SourceApp.closeCouple (sliceL (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q') q') Xm Qlp).app
        δ q' (F q') (q' + 1) s k = _
    rw [Finset.prod_congr rfl fun r hr => by rw [sliceL_join r U lsU u Xr hL, ite_eq_right (hne r hr)],
      sliceL_join q U lsU u Xr hL, ite_eq_right (Nat.ne_of_gt hlt), sliceL_join q' U lsU u Xr hL,
      ite_eq_left rfl]
    have hc : SourceApp.closeCouple Xr Xm Qlp = .type2 Xr Xm Qlp := by
      unfold SourceApp.closeCouple
      have : (Xr.isNil && Xm.isNil) = false := by
        simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hB
        exact hB.2
      rw [this]
      rfl
    rw [hc]
    rfl
  | triv =>
    by_cases hU : U.isNil = true
    · have hU' := isNil_iff.1 hU
      subst hU'
      rw [show lsU = [] from hL]
      have hc : composeC q' RegChain.nil [] RegCpl.triv = (RegCpl.triv, []) := rfl
      rw [hc, upF_nil, one_mul]
      rfl
    · have hc : composeC q' U lsU RegCpl.triv = (RegCpl.type2 U .nil .triv, lsU) := by simp [composeC, hU]
      rw [hc]
      show _ * (SourceApp.closeCouple (sliceL U lsU q') .nil .triv).app δ q' (F q') (q' + 1) s k = _
      rw [sliceL_low q' le_rfl U lsU u hL]
      rfl
  | type1 c Q₁ Q₂ Q₃ =>
    by_cases hU : U.isNil = true
    · have hU' := isNil_iff.1 hU
      subst hU'
      rw [show lsU = [] from hL]
      have hc : composeC q' RegChain.nil [] (RegCpl.type1 c Q₁ Q₂ Q₃) = (RegCpl.type1 c Q₁ Q₂ Q₃, []) := rfl
      rw [hc, upF_nil, one_mul]
      rfl
    · have hc : composeC q' U lsU (RegCpl.type1 c Q₁ Q₂ Q₃) = (RegCpl.type2 U .nil (.type1 c Q₁ Q₂ Q₃), lsU) := by
        simp [composeC, hU]
      rw [hc]
      show _ * (SourceApp.closeCouple (sliceL U lsU q') .nil (.type1 c Q₁ Q₂ Q₃)).app δ q' (F q') (q' + 1) s k = _
      rw [sliceL_low q' le_rfl U lsU u hL]
      rfl

/-- **The tree approximation factorizes.** -/
theorem appT_join (hlt : q' < q) {U : RegChain} {lsU : List ℕ} {u : ℕ} (hL : LabOK (q' + 1) U lsU u)
    (Z : RegChain) :
    appT δ F q q' t s k (appendChain U Z) (lsU ++ List.replicate (topCount Z) q') =
      upF δ F q q' t k U lsU * Z.app δ q' (F q') 1 (q' + 1) s k := by
  have hne : ∀ r ∈ Ioo q' q, r ≠ q' := fun r hr => Nat.ne_of_gt (Finset.mem_Ioo.1 hr).1
  unfold appT upF
  rw [Finset.prod_congr rfl fun r hr => by rw [sliceL_join r U lsU u Z hL, ite_eq_right (hne r hr)],
    sliceL_join q U lsU u Z hL, ite_eq_right (Nat.ne_of_gt hlt), sliceL_join q' U lsU u Z hL, ite_eq_left rfl]

end App

end WaveTurbulence.PL234
