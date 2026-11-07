/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcRec

/-! # P4-W2 (session 13, step 2b): leaf-child independence of a term with exceptional records

`hind_exc`: the generalisation of `hind_native` to `Pex, Bex` arbitrary.  The exceptional weights of the records (`xqOf`) do not depend on `t`
(they are functions of the decoration and the clocks only), so the only `t`-dependence of a term with the native-except row form is through `t 0` and the
domain `DomX`, whose `t 1`, `t 2` conditions are void at leaf lower children.  (This closes the `hind` gap: an exceptional factor never reads `t 1`, `t 2`.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem xqOf_indep (recs : List (ExcRec G d)) (p : SourcePair G) (t t' : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (x : GNode G.tree → (Fin d → ℤ)) : xqOf recs p t u x = xqOf recs p t' u x := rfl

theorem domX_leaf_congr (lay : GBranch G.tree → ℕ) (Bex : Finset (GBranch G.tree)) (t t' : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2) :
    DomX R lay Bex (t 0) (t 1) (t 2) u ↔ DomX R lay Bex (t' 0) (t' 1) (t' 2) u := by
  unfold DomX
  rw [← h0]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · rcases hp with h | h
    · exact ⟨fun h' h'' => absurd h'' h, fun h' h'' => absurd h'' h⟩
    · rw [h]
  · rcases hn with h | h
    · exact ⟨fun h' h'' => absurd h'' h, fun h' h'' => absurd h'' h⟩
    · rw [h]

theorem hind_exc (RD : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (base : Mom d)
    (ψ0 : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (recs : List (ExcRec G d))
    (hNE : RowFormNE RD hG L γ δ F layer hLayer R base ψ0 Dm (pexOf recs) (bexOf recs) (xqOf recs))
    (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) (bexOf recs) (t 0) (t 1) (t 2) u))
    (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (u : GBranch G.tree → ℝ) (hu : u a = t 0) :
    ψ0 (clExtendIndices R κ.1) t u = ψ0 (clExtendIndices R κ.1) t' u := by
  classical
  rw [hNE β' κ t u, hNE β' κ t' u]
  have hD : Dm t u ↔ Dm t' u :=
    (hDm t u hu).trans ((domX_leaf_congr (R := R) _ _ t t' u h0 hp hn).trans (hDm t' u (h0 ▸ hu)).symm)
  simp only [← h0]
  by_cases hd : Dm t u
  · rw [if_pos hd, if_pos (hD.mp hd)]
    rfl
  · rw [if_neg hd, if_neg (fun h => hd (hD.mpr h))]
    simp only [zero_mul, mul_zero]

end WaveTurbulence.VineEstS5C.P4.W2
