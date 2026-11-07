/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat2

/-! # P4-W2 (session 12, step 1c): the leaf-child independence of a native term, and the bad-case clause of the native block kinds -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **Leaf-child independence of a term with the native row form** (`hind` of `TermCertW`): the native row form depends on `t` only through
`t 0` and the clock domain, whose `t 1`, `t 2` conditions are void at leaf lower children. -/
theorem hind_native (RD : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (base : Mom d)
    (ψ0 : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hNE : RowFormNE RD hG L γ δ F layer hLayer R base ψ0 Dm ∅ ∅ Xq)
    (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ ClDom R (fun v => layer (RD.coreBranch hG v).toNode) t u))
    (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (u : GBranch G.tree → ℝ) (hu : u a = t 0) :
    ψ0 (clExtendIndices R κ.1) t u = ψ0 (clExtendIndices R κ.1) t' u := by
  classical
  rw [hNE β' κ t u, hNE β' κ t' u]
  have hClD : ClDom R (fun v => layer (RD.coreBranch hG v).toNode) t u ↔
      ClDom R (fun v => layer (RD.coreBranch hG v).toNode) t' u := by
    unfold ClDom
    rw [← h0]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · rcases hp with h | h
      · exact ⟨fun h' h'' => absurd h'' h, fun h' h'' => absurd h'' h⟩
      · rw [h]
    · rcases hn with h | h
      · exact ⟨fun h' h'' => absurd h'' h, fun h' h'' => absurd h'' h⟩
      · rw [h]
  have hD : Dm t u ↔ Dm t' u := (hDm t u hu).trans (hClD.trans (hDm t' u (h0 ▸ hu)).symm)
  simp only [Finset.notMem_empty, if_false, ← h0]
  by_cases hd : Dm t u
  · rw [if_pos hd, if_pos (hD.mp hd)]
  · rw [if_neg hd, if_neg (fun h => hd (hD.mpr h))]

/-- **`BadClauseP` of the native engine datum** (block kinds `canonBadKind`, constraints `consX .. ∅ ∅`, native exponents): clauses (a), (b) are
definitional; clause (d) is the incoherent row supplied for the bad vines that are not `AClause` (the second disjunct of `HFreeAt`). -/
theorem badClauseP_native (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ)
    (hd : ∀ i : Fin n, (assemblyPieceAt B i).vineType.IsBad = true → ¬ AClause hM9 B RD hG layer i →
      ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
        1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v)) :
    BadClauseP (engDatum hM9 B hG W wN wDec (canonBadKind hM9 B RD hG layer)
      (consX hM9 B (fun v => layer (RD.coreBranch hG v).toNode) ∅ ∅)
      (rowCoupleG hM9 B RD hG layer hLayer) (rowTreeG hM9 B RD hG layer hLayer)) := by
  classical
  refine badClauseP_engDatum hM9 B hG W wN wDec _ _ _ _ ?_ ?_ ?_
  · intro i _ h0
    have hA : AClause hM9 B RD hG layer i := by
      by_contra hn
      have : canonBadKind hM9 B RD hG layer i = 3 := by unfold canonBadKind; rw [if_neg hn]
      rw [this] at h0
      exact absurd h0 (by decide)
    rw [consX_empty]
    exact hA
  · intro i _ h2
    rcases canonBadKind_cases hM9 B RD hG layer i with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
  · intro i hnor h3
    have hnA : ¬ AClause hM9 B RD hG layer i := by
      intro hA
      have : canonBadKind hM9 B RD hG layer i = 0 := by unfold canonBadKind; rw [if_pos hA]
      rw [this] at h3
      exact absurd h3 (by decide)
    have hbad : (assemblyPieceAt B i).vineType.IsBad = true := by
      have : (assemblyShape hM9 B).nor i = false := hnor
      simpa [assemblyShape, shapeFamily] using this
    obtain ⟨⟨i', j⟩, hi, hj⟩ := hd i hbad hnA
    have hi' : i' = i := hi
    subst hi'
    exact ⟨j, hj⟩

end WaveTurbulence.VineEstS5C.P4.W2
