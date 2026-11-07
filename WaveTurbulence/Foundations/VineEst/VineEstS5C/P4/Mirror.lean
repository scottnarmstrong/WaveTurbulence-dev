/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Decomp

/-! # P4: the mirrored bundle decomposition (V5 Step 4d part C, TARGET L1904 "by symmetry")

`P1.bundle_decomp` needs `t₁ ∈ (L₄, L₄+1]`, i.e. the clock `t₁` of the node `u₄` lies in the LOWEST layer `L₄ = min (L_{u3}, L_{u4})`.
TARGET assumes `L_{u3} ≥ L_{u4}` "by symmetry".  The symmetry is complex conjugation: for conjugate-swapped barred approximants
`replSum Bs₁ Bs₂ (t₀, s₁, t₁, x, y) = - conj (replSum Bs₂ Bs₁ (t₀, t₁, s₁, y, x))` (`replSum_mirror`).  So when the clock `s₁` is in the lowest layer,
`bundle_decomp_mirror` gives the decomposition with the roles of `bsA`, `bsB` and of `(t₁, s₁)`, `(x, y)` exchanged.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1

/-- **Mirror symmetry of the pairing sum** for conjugate-swapped barred approximants. -/
theorem replSum_mirror {β : Type*} {d : ℕ} [DecidableEq β] (Bs₁ Bs₂ : Finset β) (Q T : β → ℝ → ℝ → Mom d → ℂ)
    (t0 s1 t1 : ℝ) (x y : Mom d) :
    replSum Bs₁ Bs₂ Q (cswap Q) T (cconj T) t0 s1 t1 x y =
      -(starRingEnd ℂ) (replSum Bs₂ Bs₁ Q (cswap Q) T (cconj T) t0 t1 s1 y x) := by
  unfold replSum cswap cconj
  by_cases h1 : t0 < t1 <;> by_cases h2 : t0 < s1 <;> simp [h1, h2, map_sum, map_mul]

/-- Membership in a union with the classical `DecidableEq` instance. -/
theorem mem_union_cl {β : Type*} {s t : Finset β} {b : β} :
    b ∈ @Union.union (Finset β) (@Finset.instUnion β fun a b => Classical.propDecidable (a = b)) s t ↔ b ∈ s ∨ b ∈ t :=
  @Finset.mem_union _ (fun a b => Classical.propDecidable (a = b)) _ _ _

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

variable (p kind J) in
open Classical in
/-- The pieces (a)-(c) of the mirrored decomposition: the pieces of `zpPieces` for `(bsB, bsA)` at `(t₀, t₁, s₁, y, x)` (before the conjugation and
the sign of `replSum_mirror`). -/
noncomputable def zpPiecesM (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  pieceA1 (bsB p kind J A sp0 hA) (zpTfam κ A) (cswap (zpQfam κ A)) t0 t1 s1 y x -
    pieceA2 (bsA p kind J A sp0 hA) (zpQfam κ A) (cconj (zpTfam κ A)) t0 t1 s1 y x +
  (if t0 < s1 ∧ t0 < t1 then
    pieceKQ (bsB p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 t1 s1 y x +
      pieceTQ (bsB p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 t1 s1 y +
      pieceKT (bsA p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 t1 s1 y x +
      pieceTT (bsA p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 t1 s1 y else 0)

variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

open Classical in
/-- **Mirrored bundle decomposition.**  If the clock `s₁` (instead of `t₁`) lies in the window `(L₄, L₄+1]`, then
`psiSB = bundleFrame * νA * (- conj (zpPiecesM) + zpRem)`. -/
theorem bundle_decomp_mirror (hR : RealityAll) (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (h1 : (zpQ4 A pstar : ℝ) < (bundleVars κ A sp0 x u).2.1)
    (h1' : (bundleVars κ A sp0 x u).2.1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ (bundleVars κ A sp0 x u).1)
    (h0' : (bundleVars κ A sp0 x u).1 ≤ zpQ2 A pstar + 1) :
    psiSB (p := p) (kind := kind) κ A sp0 hA x u = bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
      (-(starRingEnd ℂ) (zpPiecesM p kind J A sp0 hA κ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
          (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2) +
        zpRem p kind J A sp0 hA κ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
          (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2)) := by
  obtain ⟨τ, hbij, hrel⟩ := hZ.twin
  rw [bundle_eq_repl p kind J κ (zpQfam κ A) (zpTfam κ A) τ A sp0 hA hbij
    (fun G hG => ⟨(hrel G hG).1, (hrel G hG).2.1⟩) x u]
  congr 2
  generalize bundleVars κ A sp0 x u = v at *
  obtain ⟨t0, s1, t1, x', y'⟩ := v
  simp only at h1 h1' h0 h0' ⊢
  have hmemU : ∀ b, (b ∈ bsB p kind J A sp0 hA ∨ b ∈ bsA p kind J A sp0 hA) → b ∈ zpFinset p kind pstar J A sp0 hA := fun b hb =>
    zp_mem_of_bs A sp0 hA ((mem_zpBsU A sp0 hA).mpr hb.symm)
  have hd := replSum_decomp_ext (bsB p kind J A sp0 hA) (bsA p kind J A sp0 hA) zpLq zpLt (zpQ4 A pstar) zpTrQ zpTrT
    (zpEx κ A) (zpEt κ A) (zpQ0 κ A) (zpT0 κ A) (cswap (zpQfam κ A)) (cconj (zpTfam κ A))
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun b _ => b ∈ zpFinset p kind pstar J A sp0 hA ∧ zpQ4 A pstar < zpLq b)
    (fun b _ => b ∈ zpFinset p kind pstar J A sp0 hA ∧ zpQ4 A pstar < zpLt b)
    (fun b _ t s k ht => by simp [zpEx, not_lt.mpr ht])
    (fun b _ t s k ht => by simp [zpEt, not_lt.mpr ht])
    (fun b _ s k hb => zp_hQ0 A sp0 hA hZ hL κ hb.1 hb.2 s k)
    (fun b _ s k hb => zp_hT0 A sp0 hA hZ hL κ hb.1 hb.2 s k)
    (fun b hb hq ht => by
      have := zp_hsub A sp0 hA b ((mem_zpBsU A sp0 hA).mpr (mem_union_cl.mp hb).symm) hq ht
      exact ⟨this.2, this.1⟩)
    (fun b t s k => by simp [cswap, zpQfam])
    (fun b t s k => by simp [cconj, zpTfam])
    t0 t1 s1 y' x' h1'
    (fun _ b hb hgt _ => ⟨hmemU b (mem_union_cl.mp hb), hgt⟩)
    (fun _ b hb hgt _ => ⟨hmemU b (mem_union_cl.mp hb), hgt⟩)
    (fun hlt => by
      have hz := zp_hreal A sp0 hA hR hZ hL κ y' h1 h1' h0 h0' hlt
      convert hz using 4 <;> first | rfl | (ext b; rw [mem_zpBsU A sp0 hA]; simp [or_comm]))
  rw [replSum_mirror]
  unfold zpRem
  congr 2
  congr 1
  refine hd.trans ?_
  simp only [zpPiecesM, pieceDef, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  rfl

end
end WaveTurbulence.VineEstS5C.P4
