/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix2

/-! # P1 EXPORT: `bundle_decomp` (V5 Step 4d part C, WP-B steps 3-4)

The exact bundle `psiSB` of a level equals `bundleFrame * νA * (zpPieces + zpRem)`: the pieces (a)-(c) of TARGET L1925-L1951
(clause (d), the leading term, cancelled by `hreal`; the conjugation defects are `0` because the barred approximants are the
conjugate-swaps) plus the explicit remainder rows `remA`, `remB`.  Valid for `t₁ ∈ (L₄, L₄+1]`, `t₀ ∈ [L₂, L₂+1]`
(R35: the time window is a.e. what the vine's time domain gives).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P1
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

variable (p kind J) in
open Classical in
/-- The pieces (a)-(c) of TARGET L1925-L1951 for the approximants `Qf = zpQfam`, `Tf = zpTfam` (the barred approximants are
`cswap Qf`, `cconj Tf`), at `(t0, s1, t1, x, y)`. -/
noncomputable def zpPieces (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  pieceA1 (bsA p kind J A sp0 hA) (zpTfam κ A) (cswap (zpQfam κ A)) t0 s1 t1 x y -
    pieceA2 (bsB p kind J A sp0 hA) (zpQfam κ A) (cconj (zpTfam κ A)) t0 s1 t1 x y +
  (if t0 < t1 ∧ t0 < s1 then
    pieceKQ (bsA p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 s1 t1 x y +
      pieceTQ (bsA p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 s1 t1 x +
      pieceKT (bsB p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 s1 t1 x y +
      pieceTT (bsB p kind J A sp0 hA) (zpQfam κ A) (zpTfam κ A) t0 s1 t1 x else 0)

variable (p kind J) in
/-- The remainder rows: `∑_{bsA} remA - ∑_{bsB} remB` with the remainders `remQ`, `remT` (exact kernel minus approximant). -/
noncomputable def zpRem (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  ∑ b ∈ bsA p kind J A sp0 hA, remA (zpQfam κ A) (zpTfam κ A) (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) b t0 s1 t1 x y -
    ∑ b ∈ bsB p kind J A sp0 hA, remB (zpQfam κ A) (zpTfam κ A) (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) b t0 s1 t1 x y

open Classical in
/-- **P1 EXPORT.**  The exact bundle equals the frame times `νA` times the pieces (a)-(c) plus the remainder rows
(the leading term (d) is cancelled).  Hypotheses: `hZ : ZpSurj` (R51, owner ZP-SURJ), `hR : RealityAll` (R46, owner PL234),
`hL : ZpLayers` (layer numerals, see `ZpLayers`), and the time window. -/
theorem bundle_decomp (hR : RealityAll) (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (h1 : (zpQ4 A pstar : ℝ) < (bundleVars κ A sp0 x u).2.2.1)
    (h1' : (bundleVars κ A sp0 x u).2.2.1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ (bundleVars κ A sp0 x u).1)
    (h0' : (bundleVars κ A sp0 x u).1 ≤ zpQ2 A pstar + 1) :
    psiSB (p := p) (kind := kind) κ A sp0 hA x u = bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
      (zpPieces p kind J A sp0 hA κ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
          (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2 +
        zpRem p kind J A sp0 hA κ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
          (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2)) := by
  obtain ⟨τ, hbij, hrel⟩ := hZ.twin
  rw [bundle_eq_repl p kind J κ (zpQfam κ A) (zpTfam κ A) τ A sp0 hA hbij
    (fun G hG => ⟨(hrel G hG).1, (hrel G hG).2.1⟩) hZ.coherent x u]
  congr 2
  generalize bundleVars κ A sp0 x u = v at *
  obtain ⟨t0, s1, t1, x', y'⟩ := v
  simp only at h1 h1' h0 h0' ⊢
  have hd := replSum_decomp_ext (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA) zpLq zpLt (zpQ4 A pstar) zpTrQ zpTrT
    (zpEx κ A) (zpEt κ A) (zpQ0 κ A) (zpT0 κ A) (cswap (zpQfam κ A)) (cconj (zpTfam κ A))
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun b _ => b ∈ zpFinset p kind pstar J A sp0 hA ∧ zpQ4 A pstar < zpLq b)
    (fun b _ => b ∈ zpFinset p kind pstar J A sp0 hA ∧ zpQ4 A pstar < zpLt b)
    (fun b _ t s k ht => by simp [zpEx, not_lt.mpr ht])
    (fun b _ t s k ht => by simp [zpEt, not_lt.mpr ht])
    (fun b _ s k hb => zp_hQ0 A sp0 hA hZ hL κ hb.1 hb.2 s k)
    (fun b _ s k hb => zp_hT0 A sp0 hA hZ hL κ hb.1 hb.2 s k)
    (zp_hsub A sp0 hA)
    (fun b t s k => by simp [cswap, zpQfam])
    (fun b t s k => by simp [cconj, zpTfam])
    t0 s1 t1 x' y' h1'
    (fun _ b hb hgt _ => ⟨zp_mem_of_bs A sp0 hA (by unfold zpBsU; exact hb), hgt⟩)
    (fun _ b hb hgt _ => ⟨zp_mem_of_bs A sp0 hA (by unfold zpBsU; exact hb), hgt⟩)
    (fun hlt => zp_hreal A sp0 hA hR hZ hL κ x' h1 h1' h0 h0' hlt)
  unfold zpRem
  congr 1
  refine hd.trans ?_
  simp only [zpPieces, pieceDef, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  rfl
end
end WaveTurbulence.VineEstS5C.P1
