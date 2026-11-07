/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Linear

/-! # P3: unrolling `psiFuel` over the levels into a finite multiset of product terms (V5 Step 4d part C)

`BundleExp`: the expansion of the bundle `psiSB` of one level into a finite family of summands (the pieces (a)-(c) and the remainder rows of
`bundle_decomp`, indexed by a finite type `Ch`), valid on a window `Win`.  `Lvl.terms BE m lv`: the multiset of product terms of the recursion
`Lvl.psiFuel`: at an operative level every inner term is multiplied by every summand of the bundle (the same shape as `psiStepSp`); inert levels
and the base give one term (the native row).  `Lvl.winOf`: the conjunction of the windows of the levels.  `Lvl.psiFuel_eq_terms`: on the window,
`psiFuel = ∑ terms`.  `card_terms_le`: the number of terms is at most `N ^ #members`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P3
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The expansion of the bundle `psiSB` of a level at the member `pstar` into finitely many summands, valid on the window `Win`
(the time window of `bundle_decomp`; the summands are the pieces (a)-(c) and the remainder rows, indexed by `Ch`). -/
structure BundleExp (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) where
  Ch : Type
  [fin : Fintype Ch]
  term : Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ
  Win : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → Prop
  eq : ∀ x u, Win x u →
    psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u = ∑ c, term c x u

attribute [instance] BundleExp.fin

variable (p) in
/-- A family of bundle expansions, one for every level and member. -/
abbrev BundleExpFam (κ0 : KPar d) (hprime : IsPrimeGarden G) : Type 1 :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), BundleExp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical in
/-- The multiset of product terms of `Lvl.psiFuel` (same recursion). -/
noncomputable def Lvl.terms : ℕ → Lvl B → Multiset (PsiT G d)
  | 0, lv => lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0
  | m + 1, lv =>
    if h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j then
      if hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))).1.val) then
        (Finset.univ : Finset (BE lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).Ch).val.bind
          fun c => (Lvl.terms m (lv.next B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk)).map
            fun Ψ' x t u =>
              (BE lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).term c
                  (rA (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RS x) u *
                Ψ' (rB (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RT x)
                  ![u (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).sb.b, t 1, t 2] u
      else WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
        (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) ::ₘ 0
    else lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0

open Classical in
/-- The window on which the unrolled identity holds: the conjunction of the windows of the operative levels. -/
noncomputable def Lvl.winOf : ℕ → Lvl B → (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop
  | 0, _ => fun _ _ _ => True
  | m + 1, lv =>
    if h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j then
      if hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))).1.val) then
        fun x t u =>
          (BE lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).Win
              (rA (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RS x) u ∧
            Lvl.winOf m (lv.next B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk)
              (rB (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RT x)
              ![u (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).sb.b, t 1, t 2] u
      else fun _ _ _ => True
    else fun _ _ _ => True

open Classical in
/-- **The unrolled identity**: on the window, the recursive summand is the sum of its product terms. -/
theorem Lvl.psiFuel_eq_terms : ∀ (m : ℕ) (lv : Lvl B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE m lv x t u →
    Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
      ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv).map fun ψ => ψ x t u).sum := by
  intro m
  induction m with
  | zero => intro lv x t u _; simp [Lvl.psiFuel, Lvl.terms]
  | succ m ih =>
    intro lv x t u hw
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · by_cases hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop))).1.val)
      · set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
        have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv ps hk hprime
              (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer ps hk)) := by
          rw [Lvl.psiFuel, dif_pos hop]; exact dif_pos hk
        have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
            (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
              fun c => (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)).map
                fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                  Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
          rw [Lvl.terms, dif_pos hop]; exact dif_pos hk
        have hW : (BE lv ps hk).Win (rA (lv.split B RD hG layer hLayer ps hk).RS x) u ∧
            Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)
              (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
          have hWe : Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv = fun x t u =>
              (BE lv ps hk).Win (rA (lv.split B RD hG layer hLayer ps hk).RS x) u ∧
                Lvl.winOf (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)
                  (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
            rw [Lvl.winOf, dif_pos hop]; exact dif_pos hk
          rw [hWe] at hw; exact hw
        obtain ⟨h1, h2⟩ := hW
        rw [hF, hT]
        simp only [Lvl.psiStep, psiStepSp]
        refine (congrArg₂ (· * ·) ((BE lv ps hk).eq _ _ h1) (ih _ _ _ _ h2)).trans ?_
        rw [Finset.sum_mul]
        rw [Multiset.map_bind, Multiset.sum_bind]
        simp only [Multiset.map_map, Function.comp]
        rw [Finset.sum_eq_multiset_sum]
        refine congrArg _ (Multiset.map_congr rfl fun c _ => ?_)
        exact (Multiset.sum_map_mul_left).symm
      · have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
              (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) := by
          rw [Lvl.psiFuel, dif_pos hop]; exact dif_neg hk
        have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
              (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) ::ₘ 0 := by
          rw [Lvl.terms, dif_pos hop]; exact dif_neg hk
        refine (congrFun (congrFun (congrFun hF x) t) u).trans ?_
        rw [hT]
        exact (by simp : ∀ f : PsiT G d, f x t u = (Multiset.map (fun ψ => ψ x t u) (f ::ₘ 0)).sum) _
    · have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 := by
        rw [Lvl.psiFuel]; exact dif_neg hop
      have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
        rw [Lvl.terms]; exact dif_neg hop
      rw [hF, hT]
      exact (by simp : ∀ f : PsiT G d, f x t u = (Multiset.map (fun ψ => ψ x t u) (f ::ₘ 0)).sum) _

end WaveTurbulence.VineEstS5C.P3
