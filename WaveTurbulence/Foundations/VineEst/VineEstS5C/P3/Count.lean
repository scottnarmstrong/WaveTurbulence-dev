/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Unroll

/-! # P3: the number of product terms (V5 Step 4d part C)

`Lvl.card_terms_le`: if every bundle expansion has at most `N ≥ 1` summands, the unrolled multiset has at most `N ^ #members` terms
(`#members` = number of core vines of the level; TARGET: `4^b ∏ |Bs_i|`, one factor per operative vine).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical in
/-- **Counting the terms**: at most `N ^ #members` (`N ≥ 1` bounds every bundle expansion). -/
theorem Lvl.card_terms_le (N : ℕ) (hN : 1 ≤ N)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ N) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m →
      Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv) ≤ N ^ Fintype.card lv.ι := by
  intro m
  induction m with
  | zero => intro lv _; simpa [Lvl.terms] using Nat.one_le_pow (Fintype.card lv.ι) N hN
  | succ m ih =>
    intro lv hc
    have h1 : ∀ f : PsiT G d, Multiset.card (f ::ₘ (0 : Multiset (PsiT G d))) ≤ N ^ Fintype.card lv.ι := fun f => by
      simpa using Nat.one_le_pow (Fintype.card lv.ι) N hN
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · by_cases hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop))).1.val)
      · set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
        have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
            (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
              fun c => (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)).map
                fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                  Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
          rw [Lvl.terms, dif_pos hop]; exact dif_pos hk
        have hlt := Lvl.card_next_lt B RD hG layer hLayer lv ps hk
        have hih := ih (lv.next B RD hG layer hLayer ps hk) (by omega)
        rw [hT, Multiset.card_bind]
        simp only [Multiset.card_map, Function.comp]
        rw [Multiset.map_const', Multiset.sum_replicate]
        simp only [Finset.card_val, Finset.card_univ, smul_eq_mul]
        calc Fintype.card (BE lv ps hk).Ch * Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk))
            ≤ N * N ^ Fintype.card (lv.next B RD hG layer hLayer ps hk).ι := Nat.mul_le_mul (hCh lv ps hk) hih
          _ = N ^ (Fintype.card (lv.next B RD hG layer hLayer ps hk).ι + 1) := by ring
          _ ≤ N ^ Fintype.card lv.ι := Nat.pow_le_pow_right hN hlt
      · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
              (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) ::ₘ 0 := by
          rw [Lvl.terms, dif_pos hop]; exact dif_neg hk
        rw [hT]; exact h1 _
    · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
        rw [Lvl.terms]; exact dif_neg hop
      rw [hT]; exact h1 _

end WaveTurbulence.VineEstS5C.P3
