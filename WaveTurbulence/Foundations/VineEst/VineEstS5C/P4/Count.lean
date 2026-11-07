/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound

/-! # P4: the per-vine term count (V5 Step 4d part C, WP-F)

`Lvl.card_terms_le_prod`: if the bundle expansion of the member `pstar` at every level has at most `wt (e pstar)` summands
(`wt` a weight function on the core indices, `wt ≥ 1`), then the unrolled multiset has at most `∏_{j ∈ members} wt (e j)` terms.
This is the TARGET count `4^b ∏ |Bs_i|` (one factor per operative vine, depending on the vine and not on the level).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- The members of the next level together with `pstar` form a subset of the members of the level. -/
theorem prod_next_mul_le (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i) :
    wt (lv.e pstar) * ∏ j : (lv.next B RD hG layer hLayer pstar hk).ι, wt ((lv.next B RD hG layer hLayer pstar hk).e j) ≤
      ∏ j : lv.ι, wt (lv.e j) := by
  classical
  change wt (lv.e pstar) * ∏ j : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val}, wt (lv.e j.1) ≤ _
  rw [← Finset.prod_subtype (Finset.univ.filter fun j : lv.ι => (lv.e j).1.val < (lv.e pstar).1.val) (by simp)
    (fun j => wt (lv.e j))]
  have hnot : pstar ∉ Finset.univ.filter fun j : lv.ι => (lv.e j).1.val < (lv.e pstar).1.val := by simp
  rw [← Finset.prod_insert (f := fun j => wt (lv.e j)) hnot]
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) fun i _ _ => hwt _

open Classical in
/-- **Counting the terms per vine**: at most `∏_{members} wt (e j)` terms, where `wt (e pstar)` bounds the number of summands of the bundle
expansion of the member `pstar` (at every level). -/
theorem Lvl.card_terms_le_prod (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ wt (lv.e pstar)) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m →
      Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv) ≤ ∏ j : lv.ι, wt (lv.e j) := by
  intro m
  induction m with
  | zero =>
    intro lv _
    simpa [Lvl.terms] using Finset.one_le_prod (s := (Finset.univ : Finset lv.ι)) (f := fun j => wt (lv.e j)) (fun j _ => hwt _)
  | succ m ih =>
    intro lv hc
    have h1 : ∀ f : PsiT G d, Multiset.card (f ::ₘ (0 : Multiset (PsiT G d))) ≤ ∏ j : lv.ι, wt (lv.e j) := fun f => by
      simpa using Finset.one_le_prod (s := (Finset.univ : Finset lv.ι)) (f := fun j => wt (lv.e j)) (fun j _ => hwt _)
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
            ≤ wt (lv.e ps) * ∏ j : (lv.next B RD hG layer hLayer ps hk).ι, wt ((lv.next B RD hG layer hLayer ps hk).e j) :=
              Nat.mul_le_mul (hCh lv ps hk) hih
          _ ≤ ∏ j : lv.ι, wt (lv.e j) := prod_next_mul_le B RD hG layer hLayer lv ps hk wt hwt
      · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
              (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) ::ₘ 0 := by
          rw [Lvl.terms, dif_pos hop]; exact dif_neg hk
        rw [hT]; exact h1 _
    · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
        rw [Lvl.terms]; exact dif_neg hop
      rw [hT]; exact h1 _

end WaveTurbulence.VineEstS5C.P4
