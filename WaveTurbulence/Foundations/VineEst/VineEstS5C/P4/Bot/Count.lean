/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Count

/-! # BOT-DECOMP: the per-vine term count with the bottom bundle expanded (mirror of `P4.Lvl.card_terms_le_prod`)

`Lvl.card_termsB_le_prod`: if the bundle expansion of the member `pstar` at every (non-bottom) level has at most `wt (e pstar)` summands, and the bottom expansion of
the member `pstar` has at most `wt (e pstar)` summands, then `Lvl.termsB` has at most `∏_{j ∈ members} wt (e j)` terms.  (This is where W3 sees the size of the
bottom member's bundle, which `P4.Lvl.card_terms_le_prod` counts as `1`.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Bot
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

open Classical in
/-- **Counting the terms per vine, bottom bundle expanded**. -/
theorem Lvl.card_termsB_le_prod (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ wt (lv.e pstar))
    (hChB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      Fintype.card (BX lv pstar h0 hop hmax).Ch ≤ wt (lv.e pstar)) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m →
      Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv) ≤ ∏ j : lv.ι, wt (lv.e j) := by
  intro m
  induction m with
  | zero =>
    intro lv _
    simpa [Lvl.termsB] using Finset.one_le_prod (s := (Finset.univ : Finset lv.ι)) (f := fun j => wt (lv.e j)) (fun j _ => hwt _)
  | succ m ih =>
    intro lv hc
    have h1 : ∀ f : PsiT G d, Multiset.card (f ::ₘ (0 : Multiset (PsiT G d))) ≤ ∏ j : lv.ι, wt (lv.e j) := fun f => by
      simpa using Finset.one_le_prod (s := (Finset.univ : Finset lv.ι)) (f := fun j => wt (lv.e j)) (fun j _ => hwt _)
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · by_cases hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop))).1.val)
      · set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
        have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
            (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
              fun c => (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk)).map
                fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                  Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
          rw [Lvl.termsB, dif_pos hop]; exact dif_pos hk
        have hlt := Lvl.card_next_lt B RD hG layer hLayer lv ps hk
        have hih := ih (lv.next B RD hG layer hLayer ps hk) (by omega)
        rw [hT, Multiset.card_bind]
        simp only [Multiset.card_map, Function.comp]
        rw [Multiset.map_const', Multiset.sum_replicate]
        simp only [Finset.card_val, Finset.card_univ, smul_eq_mul]
        calc Fintype.card (BE lv ps hk).Ch * Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk))
            ≤ wt (lv.e ps) * ∏ j : (lv.next B RD hG layer hLayer ps hk).ι, wt ((lv.next B RD hG layer hLayer ps hk).e j) :=
              Nat.mul_le_mul (hCh lv ps hk) hih
          _ ≤ ∏ j : lv.ι, wt (lv.e j) := prod_next_mul_le B RD hG layer hLayer lv ps hk wt hwt
      · have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
            (Finset.univ : Finset (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) (by omega)
              (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).1
              (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).2).Ch).val.map
              fun c => (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) (by omega)
                (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).1
                (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).2).term c := by
          rw [Lvl.termsB, dif_pos hop]; exact dif_neg hk
        rw [hT, Multiset.card_map]
        simp only [Finset.card_val, Finset.card_univ]
        refine (hChB lv _ (by omega) _ _).trans ?_
        exact Finset.single_le_prod' (f := fun j => wt (lv.e j)) (fun j _ => hwt _) (Finset.mem_univ _)
    · have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
        rw [Lvl.termsB]; exact dif_neg hop
      rw [hT]; exact h1 _

end WaveTurbulence.VineEstS5C.P4.Bot
