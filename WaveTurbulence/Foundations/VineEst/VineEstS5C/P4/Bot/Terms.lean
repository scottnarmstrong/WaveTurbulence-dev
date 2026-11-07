/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Exp

/-! # BOT-DECOMP: the term multiset that expands `psiBot` (F-W2-BOT)

`BotExp`: the expansion of the bottom bundle `psiBot` of a level (top operative member of piece index `0`) into finitely many summands, valid on the window `Win`.
`BotExpFam`: one for every such level and member.  `Lvl.termsB BE BX m lv`: the multiset of `Lvl.terms` with the bottom bundle expanded (an operative level whose top
operative member has piece index `0` contributes the summands `BX.term c`, `c ∈ Ch`, instead of the single term `psiBot`).
`Lvl.psiFuel_eq_termsB_ext`: the unrolled identity under the exterior window of the top level (design R of P4), `Lvl.mem_termsB_succ`, `Lvl.termsB_induction`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

/-- The expansion of the bottom bundle `psiBot` of a level at the member `pstar` into finitely many summands, valid on the window `Win`. -/
structure BotExp (κ0 : KPar d) (lv : Lvl B) (pstar : lv.ι) where
  Ch : Type
  [fin : Fintype Ch]
  term : Ch → (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ
  Win : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → Prop
  eq : ∀ x t u, Win x u →
    psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar x t u = ∑ c, term c x t u

attribute [instance] BotExp.fin

variable (p kind) in
/-- A family of bottom expansions, one for every level and every top operative member of piece index `0`. -/
abbrev BotExpFam (κ0 : KPar d) : Type 1 :=
  ∀ (lv : Lvl B) (pstar : lv.ι), (lv.e pstar).1.val = 0 → lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) →
    BotExp (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

open Classical in
/-- The multiset of product terms of `Lvl.psiFuel`, with the bottom bundle expanded. -/
noncomputable def Lvl.termsB : ℕ → Lvl B → Multiset (PsiT G d)
  | 0, lv => lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0
  | m + 1, lv =>
    if h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j then
      if hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))).1.val) then
        (Finset.univ : Finset (BE lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).Ch).val.bind
          fun c => (Lvl.termsB m (lv.next B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk)).map
            fun Ψ' x t u =>
              (BE lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).term c
                  (rA (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RS x) u *
                Ψ' (rB (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).RT x)
                  ![u (lv.split B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk).sb.b, t 1, t 2] u
      else
        (Finset.univ : Finset (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) (by omega)
          (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)).1
          (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)).2).Ch).val.map
          fun c => (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) (by omega)
            (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)).1
            (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)).2).term c
    else lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0

/-- The windows of the bottom expansions hold under the exterior window of their level. -/
def WinOfExtBot : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
    ExtOf B RD hG layer hLayer lv u → (BX lv pstar h0 hop hmax).Win x u

open Classical in
/-- **The unrolled identity with the bottom bundle expanded** (design R: under the exterior window of the top level only). -/
theorem Lvl.psiFuel_eq_termsB_ext (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX) :
    ∀ (m : ℕ) (lv : Lvl B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    ExtOf B RD hG layer hLayer lv u →
    Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
      ((Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv).map fun ψ => ψ x t u).sum := by
  intro m
  induction m with
  | zero => intro lv x t u _; simp [Lvl.psiFuel, Lvl.termsB]
  | succ m ih =>
    intro lv x t u hu
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · by_cases hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop))).1.val)
      · set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
        have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv ps hk hprime
              (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer ps hk)) := by
          rw [Lvl.psiFuel, dif_pos hop]; exact dif_pos hk
        have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
            (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
              fun c => (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk)).map
                fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                  Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
          rw [Lvl.termsB, dif_pos hop]; exact dif_pos hk
        have hR : ((Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv).map fun ψ => ψ x t u).sum =
            (∑ c, (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u) *
              ((Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk)).map fun Ψ' =>
                Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u).sum := by
          rw [hT, Finset.sum_mul, Multiset.map_bind, Multiset.sum_bind]
          simp only [Multiset.map_map, Function.comp]
          rw [Finset.sum_eq_multiset_sum]
          refine congrArg _ (Multiset.map_congr rfl fun c _ => ?_)
          exact Multiset.sum_map_mul_left
        have heq := (BE lv ps hk).eq (rA (lv.split B RD hG layer hLayer ps hk).RS x) u
          (hW lv ps hk (rA (lv.split B RD hG layer hLayer ps hk).RS x) u hu)
        rw [hR, hF]
        simp only [Lvl.psiStep, psiStepSp]
        by_cases h0 : psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer ps hk) hprime
            (rA (lv.split B RD hG layer hLayer ps hk).RS x) u = 0
        · have h0' : ∑ c, (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u = 0 := heq.symm.trans h0
          rw [h0, h0', zero_mul, zero_mul]
        · exact congrArg₂ (· * ·) heq (ih _ _ _ _ (ext_next B RD hG layer hLayer κ0 hprime lv ps hk _ u hu h0))
      · have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
              (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) := by
          rw [Lvl.psiFuel, dif_pos hop]; exact dif_neg hk
        have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
            (Finset.univ : Finset (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) (by omega)
              (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).1
              (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).2).Ch).val.map
              fun c => (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) (by omega)
                (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).1
                (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).2).term c := by
          rw [Lvl.termsB, dif_pos hop]; exact dif_neg hk
        refine (congrFun (congrFun (congrFun hF x) t) u).trans ?_
        rw [hT]
        have heq := (BX lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)) (by omega)
          (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).1
          (Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)).2).eq x t u
          (hWB lv _ (by omega) _ _ x u hu)
        refine heq.trans ?_
        rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
        rfl
    · have hF : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 := by
        rw [Lvl.psiFuel]; exact dif_neg hop
      have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
        rw [Lvl.termsB]; exact dif_neg hop
      rw [hF, hT]
      exact (by simp : ∀ f : PsiT G d, f x t u = (Multiset.map (fun ψ => ψ x t u) (f ::ₘ 0)).sum) _

end WaveTurbulence.VineEstS5C.P4.Bot
