/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Count
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Unroll
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Count
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Unroll` (sha256 8eeb2fccb82de3bc…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # BOT-DECOMP: the shape of an unrolled term, the class-sum identity and the recentered bound with the bottom bundle expanded

`Lvl.mem_termsB_succ`, `Lvl.termsB_induction` (mirror of W2's `Lvl.mem_terms_succ`, `Lvl.terms_induction`: the bottom shape is now `BX.term c`),
`clsFn_eq_sum_termsB_ext`, `unrolled_boundR_extB`, `unrolled_boundR_extB_prod` (mirror of P4's `clsFn_eq_sum_terms_ext`, `unrolled_boundR_ext`, `unrolled_boundR_ext_prod`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

theorem LvlΓ.mem_termsB_zeroΓ (lv : LvlΓ B) (ψ : PsiT G d) :
    ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX 0 lv ↔ ψ = lv.psiBase B RD hG layer hLayer κ0 := by
  simp [LvlΓ.termsBΓ]

open Classical in
/-- **The three shapes of an unrolled term, bottom bundle expanded** (`pstar` is an operative member of maximal piece index). -/
theorem LvlΓ.mem_termsB_succΓ (m : ℕ) (lv : LvlΓ B) (ψ : PsiT G d)
    (hψ : ψ ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv) :
    ((¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j) ∧ ψ = lv.psiBase B RD hG layer hLayer κ0) ∨
      (∃ (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
        (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
        (c : (BX lv pstar h0 hop hmax).Ch), ψ = fun x t u => (BX lv pstar h0 hop hmax).term c x t u) ∨
      (∃ (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
        (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) ∧
        ∃ (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d),
          Ψ' ∈ LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer pstar hk) ∧
          ψ = fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
            Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u) := by
  by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
  · have hspec := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
    set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
    by_cases hk : 1 ≤ (lv.e ps).1.val
    · have hT : LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
          (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
            fun c => (LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk)).map
              fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
        rw [LvlΓ.termsBΓ, dif_pos hop]; exact dif_pos hk
      rw [hT, Multiset.mem_bind] at hψ
      obtain ⟨c, -, hc⟩ := hψ
      obtain ⟨Ψ', hΨ', rfl⟩ := Multiset.mem_map.mp hc
      exact Or.inr (Or.inr ⟨ps, hk, hspec.1, hspec.2, c, Ψ', hΨ', rfl⟩)
    · have hT : LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
          (Finset.univ : Finset (BX lv ps (by omega) hspec.1 hspec.2).Ch).val.map
            fun c => (BX lv ps (by omega) hspec.1 hspec.2).term c := by
        rw [LvlΓ.termsBΓ, dif_pos hop]; exact dif_neg hk
      rw [hT, Multiset.mem_map] at hψ
      obtain ⟨c, -, rfl⟩ := hψ
      exact Or.inr (Or.inl ⟨ps, by omega, hspec.1, hspec.2, c, rfl⟩)
  · have hT : LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
      rw [LvlΓ.termsBΓ]; exact dif_neg hop
    rw [hT] at hψ
    exact Or.inl ⟨hop, (Multiset.mem_cons.mp hψ).resolve_right (Multiset.notMem_zero _)⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
