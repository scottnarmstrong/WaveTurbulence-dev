/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Unroll

/-! # P4-W2: the shape of an unrolled term (case analysis of `Lvl.terms`)

The glue identity (W2 (b)) is proved by induction over the levels.  `Lvl.mem_terms_succ` gives the three shapes of a member of
`Lvl.terms (m + 1) lv`: the native summand `psiBase` of the level (no operative member), the bottom bundle `psiBot` (the top operative
member has piece index `0`), or a product `term c (rA x) u · Ψ' (rB x) (u b, t₁, t₂) u` of a summand `c` of the bundle expansion of the top
operative member and a term `Ψ'` of the next level (`Lvl.terms m (lv.next ..)`).  `Lvl.terms_induction`: the resulting induction principle.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
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

theorem Lvl.mem_terms_zero (lv : Lvl B) (ψ : PsiT G d) :
    ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE 0 lv ↔ ψ = lv.psiBase B RD hG layer hLayer κ0 := by
  simp [Lvl.terms]

open Classical in
/-- **The three shapes of an unrolled term** (`pstar` is an operative member of maximal piece index). -/
theorem Lvl.mem_terms_succ (m : ℕ) (lv : Lvl B) (ψ : PsiT G d)
    (hψ : ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv) :
    ((¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j) ∧ ψ = lv.psiBase B RD hG layer hLayer κ0) ∨
      (∃ pstar : lv.ι, lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
        (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) ∧ (lv.e pstar).1.val = 0 ∧
        ψ = WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) ∨
      (∃ (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
        (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) ∧
        ∃ (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d),
          Ψ' ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer pstar hk) ∧
          ψ = fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
            Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u) := by
  by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
  · have hspec := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
    set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
    by_cases hk : 1 ≤ (lv.e ps).1.val
    · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
          (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
            fun c => (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)).map
              fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
        rw [Lvl.terms, dif_pos hop]; exact dif_pos hk
      rw [hT, Multiset.mem_bind] at hψ
      obtain ⟨c, -, hc⟩ := hψ
      obtain ⟨Ψ', hΨ', rfl⟩ := Multiset.mem_map.mp hc
      exact Or.inr (Or.inr ⟨ps, hk, hspec.1, hspec.2, c, Ψ', hΨ', rfl⟩)
    · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv =
          WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c ps ::ₘ 0 := by
        rw [Lvl.terms, dif_pos hop]; exact dif_neg hk
      rw [hT] at hψ
      exact Or.inr (Or.inl ⟨ps, hspec.1, hspec.2, by omega,
        (Multiset.mem_cons.mp hψ).resolve_right (Multiset.notMem_zero _)⟩)
  · have hT : Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
      rw [Lvl.terms]; exact dif_neg hop
    rw [hT] at hψ
    exact Or.inl ⟨hop, (Multiset.mem_cons.mp hψ).resolve_right (Multiset.notMem_zero _)⟩

/-- **Induction principle over the unrolled terms.**  A property of (level, term) holds for every unrolled term if it holds for the
native summand of a level without operative member, for the bottom bundle of a level whose top operative member has piece index `0`, and
is preserved by the product step at the top operative member. -/
theorem Lvl.terms_induction (Q : Lvl B → PsiT G d → Prop)
    (hbase : ∀ lv : Lvl B, Q lv (lv.psiBase B RD hG layer hLayer κ0))
    (hbot : ∀ (lv : Lvl B) (pstar : lv.ι), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
      (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) → (lv.e pstar).1.val = 0 →
      Q lv (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar))
    (hstep : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
      (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) →
      ∀ (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d), Q (lv.next B RD hG layer hLayer pstar hk) Ψ' →
        Q lv (fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
          Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u)) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv, Q lv ψ := by
  intro m
  induction m with
  | zero =>
    intro lv ψ hψ
    rw [(Lvl.mem_terms_zero B RD hG layer hLayer BE lv ψ).mp hψ]
    exact hbase lv
  | succ m ih =>
    intro lv ψ hψ
    rcases Lvl.mem_terms_succ B RD hG layer hLayer BE m lv ψ hψ with ⟨-, rfl⟩ | ⟨ps, hop, hmax, h0, rfl⟩ |
        ⟨ps, hk, hop, hmax, c, Ψ', hΨ', rfl⟩
    · exact hbase lv
    · exact hbot lv ps hop hmax h0
    · exact hstep lv ps hk hop hmax c Ψ' (ih _ Ψ' hΨ')

end WaveTurbulence.VineEstS5C.P4.W2
