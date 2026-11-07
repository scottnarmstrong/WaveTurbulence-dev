/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Count

/-! # BOT-DECOMP: the shape of an unrolled term, the class-sum identity and the recentered bound with the bottom bundle expanded

`Lvl.mem_termsB_succ`, `Lvl.termsB_induction` (mirror of W2's `Lvl.mem_terms_succ`, `Lvl.terms_induction`: the bottom shape is now `BX.term c`),
`clsFn_eq_sum_termsB_ext`, `unrolled_boundR_extB`, `unrolled_boundR_extB_prod` (mirror of P4's `clsFn_eq_sum_terms_ext`, `unrolled_boundR_ext`, `unrolled_boundR_ext_prod`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Bot
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

theorem Lvl.mem_termsB_zero (lv : Lvl B) (ψ : PsiT G d) :
    ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX 0 lv ↔ ψ = lv.psiBase B RD hG layer hLayer κ0 := by
  simp [Lvl.termsB]

open Classical in
/-- **The three shapes of an unrolled term, bottom bundle expanded** (`pstar` is an operative member of maximal piece index). -/
theorem Lvl.mem_termsB_succ (m : ℕ) (lv : Lvl B) (ψ : PsiT G d)
    (hψ : ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv) :
    ((¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j) ∧ ψ = lv.psiBase B RD hG layer hLayer κ0) ∨
      (∃ (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
        (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
        (c : (BX lv pstar h0 hop hmax).Ch), ψ = fun x t u => (BX lv pstar h0 hop hmax).term c x t u) ∨
      (∃ (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
        (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) ∧
        ∃ (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d),
          Ψ' ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer pstar hk) ∧
          ψ = fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
            Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u) := by
  by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
  · have hspec := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
    set ps := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hps
    by_cases hk : 1 ≤ (lv.e ps).1.val
    · have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
          (Finset.univ : Finset (BE lv ps hk).Ch).val.bind
            fun c => (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m (lv.next B RD hG layer hLayer ps hk)).map
              fun Ψ' x t u => (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u *
                Ψ' (rB (lv.split B RD hG layer hLayer ps hk).RT x) ![u (lv.split B RD hG layer hLayer ps hk).sb.b, t 1, t 2] u := by
        rw [Lvl.termsB, dif_pos hop]; exact dif_pos hk
      rw [hT, Multiset.mem_bind] at hψ
      obtain ⟨c, -, hc⟩ := hψ
      obtain ⟨Ψ', hΨ', rfl⟩ := Multiset.mem_map.mp hc
      exact Or.inr (Or.inr ⟨ps, hk, hspec.1, hspec.2, c, Ψ', hΨ', rfl⟩)
    · have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv =
          (Finset.univ : Finset (BX lv ps (by omega) hspec.1 hspec.2).Ch).val.map
            fun c => (BX lv ps (by omega) hspec.1 hspec.2).term c := by
        rw [Lvl.termsB, dif_pos hop]; exact dif_neg hk
      rw [hT, Multiset.mem_map] at hψ
      obtain ⟨c, -, rfl⟩ := hψ
      exact Or.inr (Or.inl ⟨ps, by omega, hspec.1, hspec.2, c, rfl⟩)
  · have hT : Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 ::ₘ 0 := by
      rw [Lvl.termsB]; exact dif_neg hop
    rw [hT] at hψ
    exact Or.inl ⟨hop, (Multiset.mem_cons.mp hψ).resolve_right (Multiset.notMem_zero _)⟩

/-- **Induction principle over the unrolled terms, bottom bundle expanded.** -/
theorem Lvl.termsB_induction (Q : Lvl B → PsiT G d → Prop)
    (hbase : ∀ lv : Lvl B, Q lv (lv.psiBase B RD hG layer hLayer κ0))
    (hbot : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (BX lv pstar h0 hop hmax).Ch), Q lv (fun x t u => (BX lv pstar h0 hop hmax).term c x t u))
    (hstep : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
      (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) →
      ∀ (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d), Q (lv.next B RD hG layer hLayer pstar hk) Ψ' →
        Q lv (fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
          Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u)) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv, Q lv ψ := by
  intro m
  induction m with
  | zero =>
    intro lv ψ hψ
    rw [(Lvl.mem_termsB_zero B RD hG layer hLayer BE BX lv ψ).mp hψ]
    exact hbase lv
  | succ m ih =>
    intro lv ψ hψ
    rcases Lvl.mem_termsB_succ B RD hG layer hLayer BE BX m lv ψ hψ with ⟨-, rfl⟩ | ⟨ps, h0, hop, hmax, c, rfl⟩ |
        ⟨ps, hk, hop, hmax, c, Ψ', hΨ', rfl⟩
    · exact hbase lv
    · exact hbot lv ps h0 hop hmax c
    · exact hstep lv ps hk hop hmax c Ψ' (ih _ Ψ' hΨ')

/-- The class sum is the sum of the term observables (bottom bundle expanded), for an exterior clock strictly inside the layer window of the top joint. -/
theorem clsFn_eq_sum_termsB_ext (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX)
    (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d)
    (hExt : (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E)) :
    clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s tt E =
      ((Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv).map fun ψ => termFn B κ0 lv ψ s tt E).sum := by
  classical
  have hflat := Lvl.classSum_eq_flat (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime lv (tt 0) (tt 1) (tt 2)
    (sumintBoundary s E 0) (sumintBoundary s E 1) (sumintBoundary s E 2) (sumintBoundary s E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at hflat
  set T := Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hlk := lkRaw_finsum lv.region κ0.L κ0.base
    (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv) (fun j : Fin T.toList.length => T.toList[j])
    tt (sumintBoundary s E)
    (fun κ => Filter.Eventually.of_forall fun τ => by
      rw [Lvl.psiFuel_eq_termsB_ext (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB _ _ _ _ _
        ((extOf_clock_iff B RD hG layer hLayer lv tt τ).2 hExt), multiset_sum_eq_fin])
    (fun j => habs _ (hmem j))
  show lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 (tt 0) (tt 1) (tt 2) (sumintBoundary s E 0) (sumintBoundary s E 1)
      (sumintBoundary s E 2) (sumintBoundary s E 3) = _
  rw [hflat, hlk, multiset_sum_eq_fin, Finset.mul_sum]
  rfl

/-- **The recentered unrolled bound, bottom bundle expanded** (P4's `unrolled_boundR_ext` with the bottom bundle expanded). -/
theorem unrolled_boundR_extB (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX)
    (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hExt : ∀ tt ∈ Bx,
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFnR B σ κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv) : ℝ≥0∞) * β) := by
  classical
  set T := Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have h1 := XNorm00Restr_finsum_le hθ q hBx hK (fun j : Fin T.toList.length => termFnR B σ κ0 lv T.toList[j] s)
    (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) (fun tt htt E hE => by
      unfold clsFnR termFnR
      rw [clsFn_eq_sum_termsB_ext (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB hL hF lv s tt E (hExt tt htt)
          (fun ψ hψ => habs ψ hψ tt htt E hE),
        multiset_sum_eq_fin, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ Bx K (termFnR B σ κ0 lv T.toList[j] s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

/-- `unrolled_boundR_extB` with the per-vine count `#terms ≤ ∏_{members} wt` of `Lvl.card_termsB_le_prod`. -/
theorem unrolled_boundR_extB_prod (hW : WinOfExt B RD hG layer hLayer BE) (hWB : WinOfExtBot B RD hG layer hLayer BX)
    (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hExt : ∀ tt ∈ Bx,
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ wt (lv.e pstar))
    (hChB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      Fintype.card (BX lv pstar h0 hop hmax).Ch ≤ wt (lv.e pstar))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFnR B σ κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * (((∏ j : lv.ι, wt (lv.e j) : ℕ) : ℝ≥0∞) * β) := by
  refine (unrolled_boundR_extB (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB σ hL hF lv s hθ q hBx hK hExt habs β TermBoundR).trans ?_
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  exact_mod_cast Lvl.card_termsB_le_prod (p := p) (kind := kind) B RD hG layer hLayer BE BX wt hwt hCh hChB _ lv (Nat.le_succ _)

end WaveTurbulence.VineEstS5C.P4.Bot
