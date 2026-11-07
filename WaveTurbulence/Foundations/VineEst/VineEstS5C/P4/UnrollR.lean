/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.BundleExp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Count

/-! # P4: the unrolled identity under the exterior window of the top level only (finding F-WINCHAIN, design R)

P3's `Lvl.winOf` asks for the window of every operative level at once.  The window of the next level is the window of the clock
`u (sb.b)` of the lower joint, which is in its layer window only where the frame of the current level is nonzero (`DomF`).  So the
conjunction is not an a.e. property.  Design R: keep P3's multiset `Lvl.terms` (it never reads the windows) and prove the unrolled
identity from the exterior window `ExtOf lv u` of the level alone:

* `ext_next`: `ExtOf lv u` and `psiSB ≠ 0` give `ExtOf (lv.next ..) u` (frame `≠ 0` → `DomF` → windows of all S-branches, among
  them the lower joint `sb.b`, which is the top joint of the next level);
* `Lvl.psiFuel_eq_terms_ext`: if every bundle window `Win` holds under the exterior window (`hW`), then `ExtOf lv u` gives
  `psiFuel = ∑ terms` (if `psiSB = 0` both sides vanish, since `∑ term = psiSB`; otherwise `ext_next` and induction);
* `clsFn_eq_sum_terms_ext`, `unrolled_boundR_ext`: P3's `clsFn_eq_sum_terms` and P2's recentered `unrolled_bound_recentered` with the
  hypothesis `hExt` (the exterior clock `tt 0` strictly inside the layer window of the top joint) in place of `hWin`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The exterior window of a level: the clock of the top joint of its chain region is strictly inside its unit layer window. -/
def ExtOf (lv : Lvl B) (u : GBranch G.tree → ℝ) : Prop :=
  (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < u lv.c.a ∧
    u lv.c.a < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1

/-- The exterior window of a level at the local clock of its region is the window of the exterior clock `t 0`. -/
theorem extOf_clock_iff (lv : Lvl B) (t : Fin 3 → ℝ) (τ : CLInternalTime lv.region) :
    ExtOf B RD hG layer hLayer lv (clLocalClock lv.region t τ) ↔
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < t 0 ∧ t 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1 := by
  unfold ExtOf
  rw [show clLocalClock lv.region t τ lv.c.a = t 0 from clLocalClock_upper lv.region t τ]

/-- **The window passes to the next level** where the bundle does not vanish. -/
theorem ext_next (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) (hu : ExtOf B RD hG layer hLayer lv u)
    (h : psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u ≠ 0) :
    ExtOf B RD hG layer hLayer (lv.next B RD hG layer hLayer pstar hk) u := by
  have hf : bundleFrame κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u ≠ 0 := fun h0 =>
    h (psiSB_eq_zero_of_frame (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u h0)
  have hD := domF_of_frame_ne (pstar := pstar) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u hf
  have hsa : (lv.split B RD hG layer hLayer pstar hk).sb.a = lv.c.a := (lv.split B RD hG layer hLayer pstar hk).sa
  have hw := win_of_domF _ (lv.split B RD hG layer hLayer pstar hk) u hD (by rw [hsa]; exact hu)
  have hb := hw _ (lv.split B RD hG layer hLayer pstar hk).sb.block.2.2.1
  have hj : (lv.next B RD hG layer hLayer pstar hk).c.a = (lv.split B RD hG layer hLayer pstar hk).sb.b :=
    (lv.split B RD hG layer hLayer pstar hk).joint.symm
  unfold ExtOf
  rw [hj]
  exact hb

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- The windows of the bundle expansions hold under the exterior window of their level. -/
def WinOfExt : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
    ExtOf B RD hG layer hLayer lv u → (BE lv pstar hk).Win x u

open Classical in
/-- **The unrolled identity under the exterior window** (design R): `psiFuel = ∑ terms` wherever the clock of the top joint of the
level lies strictly inside its layer window. -/
theorem Lvl.psiFuel_eq_terms_ext (hW : WinOfExt B RD hG layer hLayer BE) :
    ∀ (m : ℕ) (lv : Lvl B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    ExtOf B RD hG layer hLayer lv u →
    Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
      ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv).map fun ψ => ψ x t u).sum := by
  intro m
  induction m with
  | zero => intro lv x t u _; simp [Lvl.psiFuel, Lvl.terms]
  | succ m ih =>
    intro lv x t u hu
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
        have hR : ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (m + 1) lv).map fun ψ => ψ x t u).sum =
            (∑ c, (BE lv ps hk).term c (rA (lv.split B RD hG layer hLayer ps hk).RS x) u) *
              ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m (lv.next B RD hG layer hLayer ps hk)).map fun Ψ' =>
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

/-- The class sum is the sum of the term observables, for an exterior clock strictly inside the layer window of the top joint. -/
theorem clsFn_eq_sum_terms_ext (hW : WinOfExt B RD hG layer hLayer BE) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d)
    (hExt : (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E)) :
    clsFn (p := p) (kind := kind) B RD hG layer hLayer κ0 lv s tt E =
      ((Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv).map fun ψ => termFn B κ0 lv ψ s tt E).sum := by
  classical
  have hflat := Lvl.classSum_eq_flat (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime lv (tt 0) (tt 1) (tt 2)
    (sumintBoundary s E 0) (sumintBoundary s E 1) (sumintBoundary s E 2) (sumintBoundary s E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at hflat
  set T := Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hlk := lkRaw_finsum lv.region κ0.L κ0.base
    (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv) (fun j : Fin T.toList.length => T.toList[j])
    tt (sumintBoundary s E)
    (fun κ => Filter.Eventually.of_forall fun τ => by
      rw [Lvl.psiFuel_eq_terms_ext (p := p) (kind := kind) B RD hG layer hLayer BE hW _ _ _ _ _
        ((extOf_clock_iff B RD hG layer hLayer lv tt τ).2 hExt), multiset_sum_eq_fin])
    (fun j => habs _ (hmem j))
  show lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 (tt 0) (tt 1) (tt 2) (sumintBoundary s E 0) (sumintBoundary s E 1)
      (sumintBoundary s E 2) (sumintBoundary s E 3) = _
  rw [hflat, hlk, multiset_sum_eq_fin, Finset.mul_sum]
  rfl

/-- **The recentered unrolled bound under the exterior window** (P2's `unrolled_bound_recentered` with `hExt` in place of `hWin`). -/
theorem unrolled_boundR_ext (hW : WinOfExt B RD hG layer hLayer BE) (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hExt : ∀ tt ∈ Bx,
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFnR B σ κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv) : ℝ≥0∞) * β) := by
  classical
  set T := Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have h1 := XNorm00Restr_finsum_le hθ q hBx hK (fun j : Fin T.toList.length => termFnR B σ κ0 lv T.toList[j] s)
    (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) (fun tt htt E hE => by
      unfold clsFnR termFnR
      rw [clsFn_eq_sum_terms_ext (p := p) (kind := kind) B RD hG layer hLayer BE hW hL hF lv s tt E (hExt tt htt)
          (fun ψ hψ => habs ψ hψ tt htt E hE),
        multiset_sum_eq_fin, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ Bx K (termFnR B σ κ0 lv T.toList[j] s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

/-- `unrolled_boundR_ext` with the per-vine count `#terms ≤ ∏_{members} wt` of `Lvl.card_terms_le_prod`. -/
theorem unrolled_boundR_ext_prod (hW : WinOfExt B RD hG layer hLayer BE) (σ : ℤˣ) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) (s : ℤˣ)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hExt : ∀ tt ∈ Bx,
      (layOf (lv.state B RD hG layer hLayer) lv.c.a : ℝ) < tt 0 ∧ tt 0 < layOf (lv.state B RD hG layer hLayer) lv.c.a + 1)
    (habs : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv, ∀ tt ∈ Bx, ∀ E ∈ K,
      LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E))
    (wt : (assemblySourceFamily B).CoreIndex → ℕ) (hwt : ∀ i, 1 ≤ wt i)
    (hCh : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), Fintype.card (BE lv pstar hk).Ch ≤ wt (lv.e pstar))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE (Fintype.card lv.ι + 1) lv,
      XNorm00Restr θ Bx K (termFnR B σ κ0 lv ψ s) ≤ β) :
    XNorm00Restr θ Bx K (clsFnR (p := p) (kind := kind) B RD hG layer hLayer σ κ0 lv s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * (((∏ j : lv.ι, wt (lv.e j) : ℕ) : ℝ≥0∞) * β) := by
  refine (unrolled_boundR_ext (p := p) (kind := kind) B RD hG layer hLayer BE hW σ hL hF lv s hθ q hBx hK hExt habs β TermBoundR).trans ?_
  refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  exact_mod_cast Lvl.card_terms_le_prod (p := p) (kind := kind) B RD hG layer hLayer BE wt hwt hCh _ lv (Nat.le_succ _)

end WaveTurbulence.VineEstS5C.P4
