/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot19

/-! # The induction over the core vines (V5 Step 4d part C, WP-I)

`Lvl.classSum_base`: with no operative member the class sum of a level is the native kernel of its chain region (`lkRaw` of `psiNat`).
`Lvl.psiFuel κ0 hprime m lv`: the summand of a level, by recursion on a fuel: the top operative member (largest piece index) is split off and the
lower level continues (`Lvl.psiStep`).  **`Lvl.classSum_flat`**: under the clock locality of the bundle `psiSB` and of the summands, the absolute convergence
of the glued summands at every level, and the absence of an operative member at the bottom piece (finding F-BOTTOM), the class sum of every level
is `c ζ lkRaw` of `psiFuel`: the flat form of TARGET Step 4 before the splitting of the bundle into its pieces (a)-(d).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The base summand of a level (no operative member): the native summand of its chain region. -/
noncomputable def Lvl.psiBase (κ0 : KPar d) (lv : Lvl B) : PsiT G d :=
  psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) κ0.base

/-- **Base case of the induction over the core vines**: with no operative member the class sum of a level is the native kernel of its chain
region. -/
theorem Lvl.classSum_base (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (lv.psiBase B RD hG layer hLayer κ0) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold Lvl.classSum
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold twistedLocalKernel
  exact clLocalKernel_eq_lkRaw _ _ lv.region _ _ _ _ _ _ _ _ _ _ _ _ _ _


/-- Member `j` of a level has an LF operation at the state of the level. -/
def Lvl.Op (lv : Lvl B) (j : lv.ι) : Prop :=
  Nonempty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j)

open Classical in
/-- The top operative member of a level (largest piece index), if there is an operative member. -/
theorem Lvl.exists_top (lv : Lvl B) (h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j) :
    ∃ pstar, lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar ∧
      ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val := by
  obtain ⟨j0, hj0⟩ := h
  obtain ⟨pstar, hmem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => lv.Op (p := p) (kind := kind) B RD hG layer hLayer j)
    (fun j => (lv.e j).1.val) ⟨j0, by simpa using hj0⟩
  exact ⟨pstar, by simpa using hmem, fun j hj => hmax j (by simpa using hj)⟩

/-- At a member of piece index `0` the chain region of the level has the lower joint of the member as its bottom joint. -/
theorem Lvl.bottom_hb0 (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) :
    lv.c.b = ((lv.state B RD hG layer hLayer).family.placement pstar).lower := by
  have h3 := ((assemblySourceFamily B).corePlacement_at (lv.e pstar)).1
  have h2 := piece_lower_eq_jointAt B (lv.e pstar).1.val (lv.e pstar).1.2
  have h4 : jointAt B (lv.e pstar).1.val = b := by rw [h0]; exact jointAt_zero B
  show lv.c.b = ((assemblySourceFamily B).corePlacement (lv.e pstar)).lower
  rw [h3, lv.hcb]
  exact (h2.trans h4).symm

/-- **4d-B2 at a level**: if the only operative member is at piece index `0` (the bottom vine of the chain), the class sum is `c ζ` times the local
sum-integral of the A-chart bottom bundle `psiBot`. -/
theorem Lvl.classSum_bottom (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)
          ![t0, t1, t2] ![e, f, g, h] :=
  WaveTurbulence.VineEstS5B2.classSum_bottom (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) lv.c hprime
    (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF t0 t1 t2 e f g h

open Classical in
/-- The summand of a level, defined by recursion on the fuel `m`: at an operative level the top operative member is split off. -/
noncomputable def Lvl.psiFuel (κ0 : KPar d) (hprime : IsPrimeGarden G) : ℕ → Lvl B → PsiT G d
  | 0, lv => lv.psiBase B RD hG layer hLayer κ0
  | m + 1, lv =>
    if h : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j then
      if hk : 1 ≤ ((lv.e (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))).1.val) then
        Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk hprime
          (Lvl.psiFuel κ0 hprime m (lv.next B RD hG layer hLayer (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h)) hk))
      else WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c
        (Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer h))
    else lv.psiBase B RD hG layer hLayer κ0


theorem Lvl.card_next_lt (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι < Fintype.card lv.ι := by
  change Fintype.card {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} < Fintype.card lv.ι
  refine Fintype.card_subtype_lt (x := pstar) (by simp)

open Classical in
/-- **The induction over the core vines, flat form** (TARGET Step 4, structure of the argument).  Under the clock locality of the bundle and of the
summands, the absolute convergence of the glued summands at every level, and (via 4d-B2, `Lvl.classSum_bottom`) the bottom vine, the class sum of every level is `c ζ lkRaw` of the recursively defined summand `psiFuel`. -/
theorem Lvl.classSum_flat (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : Lvl B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv)
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  induction m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [Lvl.classSum_base (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv hno]
    simp only [Lvl.psiFuel, hnop, dite_false]
  | succ m ih =>
    intro lv hc t0 t1 t2 e f g h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
      set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      swap
      · have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hstep]
        exact Lvl.classSum_bottom (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime lv pstar h0 hup t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := Lvl.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => ih (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Lvl.psiFuel, dif_pos hop]
        exact dif_pos hk
      rw [hstep]
      exact Lvl.classSum_flat_step (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime lv pstar hk hA0 _ hIH
        (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [Lvl.classSum_base (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv hno]
      simp only [Lvl.psiFuel, hop, dite_false]

end WaveTurbulence.VineEstS5C
