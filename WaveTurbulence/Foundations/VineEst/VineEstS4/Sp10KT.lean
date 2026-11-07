/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp9Fib

/-! # The common factor of the lower kernels (V5 Step 4b, step 4, WP-A / WP-C)

`twAt A G pstar`: the operation at `pstar` that gives `G` twisted the skeleton (the sign at the lower joint of `pstar` differs from
the one of `A`).  `kTor`: the lower kernel of `y` with the first two boundary momenta exchanged iff `twAt`.
`kT_rel`: for `x` in the fibre of `G` and `x = (operation at pstar)(y)`, `kT x = kTor G y` (TARGET: "the roles of
`k_{u_2^p}` and `k_{u_23^p}` are switched again").
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The operation at `pstar` that produced `G` twisted the skeleton. -/
@[expose] def twAt (A G : FamilyReconstruction w ι) (pstar : ι) : Prop := (sigStar G pstar).1 ≠ (sigStar A pstar).1

open Classical in
/-- The lower kernel of `y`, with the first two boundary momenta exchanged iff `G` is a twist at `pstar`. -/
@[expose] noncomputable def kTor (κ : KPar d) (A G : FamilyReconstruction w ι) (pstar : ι) (y : ST w ι pstar J) :
    ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  if twAt A G pstar then kT κ y.1 y.2 t F' E else kT κ y.1 y.2 t E F'

theorem not_twAt_of_eq {A G : FamilyReconstruction w ι} (h : sigStar G pstar = sigStar A pstar) : ¬ twAt A G pstar :=
  fun hh => hh (congrArg Prod.fst h)

section Rel
variable (κ : KPar d) {A : FamilyReconstruction w ι} {sp0 : SplitAt A.skeleton A.family pstar J}

/-- **The fibre kernel is the exchanged kernel of `y`.** -/
theorem kT_rel (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J}
    (hG : ReachSp p kind pstar J [pstar] A sp0 G.1 G.2) {x y : ST w ι pstar J}
    {M My : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) (hMy : My.Perm (Finset.univ.erase pstar).toList)
    (hx : ReachSp p kind pstar J M G.1 G.2 x.1 x.2) (hy : ReachSp p kind pstar J My A sp0 y.1 y.2)
    (hxy : FamilyBatch p kind [pstar] y.1 x.1) (t : ℝ) (E F' : Mom d) :
    kT κ x.1 x.2 t E F' = kTor κ A G.1 pstar y t E F' := by
  classical
  have hsy : sigStar y.1 pstar = sigStar A pstar := sigStar_batch hy.batch (not_mem_erase hMy)
  have hsx : sigStar x.1 pstar = sigStar G.1 pstar := sigStar_batch hx.batch (not_mem_erase hM)
  have hxA : ReachSp p kind pstar J ([pstar] ++ M) A sp0 x.1 x.2 := ReachSp.append hG hx
  obtain ⟨X, sx⟩ := x
  simp only at hxy hsx hxA ⊢
  cases hxy with
  | skip _ h1 =>
    cases h1
    -- `x = y` as states, hence as splits
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0 y.1 y.2 := ReachSp.append hy (ReachSp.skips y.2 _)
    have e : sx = y.2 := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hn : ¬ twAt A G.1 pstar := not_twAt_of_eq (hsx.symm.trans hsy)
    unfold kTor
    rw [if_neg hn]
  | apply op h1 =>
    cases h1
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) y.1 pstar))
        (SplitAt.nextA y.1 y.2 pstar ε) := ReachSp.append hy (.apply _ (.nil _ _))
    have e : sx = SplitAt.nextA y.1 y.2 pstar ε := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hs := sigStar_output y.1 pstar hcan hel htc hcc con
    cases ε
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = (sigStar A pstar).1 := by
        rw [hs]
        exact h0
      have hn : ¬ twAt A G.1 pstar := fun hh => hh (hsx ▸ h1)
      unfold kTor
      rw [if_neg hn]
      exact kT_op_false κ y.1 y.2 hcan hel htc hcc con t E F'
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = -(sigStar A pstar).1 := by
        rw [hs]
        refine (sign_out_true y.1 pstar hcan hel htc hcc con).trans ?_
        exact congrArg (fun z => -z) h0
      have hn : twAt A G.1 pstar := by
        intro hh
        apply units_ne_neg (sigStar A pstar).1
        rw [← h1, hsx, hh]
      unfold kTor
      rw [if_pos hn]
      exact kT_op_true κ y.1 y.2 hcan hel htc hcc con t E F'

end Rel

end WaveTurbulence.VineEstS4
