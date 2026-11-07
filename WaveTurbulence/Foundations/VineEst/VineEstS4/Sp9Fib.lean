/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp8Fib

/-! # `canon(A) = ⊔_{G ∈ Zp(A)} Y(G)` and `Y(G) ≃ Y(A)` (V5 Step 4b, step 4, WP-A)

`sum_canon`: the sum over the class splits over `Zp(A)` and the fibres `yFinset G`.
`sum_yG_eq_yA`: for `G ∈ Zp(A)`, the fibre `yFinset G` is in bijection with `yFinset A` by the relation
`x = (operation at pstar)(y)` (`FamilyBatch [pstar] y x`), so a sum over the fibre of a function related to a function of `y`
is the sum over `yA`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable (p kind pstar J) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)

open Classical in
/-- The states reached from `A` by one operation at `pstar` (or by skipping it). -/
@[expose] noncomputable def zpFinset (hA : IsPrimeGarden A.skeleton) : Finset (ST w ι pstar J) :=
  (canonSpFinset p kind pstar J A sp0 hA).filter fun x => ReachSp p kind pstar J [pstar] A sp0 x.1 x.2

open Classical in
/-- The states of the class reached from `G` by a batch over the members other than `pstar`. -/
@[expose] noncomputable def yFinset (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) : Finset (ST w ι pstar J) :=
  (canonSpFinset p kind pstar J A sp0 hA).filter fun x =>
    ∃ M : List ι, M.Perm (Finset.univ.erase pstar).toList ∧ ReachSp p kind pstar J M G.1 G.2 x.1 x.2

variable {p kind pstar J A sp0}

theorem mem_zpFinset (hA : IsPrimeGarden A.skeleton) {x : ST w ι pstar J} :
    x ∈ zpFinset p kind pstar J A sp0 hA ↔ ReachSp p kind pstar J [pstar] A sp0 x.1 x.2 := by
  classical
  unfold zpFinset
  rw [Finset.mem_filter, mem_canonSpFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨[pstar] ++ (Finset.univ.erase pstar).toList, perm_cons_erase pstar, ?_⟩, h⟩
    exact ReachSp.append h (ReachSp.skips x.2 _)

theorem mem_yFinset (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J}
    (hG : ReachSp p kind pstar J [pstar] A sp0 G.1 G.2) {x : ST w ι pstar J} :
    x ∈ yFinset p kind pstar J A sp0 hA G ↔
      ∃ M : List ι, M.Perm (Finset.univ.erase pstar).toList ∧ ReachSp p kind pstar J M G.1 G.2 x.1 x.2 := by
  classical
  unfold yFinset
  rw [Finset.mem_filter, mem_canonSpFinset]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨M, hM, hr⟩ := h
    refine ⟨⟨[pstar] ++ M, (List.Perm.append_left _ hM).trans (perm_cons_erase pstar), ReachSp.append hG hr⟩, M, hM, hr⟩

theorem mem_yA (hA : IsPrimeGarden A.skeleton) {x : ST w ι pstar J} :
    x ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩ ↔
      ∃ M : List ι, M.Perm (Finset.univ.erase pstar).toList ∧ ReachSp p kind pstar J M A sp0 x.1 x.2 := by
  classical
  unfold yFinset
  rw [Finset.mem_filter, mem_canonSpFinset]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨M, hM, hr⟩ := h
    refine ⟨⟨M ++ [pstar], (List.Perm.append_right _ hM).trans (perm_erase_cons pstar),
      ReachSp.append hr (ReachSp.skips x.2 _)⟩, M, hM, hr⟩

theorem yFinset_subset (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) :
    yFinset p kind pstar J A sp0 hA G ⊆ canonSpFinset p kind pstar J A sp0 hA := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- **The class sum splits over `Zp(A)` and the fibres.** -/
theorem sum_canon (hc : Stage1.OpsCommute p kind w ι) (hA : IsPrimeGarden A.skeleton) {β : Type*} [AddCommMonoid β]
    (f : ST w ι pstar J → β) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, f x =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, ∑ x ∈ yFinset p kind pstar J A sp0 hA G, f x := by
  classical
  have hU : canonSpFinset p kind pstar J A sp0 hA = (zpFinset p kind pstar J A sp0 hA).biUnion (yFinset p kind pstar J A sp0 hA) := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · intro hx
      obtain ⟨M0, hM0, h⟩ := (mem_canonSpFinset p kind pstar J A sp0 hA).mp hx
      obtain ⟨G, M, hG, hM, hGx⟩ := decomp_state hc hM0 h.batch pstar
      obtain ⟨sG, hsG⟩ := batch_reachSp hG sp0
      obtain ⟨sx, hsx⟩ := batch_reachSp hGx sG
      have hsx2 : sx = x.2 := by
        exact ReachSp.unique (nodup_pre hM) (perm_univ_nodup hM0) (ReachSp.append hsG hsx) h
      subst hsx2
      refine ⟨⟨G, sG⟩, (mem_zpFinset hA).mpr hsG, ?_⟩
      exact (mem_yFinset hA hsG).mpr ⟨M, hM, hsx⟩
    · rintro ⟨G, hG, hx⟩
      exact yFinset_subset hA G hx
  rw [hU, Finset.sum_biUnion]
  intro G1 hG1 G2 hG2 hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hr1 := (mem_zpFinset hA).mp hG1
  have hr2 := (mem_zpFinset hA).mp hG2
  obtain ⟨M1, hM1, h1⟩ := (mem_yFinset hA hr1).mp hx1
  obtain ⟨M2, hM2, h2⟩ := (mem_yFinset hA hr2).mp hx2
  have hGG := g_unique hA (not_mem_erase hM1) (not_mem_erase hM2) hr1.batch hr2.batch h1.batch h2.batch
  exact hne (st_ext hGG (List.nodup_singleton _) (List.nodup_singleton _) hr1 hr2)

/-- **The fibre over `G ∈ Zp(A)` is in bijection with `Y(A)`** (`x = (operation at pstar)(y)`). -/
theorem sum_yG_eq_yA (hc : Stage1.OpsCommute p kind w ι) (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J}
    (hG : G ∈ zpFinset p kind pstar J A sp0 hA) {β : Type*} [AddCommMonoid β] (f g : ST w ι pstar J → β)
    (hrel : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, ∀ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩,
      FamilyBatch p kind [pstar] y.1 x.1 → f x = g y) :
    ∑ x ∈ yFinset p kind pstar J A sp0 hA G, f x = ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, g y := by
  classical
  have hr := (mem_zpFinset hA).mp hG
  -- existence of `y` for `x` (the operation at pstar moved last)
  have hex : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, ∃ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩,
      FamilyBatch p kind [pstar] y.1 x.1 := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    obtain ⟨y, hy1, hy2⟩ := move_last hc (not_mem_erase hM) hr.batch hxr.batch
    obtain ⟨sy, hsy⟩ := batch_reachSp hy1 sp0
    exact ⟨⟨y, sy⟩, (mem_yA hA).mpr ⟨M, hM, hsy⟩, hy2⟩
  refine Finset.sum_bij (fun x hx => (hex x hx).choose) (fun x hx => (hex x hx).choose_spec.1) ?_ ?_ ?_
  · intro x1 hx1 x2 hx2 heq
    obtain ⟨M1, hM1, h1⟩ := (mem_yFinset hA hr).mp hx1
    obtain ⟨M2, hM2, h2⟩ := (mem_yFinset hA hr).mp hx2
    have hy := (hex x1 hx1).choose_spec
    have hy2 := (hex x2 hx2).choose_spec
    obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy.1
    have hyp : IsPrimeGarden (hex x1 hx1).choose.1.skeleton := batch_prime hyr.batch hA
    rw [← heq] at hy2
    have := x_unique hyp (not_mem_erase hM1) (not_mem_erase hM2) h1.batch h2.batch hy.2 hy2.2
    exact st_ext this (nodup_pre hM1) (nodup_pre hM2) (ReachSp.append hr h1) (ReachSp.append hr h2)
  · intro y hy
    obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
    obtain ⟨x, hx1, hx2⟩ := diamond_ind hyr.batch (not_mem_erase hMy) hr.batch
    obtain ⟨sx, hsx⟩ := batch_reachSp hx1 G.2
    have hxm : (⟨x, sx⟩ : ST w ι pstar J) ∈ yFinset p kind pstar J A sp0 hA G := (mem_yFinset hA hr).mpr ⟨My, hMy, hsx⟩
    refine ⟨⟨x, sx⟩, hxm, ?_⟩
    have hy' := (hex ⟨x, sx⟩ hxm).choose_spec
    obtain ⟨My', hMy', hyr'⟩ := (mem_yA hA).mp hy'.1
    exact y_unique hA (not_mem_erase hMy') (not_mem_erase hMy) hyr'.batch hyr.batch hy'.2 hx2 |> fun e =>
      st_ext e (nodup_erase hMy') (nodup_erase hMy) hyr' hyr
  · intro x hx
    exact hrel x hx _ (hex x hx).choose_spec.1 (hex x hx).choose_spec.2

end WaveTurbulence.VineEstS4
