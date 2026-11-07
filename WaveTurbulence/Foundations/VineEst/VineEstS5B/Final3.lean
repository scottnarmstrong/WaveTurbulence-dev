/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final2

/-! # V5 Step 4d-B: the twisted factor identity at `U^p` (TARGET (tildeJ2), L1877-L1925)

`zp_state`: for every `G ∈ Zp(A)`, `sSumAt G (K̃^G)` is `± c ∑' ∫ bundleInt ...` in the chart of `A`, with `BOK`.
`tildeJ2_bundle`: the sum over `Zp(A)` is `c ∑'_x ∫_σ ∑_G ε_G bundleInt_G`: all states share the frame and the lower factor
`K̃_A(t_b, E, F_r)`; only the exceptional factor `rowVal` (rows `rowQ`, `rowT`, sign `nuOf`, clock/label pattern `tw`) differs.
The rows enter only as abstract functions `rowQ κ G p*`, `rowT κ G p*` (starred kernels of the native objects of `G`), so
the statement is independent of the input profile `κ.F` beyond the summability premise `hF`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The sign `ε_G = -1` for a twisted state, `+1` otherwise. -/
@[expose] noncomputable def epsOf (A : FamilyReconstruction w ι) (pstar : ι) (G : FamilyReconstruction w ι) : ℂ :=
  if twAt A G pstar then -1 else 1

open Classical in
/-- The integrand of the state `G` in the chart of `A`. -/
@[expose] noncomputable def stInt (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : FamilyReconstruction w ι)
    (x : ExtS sp0.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp0.RS) : ℂ :=
  epsOf A pstar G * bundleInt κ A sp0 (Ktil (p := p) (kind := kind) κ A sp0 hA) (decide (twAt A G pstar)) (nuOf G pstar)
    (rowQ κ G pstar) (rowT κ G pstar) x σ

theorem tw_false (A : FamilyReconstruction w ι) {kind : Bool} (hcan : CanonicalObject p kind A.layered)
    (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
      (A.family.atoms pstar) (A.family.upper pstar))
    (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
    (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    ¬ twAt A (opOut A pstar hcan hel htc hcc con) pstar := by
  intro hh
  apply hh
  rw [sigStar_false A hcan hel htc hcc con]
  rfl

theorem tw_true (A : FamilyReconstruction w ι) {kind : Bool} (hcan : CanonicalObject p kind A.layered)
    (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
      (A.family.atoms pstar) (A.family.upper pstar))
    (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
    (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    twAt A (opOut A pstar hcan hel htc hcc con) pstar := by
  intro e
  have h1 : (sigStar (opOut A pstar hcan hel htc hcc con) pstar).1 = -(sigStar A pstar).1 := by
    rw [sigStar_output]
    exact (sign_out_true A pstar hcan hel htc hcc con).trans (congrArg (fun z => -z) (by rw [sigStar_self]))
  exact units_ne_neg (sigStar A pstar).1 (by rw [← h1]; exact e.symm)

theorem zp_state (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    sSumAt κ G.1 G.2 (ktilde (p := p) (kind := kind) κ A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        (∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS, stInt (p := p) (kind := kind) κ A sp0 hA G.1 x σ) ∧
    BOK sp0.RS κ.L κ.base κ.e κ.f (stInt (p := p) (kind := kind) κ A sp0 hA G.1) := by
  classical
  have hok := sok_ktilde κ A sp0 hA hA0 hL hF hG
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hok hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    have e : stInt (p := p) (kind := kind) κ A sp0 hA A = bundleInt κ A sp0 (Ktil (p := p) (kind := kind) κ A sp0 hA) false (nuOf A pstar)
        (rowQ κ A pstar) (rowT κ A pstar) := by
      funext x σ; simp [stInt, epsOf, hn]
    rw [e]
    exact ⟨sSumAt_skip κ A sp0 _, bok_skip κ A sp0 _ hok⟩
  | apply op h =>
    cases h
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · have hn := tw_false A hcan hel htc hcc con
      have hk : ktilde (p := p) (kind := kind) κ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar false⟩ = Ktil (p := p) (kind := kind) κ A sp0 hA := by
        rw [ktilde_eq]; funext t E F'; simp [hn]
      have e : stInt (p := p) (kind := kind) κ A sp0 hA (opOut A pstar hcan hel htc hcc con) =
          bundleInt κ A sp0 (Ktil (p := p) (kind := kind) κ A sp0 hA) false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) := by
        funext x σ; simp [stInt, epsOf, hn]
      rw [hk] at hok ⊢
      rw [e]
      exact ⟨sSumAt_false κ A sp0 hcan hel htc hcc con _, bok_false κ A sp0 hcan hel htc hcc con _ hok⟩
    · have ht := tw_true A hcan hel htc hcc con
      have hk : ktilde (p := p) (kind := kind) κ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar true⟩ =
          fun t E F' => Ktil (p := p) (kind := kind) κ A sp0 hA t F' E := by
        rw [ktilde_eq]; funext t E F'; simp [ht]
      have e : stInt (p := p) (kind := kind) κ A sp0 hA (opOut A pstar hcan hel htc hcc con) = fun x σ =>
          -bundleInt κ A sp0 (fun t E Fr => (fun t E F' => Ktil (p := p) (kind := kind) κ A sp0 hA t F' E) t Fr E) true
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
        funext x σ; simp [stInt, epsOf, ht]
      rw [hk] at hok ⊢
      rw [e]
      refine ⟨?_, ?_⟩
      · rw [sSumAt_true κ A sp0 hcan hel htc hcc con]
        simp only [integral_neg, tsum_neg]
        ring
      · obtain ⟨h1, h2⟩ := bok_true κ A sp0 hcan hel htc hcc con _ hok
        exact ⟨fun x => (h1 x).neg, by simpa [norm_neg] using h2⟩

/-- **The twisted factor identity at `U^p`** (TARGET `(tildeJ2)` with the sum over the LF twists at `p*` carried inside the
decoration sum and the time integral of the chart of `A`). -/
theorem tildeJ2_bundle (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ G ∈ zpFinset p kind pstar J A sp0 hA, sSumAt κ G.1 G.2 (ktilde (p := p) (kind := kind) κ A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        ∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS,
          ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stInt (p := p) (kind := kind) κ A sp0 hA G.1 x σ := by
  classical
  have hz := fun G (hG : G ∈ zpFinset p kind pstar J A sp0 hA) => zp_state κ A sp0 hA hA0 hL hF hG
  rw [Finset.sum_congr rfl (fun G hG => (hz G hG).1), ← Finset.mul_sum]
  congr 1
  have hint : ∀ x, ∫ σ, ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stInt (p := p) (kind := kind) κ A sp0 hA G.1 x σ =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, ∫ σ, stInt (p := p) (kind := kind) κ A sp0 hA G.1 x σ := fun x =>
    integral_finset_sum _ (fun G hG => (hz G hG).2.1 x)
  simp_rw [hint]
  exact (Summable.tsum_finsetSum (fun G hG => Summable.of_norm_bounded (hz G hG).2.2
    (fun x => norm_integral_le_integral_norm _))).symm

end WaveTurbulence.VineEstS5B
