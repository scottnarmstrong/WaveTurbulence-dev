/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BotAbs2

/-! # `UAbs` of the bottom bundle `psiBot` (V5 Step 4d part C, 4d-B2 integration)

`uAbs_stBot_of_mem`: every state of the class `canonFinset` has a uniform `UAbs` bound of its signed A-chart integrand `stBot`.
**`uAbs_psiBot`**: `psiBot` has a uniform `UAbs` bound.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

open Classical in
theorem uAbs_stBot_skip (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    UAbs (botR A c0) κ.L κ.base (stBot κ A c0 pstar A)
      (baseConst A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base (botR A c0)) := by
  refine uAbs_of_summand_eq (hLayer := stateLayer_isLayering A) c0.block (botR A c0)
    (HF_of_all A.data A.plain κ.L κ.F (stateLayer A) κ.base hF) hL _ ?_
  intro t β κd τ
  obtain ⟨t0, t1, t2, rfl⟩ : ∃ t0 t1 t2 : ℝ, t = ![t0, t1, t2] := ⟨t 0, t 1, t 2, vec3_eta t⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ e f g h : Mom d, β = ![e, f, g, h] := ⟨β 0, β 1, β 2, β 3, vec4_eta β⟩
  rw [← clLocalSummand_eq_psiNat]
  exact stBot_skip_eq (kparAt κ ![t0, t1, t2] ![e, f, g, h]) A c0 hb0 κd τ

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
  (hcan : CanonicalObject p kind A.layered)
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

open Classical in
theorem uAbs_stBot_false (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    UAbs (botR A c0) κ.L κ.base (stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con))
      (baseConst con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base (botR A c0)) := by
  refine uAbs_of_summand_eq (hLayer := stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) c0.block (botR A c0)
    (HF_of_all con.data A.plain κ.L κ.F (stateLayer (opOut A pstar hcan hel htc hcc con)) κ.base hF) hL _ ?_
  intro t β κd τ
  obtain ⟨t0, t1, t2, rfl⟩ : ∃ t0 t1 t2 : ℝ, t = ![t0, t1, t2] := ⟨t 0, t 1, t 2, vec3_eta t⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ e f g h : Mom d, β = ![e, f, g, h] := ⟨β 0, β 1, β 2, β 3, vec4_eta β⟩
  exact (stBot_false_eq (kparAt κ ![t0, t1, t2] ![e, f, g, h]) A c0 hcan hel htc hcc hb0 con κd τ).trans
    (clLocalSummand_eq_psiNat _ _ _ _ _ _ _ _ _ _ _ _ _ _)

open Classical in
theorem uAbs_stBot_true (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∃ C : ℝ, 0 ≤ C ∧ UAbs (botR A c0) κ.L κ.base (stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con)) C := by
  have hT := chain_stw c0 pstar hb0
  have hHF := HF_of_all con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con)) κ.base hF
  have key := uAbs_psiNat (hLayer := stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (γ := κ.γ) (δ := κ.δ)
    (c0.next pstar true).block (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true)
      (c0.next pstar true).block (c0.next pstar true).cl) hHF hL
  have key' := uAbs_const_mul _ κ.L κ.base _ (-1 : ℂ) key
  refine ⟨_, ?_, uAbs_transport (botR A c0) _ κ.L κ.base (VineEstS5B2.decEquiv (A.family.placement pstar) hT κ.L κ.base)
    (tEquivS (A.family.placement pstar) (botR A c0) _)
    (tEquivS_measurePreserving (A.family.placement pstar) (botR A c0) _) _ _ ?_ key'⟩
  · exact mul_nonneg (norm_nonneg _) (baseConst_nonneg _)
  intro t β κd τ
  obtain ⟨t0, t1, t2, rfl⟩ : ∃ t0 t1 t2 : ℝ, t = ![t0, t1, t2] := ⟨t 0, t 1, t 2, vec3_eta t⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ e f g h : Mom d, β = ![e, f, g, h] := ⟨β 0, β 1, β 2, β 3, vec4_eta β⟩
  have h1 := (stBot_true_eq (kparAt κ ![t0, t1, t2] ![e, f, g, h]) A c0 hcan hel htc hcc hb0 con κd τ)
  have h2 := congrArg Neg.neg (clLocalSummand_eq_psiNat (hLayer := stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) _ κ.L κ.γ κ.δ κ.F _ κ.base
    ![e, f, g, h] ![t0, t1, t2] (VineEstS5B2.decEquiv (A.family.placement pstar) hT κ.L κ.base ![e, f, g, h] κd)
    (tEquivS (A.family.placement pstar) (botR A c0) _ τ))
  simp only [neg_mul, one_mul]
  exact h2.symm.trans h1.symm

end Ops

open Classical in
theorem uAbs_stBot_of_mem (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {z : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hz : z ∈ canonFinsetK p kind A c0) :
    ∃ C : ℝ, 0 ≤ C ∧ UAbs (botR A c0) κ.L κ.base (stBot κ A c0 pstar z.1) C := by
  obtain ⟨B, cB⟩ := z
  have hr := (mem_canonFinset_iff_bottom hA hup).mp hz
  rcases reach_single hr with e | ⟨op, e⟩
  · rw [e]
    exact ⟨_, baseConst_nonneg _, uAbs_stBot_skip κ A c0 hb0 hL hF⟩
  · rw [e]
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact ⟨_, baseConst_nonneg _, uAbs_stBot_false κ A c0 hcan hel htc hcc hb0 con hL hF⟩
    · exact uAbs_stBot_true κ A c0 hcan hel htc hcc hb0 con hL hF

open Classical in
/-- **`UAbs` of the bottom bundle `psiBot`** (uniform in the exterior times and momenta). -/
theorem uAbs_psiBot (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∃ C : ℝ, 0 ≤ C ∧ UAbs (botR A c0) κ.L κ.base (psiBot p kind κ A c0 pstar) C := by
  have hh : ∀ z ∈ canonFinsetK p kind A c0, ∃ C : ℝ, 0 ≤ C ∧ UAbs (botR A c0) κ.L κ.base (stBot κ A c0 pstar z.1) C :=
    fun z hz => uAbs_stBot_of_mem (p := p) (kind := kind) κ A c0 hA hb0 hup hL hF hz
  choose! C hC0 hC using hh
  refine ⟨∑ z ∈ canonFinsetK p kind A c0, C z, Finset.sum_nonneg fun z hz => hC0 z hz, ?_⟩
  exact uAbs_finsetSum (botR A c0) κ.L κ.base (canonFinsetK p kind A c0) (fun z x t u => stBot κ A c0 pstar z.1 x t u) C hC

end WaveTurbulence.VineEstS5C
