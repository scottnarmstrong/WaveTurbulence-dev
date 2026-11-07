/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFactor

/-! # The CL-local summand of `U = S ∪ T` factors at `b` (V5 Step 4b, P2.3)

`starProd V a top x u`: the native starred-kernel factors of the pairs internal to `V` and the branches of `V.erase a`.
`spart`: the S-part of the summand (time condition of `S`, epsilon and phase of the atoms of `S` other than `b`, the starred
factors of `S`).  `summand_split`: the summand of `U` at the glued decoration is `spart * (summand of T at the upper time u b)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Defs
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

/-- Starred factors of the pairs internal to `V` and the branches of `V.erase a` (parent clocks relative to `top`). -/
@[expose] noncomputable def starProd (V : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  (∏ p ∈ clRegionalPairs hG V, KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
    (parentClock top u (p.firstLeaf hG).toNode) (parentClock top u (p.secondLeaf hG).toNode)
    (cosetDecoration G L base x (p.firstLeaf hG).toNode)) *
  (∏ v ∈ V.erase a, KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
    (parentClock top u v.toNode) (u v) (cosetDecoration G L base x v.toNode))

/-- The S-part of the summand. -/
@[expose] noncomputable def spart (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  open Classical in
  (if DomS (fun v => layer (D.coreBranch hG v).toNode) S a u then 1 else 0) *
    ((clRegionalEpsilon G (S.erase b) x : ℂ) *
      (clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base x) u *
        starProd D hG L γ δ F layer hLayer base S a (u a) x u))

theorem clLocalStarProduct_eq {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProduct D hG R L γ δ F layer hLayer base x t τ =
      starProd D hG L γ δ F layer hLayer base U a (t 0) x (clLocalClock R t τ) := rfl

end Defs

/-! ## Splitting the factors -/

section Factor
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

include hS hT hi hU

theorem eps_split (x : GNode G.tree → (Fin d → ℤ)) :
    clRegionalEpsilon G (S ∪ T) x = clRegionalEpsilon G (S.erase b) x * clRegionalEpsilon G T x := by
  unfold clRegionalEpsilon
  rw [split_union_erase hS hT hi hU]
  exact Finset.prod_union (split_disjoint_erase hS hT hi hU)

theorem phase_split (k : GNode G.tree → Mom d) (u : GBranch G.tree → ℝ) :
    clRegionalPhase G (S ∪ T) L γ δ k u =
      clRegionalPhase G (S.erase b) L γ δ k u * clRegionalPhase G T L γ δ k u := by
  unfold clRegionalPhase
  rw [split_union_erase hS hT hi hU]
  exact Finset.prod_union (split_disjoint_erase hS hT hi hU)

theorem starProd_split (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    starProd D hG L γ δ F layer hLayer base (S ∪ T) a top x u =
      starProd D hG L γ δ F layer hLayer base S a top x u *
        starProd D hG L γ δ F layer hLayer base T b top x u := by
  unfold starProd
  rw [split_pairs hS hT hi hU hG, Finset.prod_union (split_pairs_disjoint hS hT hi hU hG),
    split_interior hS hT hi hU, Finset.prod_union (split_interior_disjoint hS hT hi hU)]
  ring

end Factor

/-! ## Locality -/

theorem epsBranch_congr {x y : GNode G.tree → (Fin d → ℤ)} (v : GBranch G.tree)
    (h : ∀ i, x (v.child i) = y (v.child i)) : epsBranch x v = epsBranch y v := by
  unfold epsBranch
  rw [h 0, h 1, h 2]

theorem omegaNode_congr {k k' : GNode G.tree → Mom d} (v : GBranch G.tree)
    (h0 : k v.toNode = k' v.toNode) (h : ∀ i, k (v.child i) = k' (v.child i)) :
    omegaNode G k v = omegaNode G k' v := by
  unfold omegaNode
  rw [h0, h 0, h 1, h 2]

theorem clRegionalEpsilon_congr (V : Finset (GBranch G.tree)) {x y : GNode G.tree → (Fin d → ℤ)}
    (h : ∀ v ∈ V, ∀ i, x (v.child i) = y (v.child i)) : clRegionalEpsilon G V x = clRegionalEpsilon G V y := by
  unfold clRegionalEpsilon
  exact Finset.prod_congr rfl (fun v hv => epsBranch_congr v (h v hv))

theorem clRegionalPhase_congr (V : Finset (GBranch G.tree)) (L γ δ : ℝ) {k k' : GNode G.tree → Mom d}
    {u u' : GBranch G.tree → ℝ} (hk0 : ∀ v ∈ V, k v.toNode = k' v.toNode)
    (hk : ∀ v ∈ V, ∀ i, k (v.child i) = k' (v.child i)) (hu : ∀ v ∈ V, u v = u' v) :
    clRegionalPhase G V L γ δ k u = clRegionalPhase G V L γ δ k' u' := by
  unfold clRegionalPhase
  refine Finset.prod_congr rfl (fun v hv => ?_)
  rw [omegaNode_congr v (hk0 v hv) (hk v hv), hu v hv]

theorem glue_A (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) {y : GNode G.tree}
    (hy : y ∈ splitA RS) : glue RS xS xT y = xS y := by
  simp [glue, hy]

section Local
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
include hS hT hi hU

theorem cosetDecoration_glue_A (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) {y : GNode G.tree}
    (hy : y ∈ splitA RS) : cosetDecoration G L base (glue RS xS xT) y = cosetDecoration G L base xS y := by
  simp only [cosetDecoration, glue_A RS xS xT hy]

theorem eps_S_glue (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) :
    clRegionalEpsilon G (S.erase b) (glue RS xS xT) = clRegionalEpsilon G (S.erase b) xS := by
  refine clRegionalEpsilon_congr _ (fun v hv i => ?_)
  obtain ⟨hvb, hvS⟩ := Finset.mem_erase.mp hv
  exact glue_A RS xS xT (splitA_child hS hT hi hU RS hvS hvb i)

theorem phase_S_glue (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base (glue RS xS xT)) u =
      clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base xS) u := by
  refine clRegionalPhase_congr _ L γ δ (fun v hv => ?_) (fun v hv i => ?_) (fun v hv => rfl)
  · exact cosetDecoration_glue_A hS hT hi hU L base RS xS xT (splitA_node hS hT hi hU RS (Finset.mem_erase.mp hv).2)
  · obtain ⟨hvb, hvS⟩ := Finset.mem_erase.mp hv
    exact cosetDecoration_glue_A hS hT hi hU L base RS xS xT (splitA_child hS hT hi hU RS hvS hvb i)

theorem starProd_S_glue (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) (top : ℝ)
    (u : GBranch G.tree → ℝ) :
    starProd D hG L γ δ F layer hLayer base S a top (glue RS xS xT) u =
      starProd D hG L γ δ F layer hLayer base S a top xS u := by
  unfold starProd
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [mem_pairs_split] at hp
    have h1 : (p.firstLeaf hG).toNode ∈ splitA RS :=
      Finset.mem_union_left _ ((leaf_mem_clRealizationNodes _).mpr hp)
    rw [cosetDecoration_glue_A hS hT hi hU L base RS xS xT h1]
  · refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [cosetDecoration_glue_A hS hT hi hU L base RS xS xT (splitA_node hS hT hi hU RS (Finset.mem_erase.mp hv).2)]

end Local

theorem pair_first_eq_second (hG : G.IsPlain) (q : SourcePair G) : G.pair (q.firstLeaf hG) = q.secondLeaf hG := by
  have hh := (pairOfLeaf_sides_pos G hG (q.firstLeaf hG) (sourcePair_first_sign G hG q)).2
  rw [pairOfLeaf_firstLeaf] at hh
  exact hh.symm

/-! ## The summand of `U` at a glued decoration -/

section Summand
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
include hS hT hi hU

theorem eps_T_glue (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) {base : Mom d}
    {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT) :
    clRegionalEpsilon G T (glue RS xS xT) = clRegionalEpsilon G T xT := by
  refine clRegionalEpsilon_congr _ (fun v hv i => ?_)
  exact glue_B hS hT hi hU RS RT hL hc (cl_child_mem_support hT RT hv i)

theorem phase_T_glue (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) (hc0 : L ≠ 0) {base : Mom d}
    {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT)
    {u u' : GBranch G.tree → ℝ} (hu : ∀ v ∈ T, u v = u' v) :
    clRegionalPhase G T L γ δ (cosetDecoration G L base (glue RS xS xT)) u =
      clRegionalPhase G T L γ δ (cosetDecoration G L base xT) u' := by
  refine clRegionalPhase_congr _ L γ δ (fun v hv => ?_) (fun v hv i => ?_) hu
  · simp only [cosetDecoration, glue_B hS hT hi hU RS RT hc0 hc
      (cl_realization_mem_support RT ((branch_mem_clRealizationNodes v).mpr hv))]
  · simp only [cosetDecoration, glue_B hS hT hi hU RS RT hc0 hc (cl_child_mem_support hT RT hv i)]

theorem starProd_T_glue (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) (hc0 : L ≠ 0) {base : Mom d}
    {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT)
    {top top' : ℝ} {u u' : GBranch G.tree → ℝ} (hu : ∀ v ∈ T, u v = u' v)
    (hp : ∀ x ∈ clRealizationNodes G T, x ≠ b.toNode → parentClock top u x = parentClock top' u' x) :
    starProd D hG L γ δ F layer hLayer base T b top (glue RS xS xT) u =
      starProd D hG L γ δ F layer hLayer base T b top' xT u' := by
  have hg : ∀ {y : GNode G.tree}, y ∈ clLocalSupport RT →
      cosetDecoration G L base (glue RS xS xT) y = cosetDecoration G L base xT y := fun {y} hy => by
    simp only [cosetDecoration, glue_B hS hT hi hU RS RT hc0 hc hy]
  unfold starProd
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl (fun p hp' => ?_)
    rw [mem_pairs_split] at hp'
    have h1 : (p.firstLeaf hG).toNode ∈ clRealizationNodes G T := (leaf_mem_clRealizationNodes _).mpr hp'
    have h2 : (p.secondLeaf hG).toNode ∈ clRealizationNodes G T := by
      refine (leaf_mem_clRealizationNodes _).mpr ?_
      have := (Mole.internal_leaf_pair_iff G T (p.firstLeaf hG)).mpr hp'
      rwa [pair_first_eq_second hG p] at this
    rw [hp _ h1 (fun h => Mole.branch_toNode_ne_leaf b _ h.symm), hp _ h2 (fun h => Mole.branch_toNode_ne_leaf b _ h.symm),
      hg (cl_realization_mem_support RT h1)]
  · refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hvb, hvT⟩ := Finset.mem_erase.mp hv
    have h1 : v.toNode ∈ clRealizationNodes G T := (branch_mem_clRealizationNodes v).mpr hvT
    rw [hp _ h1 (fun h => hvb (Mole.branch_toNode_injective h)), hu v hvT,
      hg (cl_realization_mem_support RT h1)]

/-- **The summand of `U` at a glued decoration factors at `b`.**  The S-part is evaluated on the clock of `U`; the T-part is
the summand of `T` with upper time the time of `b`. -/
theorem summand_split (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {L : ℝ} (hL : L ≠ 0) {base : Mom d} {xS xT : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d}
    (hc : BdAt RT L base (bdT RT L base xS β2 β3) xT) {βU βT : Fin 4 → Mom d}
    (κU : CLLocalDecoration RU L base βU) (κT : CLLocalDecoration RT L base βT)
    (hκU : clExtendIndices RU κU.1 = glue RS xS xT) (hκT : clExtendIndices RT κT.1 = xT)
    (t : Fin 3 → ℝ) (τ : CLInternalTime RU) :
    clLocalSummand D hG RU L γ δ F layer hLayer base βU t κU τ =
      spart D hG L γ δ F layer hLayer base S a b xS (clLocalClock RU t τ) *
        clLocalSummand D hG RT L γ δ F layer hLayer base βT (tT b RU t τ) κT (restrT hS hT hi hU RU RT τ) := by
  classical
  unfold clLocalSummand
  rw [hκU, hκT]
  have hu : ∀ v ∈ T, clLocalClock RU t τ v = clLocalClock RT (tT b RU t τ) (restrT hS hT hi hU RU RT τ) v :=
    fun v hv => (clockT hS hT hi hU RU RT t τ hv).symm
  have hp : ∀ x ∈ clRealizationNodes G T, x ≠ b.toNode →
      parentClock (t 0) (clLocalClock RU t τ) x =
        parentClock ((tT b RU t τ) 0) (clLocalClock RT (tT b RU t τ) (restrT hS hT hi hU RU RT τ)) x :=
    fun x hx hne => (pclockT hS hT hi hU RU RT t τ hx hne).symm
  have hdom := domain_iff hS hT hi hU RU RT (fun v => layer (D.coreBranch hG v).toNode) t τ
  by_cases hD : τ ∈ clLocalTimeDomain RU (fun v => layer (D.coreBranch hG v).toNode) t
  · obtain ⟨hs, ht⟩ := hdom.mp hD
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem ht]
    unfold spart
    rw [if_pos hs, clLocalStarProduct_eq, clLocalStarProduct_eq, eps_split hS hT hi hU, phase_split hS hT hi hU,
      starProd_split hS hT hi hU, eps_S_glue hS hT hi hU RS xS xT, eps_T_glue hS hT hi hU RS RT hL hc,
      phase_S_glue hS hT hi hU L γ δ base RS xS xT, phase_T_glue hS hT hi hU L γ δ RS RT hL hc hu,
      starProd_S_glue hS hT hi hU D hG L γ δ F layer hLayer base RS xS xT,
      starProd_T_glue hS hT hi hU D hG L γ δ F layer hLayer RS RT hL hc hu hp]
    push_cast
    simp only [clLocalClock_upper RU t τ]
    ring
  · rw [Set.indicator_of_notMem hD]
    by_cases hs : DomS (fun v => layer (D.coreBranch hG v).toNode) S a (clLocalClock RU t τ)
    · have ht : restrT hS hT hi hU RU RT τ ∉ clLocalTimeDomain RT (fun v => layer (D.coreBranch hG v).toNode)
          (tT b RU t τ) := fun h => hD (hdom.mpr ⟨hs, h⟩)
      rw [Set.indicator_of_notMem ht]
      simp
    · unfold spart
      rw [if_neg hs]
      simp

end Summand

end WaveTurbulence.VineEstS4
