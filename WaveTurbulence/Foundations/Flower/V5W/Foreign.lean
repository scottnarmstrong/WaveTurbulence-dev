/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Statements
public import WaveTurbulence.Foundations.Flower.V5W.Rigid
public import WaveTurbulence.Foundations.Flower.V5W.Weight

/-! # V5W-0, T4: the weighted class factorization

* `unitKernelFW_foreign : UnitKernelFWForeign` (weighted `VineC.unitKernelW_foreign`, TARGET L1948, observation 1): an
  operation at a member outside the unit leaves the unit's weighted kernel unchanged.  The rows of the region are
  ordinary (`FullRigid`), so `clLocalKernelFW_rigid_LF`/`_false_LF` apply, with the multiplier transported by
  `regionWeightFW_true`/`_false`.
* `reachU_kernelFW_eq`, `coordFW_exists`, `unitKernelFW_classProd`: the weighted unit kernel of a class member is the
  weighted kernel of its unit coordinate (copies of `ReachU.kernel_eq`, `coord_exists`, `unitKernelW_classProd`).
* `weightedClassFactorization : WeightedClassFactorization` (weighted `VineC.sum_tauClass_vineD_api`), through main's
  generic `sum_layered_eq_sum_classU` and `sum_classU_outerValM`.  The modulation `modW λ` (R58, U-clock) is carried in
  every unit and class factor, uniformly in `λ`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory
open WaveTurbulence.VineC

/-- **T4's key lemma** (weighted `VineC.unitKernelW_foreign`). -/
theorem unitKernelFW_foreign : UnitKernelFWForeign := by
  intro w ι Q p kind d pw g S X u i hi op L γ δ F base W t0 t1 t2 e f g' h
  have hF := fullRigid_of_disjoint X.family (u.disj i hi)
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact clLocalKernelFW_false_LF (X.source i hcan hel htc hcc) con u.blk.block hF.lower_notMem
      (clRegionData X.skeleton u.blk.block u.cl) (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (opOut X i hcan hel htc hcc con)) pw g L γ δ F base _ _
      (fun z => regionWeightFW_false X i hcan hel htc hcc con pw g S L base u.blk.a hF.lower_notMem z)
      W t0 t1 t2 e f g' h
  · exact clLocalKernelFW_rigid_LF (X.source i hcan hel htc hcc) con u.blk.block hF
      (clRegionData X.skeleton u.blk.block u.cl) _ (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (opOut X i hcan hel htc hcc con)) pw g L γ δ F base _ _
      (fun z' => regionWeightFW_true X i hcan hel htc hcc con pw g S L base hF u.blk.block.2.1 z')
      W t0 t1 t2 e f g' h

section Reach
variable {w : ℕ} {ι : Type*} {J : Type*} {Qm : J → ι → Prop} {p : ℕ} {kind : Bool}

/-- Along a batch avoiding the unit `j`, the weighted kernel of the unit `j` is unchanged. -/
theorem reachU_kernelFW_eq {Lst : List ι} {A B : FamilyReconstruction w ι}
    {us : ∀ j, UnitAt A.skeleton A.family (Qm j)} {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)}
    (hR : ReachU p kind Qm Lst A us B us') (j : J) (hL : ∀ i ∈ Lst, ¬ Qm j i) {d : ℕ} (pw : ℕ) (g : Mom d → ℂ)
    (S : Option ℝ) (L' γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    unitKernelFW pw g S B (us' j) L' γ δ F base W t0 t1 t2 e f g' k =
      unitKernelFW pw g S A (us j) L' γ δ F base W t0 t1 t2 e f g' k := by
  induction hR with
  | nil A us => rfl
  | skip i h ih => exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
  | @apply Lst A us B us' i op h ih =>
    refine (ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))).trans ?_
    exact unitKernelFW_foreign pw g S A (us j) (hL i List.mem_cons_self) op L' γ δ F base W t0 t1 t2 e f g' k

end Reach

section Proj
variable {w : ℕ} {ι κ : Type*} (e : κ → ι) (he : Function.Injective e) {Q : ι → Prop} (hQ : ∀ k, Q (e k))

/-- The weighted unit kernel of the big state is the weighted twisted kernel of the restricted state. -/
theorem unitKernelFW_eq_twisted {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (X : FamilyReconstruction w ι)
    (u : UnitAt X.skeleton X.family Q) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ)
    (e' f g' h : Mom d) :
    unitKernelFW pw g S X u L γ δ F base W t0 t1 t2 e' f g' h =
      twistedLocalKernelFW pw g S (stComap X e he) (u.toChainAt e he hQ) L γ δ F base W t0 t1 t2 e' f g' h := rfl

end Proj

section Coord
variable {w : ℕ} {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

omit [Fintype J] in
/-- **Existence of the unit coordinates, with the weighted unit kernel read at the coordinate** (weighted
`VineC.coord_exists`). -/
theorem coordFW_exists {A : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)}
    {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J) :
    ∃ x, IsCoord Us p kind A us y j x ∧
      ∀ {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ)
        (t0 t1 t2 : ℝ) (e f g' h : Mom d),
        twistedLocalKernelFW pw g S x.1 x.2 L γ δ F base W t0 t1 t2 e f g' h =
          unitKernelFW pw g S y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g' h := by
  obtain ⟨B, usB⟩ := y
  obtain ⟨M, hM, hR⟩ := hy
  dsimp only at hR ⊢
  have hMn : M.Nodup := perm_univ_nodup hM
  obtain ⟨Y, h1, h2⟩ := batch_partition (fun i => decide (Us.unitOf i = j)) M hMn hR.batch
  obtain ⟨usY, hRY⟩ := batch_reachU (Qm := Us.Q) h1 us
  obtain ⟨us'', hR2⟩ := batch_reachU (Qm := Us.Q) h2 usY
  have hn2 : (M.filter (fun i => decide (Us.unitOf i = j)) ++
      M.filter (fun i => !decide (Us.unitOf i = j))).Nodup :=
    (List.filter_append_perm (fun i => decide (Us.unitOf i = j)) M).nodup_iff.mpr hMn
  have hus : us'' = usB := ReachU.unique hn2 hMn (hRY.append hR2) hR
  subst hus
  obtain ⟨N, hN, hNe⟩ := Us.filter_eq_map j hM
  have hRY' : ReachU p kind Us.Q (N.map (Us.emb j)) A us Y usY := by rw [hNe]; exact hRY
  have hproj := ReachU.proj (Us.emb j) (Us.inj j) j (Us.q_emb j) N hRY'
  have hnot : ∀ i ∈ M.filter (fun i => !decide (Us.unitOf i = j)), ¬ Us.Q j i := by
    intro i hi hq
    have := (List.mem_filter.mp hi).2
    simp only [UnitSplit.Q] at hq
    simp [hq] at this
  refine ⟨⟨stComap Y (Us.emb j) (Us.inj j), (usY j).toChainAt (Us.emb j) (Us.inj j) (Us.q_emb j)⟩,
    ⟨⟨N, hN, hproj⟩, fun k => ?_⟩, fun pw g S L γ δ F base W t0 t1 t2 e f g' h => ?_⟩
  · show sigStar Y (Us.emb j k) = sigStar B (Us.emb j k)
    exact (sigStar_batch h2 (fun hm => hnot _ hm (Us.q_emb j k))).symm
  · exact (unitKernelFW_eq_twisted (Us.emb j) (Us.inj j) (Us.q_emb j) pw g S Y (usY j) L γ δ F base W t0 t1 t2
      e f g' h).symm.trans (reachU_kernelFW_eq hR2 j hnot pw g S L γ δ F base W t0 t1 t2 e f g' h).symm

omit [Fintype J] in
/-- **The weighted unit kernel of a class member is the weighted kernel of its unit coordinate** (TARGET L1948,
observation 1; weighted `VineC.unitKernelW_classProd`). -/
theorem unitKernelFW_classProd {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J)
    {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ)
    (t0 t1 t2 : ℝ) (e f g' h : Mom d) :
    unitKernelFW pw g S y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g' h =
      twistedLocalKernelFW pw g S (classProd Us p kind A us y j).1 (classProd Us p kind A us y j).2 L γ δ F base W
        t0 t1 t2 e f g' h := by
  obtain ⟨x, hx, hk⟩ := coordFW_exists hy j
  rw [coord_unique hA (classProd_isCoord hy j) hx]
  exact (hk pw g S L γ δ F base W t0 t1 t2 e f g' h).symm

end Coord

/-- **T4: the weighted class factorization** (weighted `VineC.sum_tauClass_vineD_api`). -/
theorem weightedClassFactorization : WeightedClassFactorization := by
  intro w S D hS layer hLayer J₀ instF instD U₀ a₀ b₀ R₀ n₀ B₀ hdisj₀ hprime p kind T hT V I instI sgn Ξ Wt d G L γ δ
    base roots tt lay hinges Zw hG amp frq route hclk hmom F gU SU hV hξ hint hsm
  rw [sum_layered_eq_sum_classU (Us := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (hξ i)]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hfg : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ (j : J₀) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d),
        unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3) =
          recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
              ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
            twistedLocalKernelFW p (gU j) (SU j)
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).1
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).2
              L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
    intro y hy j lam t k
    obtain ⟨M, _, hR⟩ := (mem_classU hprime).mp hy
    unfold unitRecenteredFW
    rw [hR.sign_upper j, unitKernelFW_classProd hprime ((mem_classU hprime).mp hy) j]
    rfl
  rw [sum_classU_outerValM (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt lay hinges Zw hG
    (amp i ξ) (frq i ξ) route hclk hmom _
    (fun j lam t k x => recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
        ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelFW p (gU j) (SU j) x.1 x.2 L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3))
    hfg (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  unfold twistedRecenteredFW
  exact (Finset.mul_sum _ _ _).symm

end WaveTurbulence.Flower.V5W
