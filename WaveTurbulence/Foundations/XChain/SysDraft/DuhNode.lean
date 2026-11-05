/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.DuhTime

/-!
# Obligation O-TR1: the root splitting of the tree terms (scratch, snapshot 5)

`treeTerm_node`: for `t ≥ p` and summable data,
`𝒥_{node l m r}(t)_n = ∫_p^t 𝒞₊(𝒥_l(s), 𝒥̄_m(s), 𝒥_r(s))_n ds`.

The steps:
1. The `ε` coefficients, the leaf factors and the prefactor of `node l m r` split at the root; the middle
   subtree is conjugated (`epsProd_node`, `leafProd_node`, `treePrefactor_node`).
2. For each `s`, the product of the three decoration sums and the pair sum of `𝒞₊` combine into one
   absolutely convergent sum over `Σ q, Dec(l,q₁) × Dec(m,q₂) × Dec(r,n-q₁+q₂)` (`aNonlin_treeTerms_eq`).
3. That sum commutes with `∫_p^t ds`. The integrands are measurable and bounded, and their integrals are
   summable (`integral_tsum_nodeSummand`).
4. Reindex by `decSplit`; the time integral of each term is `timeInt_node`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

section Node

variable (l m r : TTree) (L γ δ : ℝ) {d : ℕ}

/-! ### The `ε` coefficients, leaf factors and prefactor of `node l m r` -/

theorem epsProd_node (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ)) :
    epsProd (TTree.node l m r) κ = (epsCoef (κ ((rootB l m r).child 0)) (κ ((rootB l m r).child 1))
        (κ ((rootB l m r).child 2)) : ℂ) *
      (epsProd l ((isSubtreeAt_left l m r).res κ) *
        (epsProd m ((isSubtreeAt_mid l m r).res κ) * epsProd r ((isSubtreeAt_right l m r).res κ))) := by
  unfold epsProd
  rw [prod_gBranch_node (M := ℂ)]
  rfl

theorem conj_epsProd (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) :
    (starRingEnd ℂ) (epsProd S κ) = epsProd S κ := by
  unfold epsProd
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => Complex.conj_ofReal _

theorem zpowSign_neg (u : ℤˣ) (z : ℂ) : zpowSign (-u) z = (starRingEnd ℂ) (zpowSign u z) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [zpowSign]
  · simp [zpowSign]

theorem leafProd_node (b : (Fin d → ℤ) → ℂ) (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ)) :
    leafProd (TTree.node l m r) b κ = leafProd l b ((isSubtreeAt_left l m r).res κ) *
      ((starRingEnd ℂ) (leafProd m b ((isSubtreeAt_mid l m r).res κ)) *
        leafProd r b ((isSubtreeAt_right l m r).res κ)) := by
  unfold leafProd
  rw [prod_gLeaf_node (M := ℂ), map_prod (starRingEnd ℂ)]
  have hl : ∀ ℓ : GLeaf (single l), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_left l m r).embL ℓ).toNode) (b (κ ((isSubtreeAt_left l m r).embL ℓ).toNode)) =
      zpowSign (treeSign l ℓ.toNode) (b ((isSubtreeAt_left l m r).res κ ℓ.toNode)) := fun ℓ => by
    rw [IsSubtreeAt.embL_toNode, treeSign_embN_left]
    rfl
  have hm : ∀ ℓ : GLeaf (single m), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_mid l m r).embL ℓ).toNode) (b (κ ((isSubtreeAt_mid l m r).embL ℓ).toNode)) =
      (starRingEnd ℂ) (zpowSign (treeSign m ℓ.toNode) (b ((isSubtreeAt_mid l m r).res κ ℓ.toNode))) :=
    fun ℓ => by
      rw [IsSubtreeAt.embL_toNode, treeSign_embN_mid, zpowSign_neg]
      rfl
  have hr : ∀ ℓ : GLeaf (single r), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_right l m r).embL ℓ).toNode) (b (κ ((isSubtreeAt_right l m r).embL ℓ).toNode)) =
      zpowSign (treeSign r ℓ.toNode) (b ((isSubtreeAt_right l m r).res κ ℓ.toNode)) := fun ℓ => by
    rw [IsSubtreeAt.embL_toNode, treeSign_embN_right]
    rfl
  rw [Finset.prod_congr rfl fun ℓ _ => hl ℓ, Finset.prod_congr rfl fun ℓ _ => hm ℓ,
    Finset.prod_congr rfl fun ℓ _ => hr ℓ]

theorem treePrefactor_node :
    treePrefactor L γ δ d (TTree.node l m r) = (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) *
      (treePrefactor L γ δ d l * ((starRingEnd ℂ) (treePrefactor L γ δ d m) *
        treePrefactor L γ δ d r)) := by
  unfold treePrefactor
  rw [prod_gBranch_node (M := ℂ), map_mul, map_pow, map_prod, Complex.conj_ofReal, treeSign_rootB]
  have hl : ∀ c : GBranch (single l), Complex.I *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_left l m r).embB c).toNode : ℤˣ) : ℤ) : ℂ) =
      Complex.I * (((treeSign l c.toNode : ℤˣ) : ℤ) : ℂ) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_left]
  have hm : ∀ c : GBranch (single m), Complex.I *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_mid l m r).embB c).toNode : ℤˣ) : ℤ) : ℂ) =
      (starRingEnd ℂ) (Complex.I * (((treeSign m c.toNode : ℤˣ) : ℤ) : ℂ)) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_mid, map_mul, Complex.conj_I, map_intCast,
      Units.val_neg, Int.cast_neg]
    ring
  have hr : ∀ c : GBranch (single r), Complex.I *
      (((treeSign (TTree.node l m r) ((isSubtreeAt_right l m r).embB c).toNode : ℤˣ) : ℤ) : ℂ) =
      Complex.I * (((treeSign r c.toNode : ℤˣ) : ℤ) : ℂ) := fun c => by
    rw [IsSubtreeAt.embB_toNode, treeSign_embN_right]
  rw [Finset.prod_congr rfl fun c _ => hl c, Finset.prod_congr rfl fun c _ => hm c,
    Finset.prod_congr rfl fun c _ => hr c]
  simp only [TTree.order, Units.val_one, Int.cast_one]
  ring

/-! ### The joint summand -/

/-- The `ε`-and-phase factor of the pair `q` in `𝒞₊`. -/
noncomputable def pairFactor (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) (s : ℝ) : ℂ :=
  (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
    Complex.exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
      resFactor (latticePoint L q.1) (latticePoint L q.2) (latticePoint L (n - q.1 + q.2))
        (latticePoint L n) * s : ℝ) : ℂ) * Complex.I)

theorem aNonlinTerm_eq (s : ℝ) (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    aNonlinTerm L γ δ 1 s f g h n q = pairFactor L γ δ n q s * f q.1 * g q.2 * h (n - q.1 + q.2) :=
  rfl

theorem norm_pairFactor_le (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) (s : ℝ) :
    ‖pairFactor L γ δ n q s‖ ≤ 1 := by
  unfold pairFactor
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  unfold epsCoef
  split_ifs <;> simp

theorem continuous_pairFactor (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    Continuous fun s => pairFactor L γ δ n q s := by
  unfold pairFactor
  fun_prop

/-- The joint summand over `Σ q, Dec(l,q₁) × Dec(m,q₂) × Dec(r,n-q₁+q₂)`. -/
noncomputable def nodeSummand (p : ℕ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) (s : ℝ) : ℂ :=
  pairFactor L γ δ n x.1 s * (treeSummand L γ δ p l b s x.1.1 x.2.1 *
    ((starRingEnd ℂ) (treeSummand L γ δ p m b s x.1.2 x.2.2.1) *
      treeSummand L γ δ p r b s (n - x.1.1 + x.1.2) x.2.2.2))

/-- The leaf weight of a joint decoration. -/
noncomputable def nodeWeight (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) : ℝ :=
  (∏ ℓ : GLeaf (single l), ‖b (x.2.1.1 ℓ.toNode)‖) *
    ((∏ ℓ : GLeaf (single m), ‖b (x.2.2.1.1 ℓ.toNode)‖) *
      ∏ ℓ : GLeaf (single r), ‖b (x.2.2.2.1 ℓ.toNode)‖)

theorem nodeWeight_nonneg (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) : 0 ≤ nodeWeight l m r b n x :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem summable_nodeWeight {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (n : Fin d → ℤ) :
    Summable (nodeWeight l m r b n) := by
  have hg := summable_leafNorm_sigma (TTree.node l m r) hb
  have hg0 : ∀ x : (Σ n : Fin d → ℤ, TreeDecoration (TTree.node l m r) d n),
      0 ≤ ∏ ℓ : GLeaf (single (TTree.node l m r)), ‖b (x.2.1 ℓ.toNode)‖ :=
    fun x => Finset.prod_nonneg fun _ _ => norm_nonneg _
  obtain ⟨hκ, -⟩ := (summable_sigma_of_nonneg hg0).1 hg
  refine (decSplit l m r n).summable_iff.1 ?_
  convert hκ n using 1
  funext κ
  show nodeWeight l m r b n (decSplit l m r n κ) = _
  rw [prod_gLeaf_node (M := ℝ)]
  rfl

theorem norm_nodeSummand_le (p : ℕ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) {s t : ℝ} (hst : s ≤ t) :
    ‖nodeSummand l m r L γ δ p b n x s‖ ≤
      boxVol l p t * (boxVol m p t * boxVol r p t) * nodeWeight l m r b n x := by
  unfold nodeSummand nodeWeight
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
  have h1 := norm_treeSummand_le L γ δ p l b s x.1.1 x.2.1
  have h2 := norm_treeSummand_le L γ δ p m b s x.1.2 x.2.2.1
  have h3 := norm_treeSummand_le L γ δ p r b s (n - x.1.1 + x.1.2) x.2.2.2
  have hb1 := boxVol_mono l (p : ℝ) hst
  have hb2 := boxVol_mono m (p : ℝ) hst
  have hb3 := boxVol_mono r (p : ℝ) hst
  have hE := norm_pairFactor_le L γ δ n x.1 s
  have P1 : 0 ≤ ∏ ℓ : GLeaf (single l), ‖b (x.2.1.1 ℓ.toNode)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  have P2 : 0 ≤ ∏ ℓ : GLeaf (single m), ‖b (x.2.2.1.1 ℓ.toNode)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  have P3 : 0 ≤ ∏ ℓ : GLeaf (single r), ‖b (x.2.2.2.1 ℓ.toNode)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  have B1 := boxVol_nonneg l (p : ℝ) s
  have B2 := boxVol_nonneg m (p : ℝ) s
  have B3 := boxVol_nonneg r (p : ℝ) s
  change ‖treeSummand L γ δ p l b s x.1.1 x.2.1‖ ≤ boxVol l p s * _ at h1
  change ‖treeSummand L γ δ p m b s x.1.2 x.2.2.1‖ ≤ boxVol m p s * _ at h2
  change ‖treeSummand L γ δ p r b s (n - x.1.1 + x.1.2) x.2.2.2‖ ≤ boxVol r p s * _ at h3
  calc _ ≤ 1 * ((boxVol l p s * ∏ ℓ : GLeaf (single l), ‖b (x.2.1.1 ℓ.toNode)‖) *
        ((boxVol m p s * ∏ ℓ : GLeaf (single m), ‖b (x.2.2.1.1 ℓ.toNode)‖) *
          (boxVol r p s * ∏ ℓ : GLeaf (single r), ‖b (x.2.2.2.1 ℓ.toNode)‖))) := by
        gcongr
    _ ≤ 1 * ((boxVol l p t * ∏ ℓ : GLeaf (single l), ‖b (x.2.1.1 ℓ.toNode)‖) *
        ((boxVol m p t * ∏ ℓ : GLeaf (single m), ‖b (x.2.2.1.1 ℓ.toNode)‖) *
          (boxVol r p t * ∏ ℓ : GLeaf (single r), ‖b (x.2.2.2.1 ℓ.toNode)‖))) := by
        gcongr
        all_goals exact mul_nonneg (boxVol_nonneg _ _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

theorem summable_nodeSummand (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖)
    (n : Fin d → ℤ) (s : ℝ) : Summable fun x => nodeSummand l m r L γ δ p b n x s :=
  Summable.of_norm_bounded ((summable_nodeWeight l m r hb n).mul_left _)
    fun x => norm_nodeSummand_le l m r L γ δ p b n x le_rfl

/-! ### Step 1: for each time, one absolutely convergent sum -/

theorem aNonlin_treeTerms_eq (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (s : ℝ)
    (n : Fin d → ℤ) :
    aNonlin L γ δ 1 s (treeTerm L γ δ p l b s) (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b s k))
        (treeTerm L γ δ p r b s) n =
      (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
        ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r)) *
        ∑' x, nodeSummand l m r L γ δ p b n x s := by
  set P := treePrefactor L γ δ d l * ((starRingEnd ℂ) (treePrefactor L γ δ d m) *
    treePrefactor L γ δ d r)
  have hq : ∀ q : (Fin d → ℤ) × (Fin d → ℤ),
      aNonlinTerm L γ δ 1 s (treeTerm L γ δ p l b s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b s k)) (treeTerm L γ δ p r b s) n q =
      P * ∑' y : DecFiber l m r n q, nodeSummand l m r L γ δ p b n ⟨q, y⟩ s := by
    intro q
    rw [aNonlinTerm_eq]
    simp only [treeTerm_eq]
    rw [map_mul, Complex.conj_tsum]
    have ha := summable_treeSummand L γ δ p l hb s q.1
    have hb' : Summable fun κ : TreeDecoration m d q.2 =>
        ‖(starRingEnd ℂ) (treeSummand L γ δ p m b s q.2 κ)‖ := by
      simpa using summable_treeSummand L γ δ p m hb s q.2
    have hc := summable_treeSummand L γ δ p r hb s (n - q.1 + q.2)
    have hbc := tsum_mul_tsum_of_summable_norm hb' hc
    have hbc' : Summable fun w : TreeDecoration m d q.2 × TreeDecoration r d (n - q.1 + q.2) =>
        ‖(starRingEnd ℂ) (treeSummand L γ δ p m b s q.2 w.1) *
          treeSummand L γ δ p r b s (n - q.1 + q.2) w.2‖ := by
      simp only [norm_mul]
      exact summable_mul_of_summable_norm (f := fun κ => ‖(starRingEnd ℂ)
        (treeSummand L γ δ p m b s q.2 κ)‖) (g := fun κ => ‖treeSummand L γ δ p r b s
          (n - q.1 + q.2) κ‖) (by simpa using hb') (by simpa using hc)
    have habc := tsum_mul_tsum_of_summable_norm ha hbc'
    calc pairFactor L γ δ n q s * (treePrefactor L γ δ d l * ∑' κ, treeSummand L γ δ p l b s q.1 κ) *
          ((starRingEnd ℂ) (treePrefactor L γ δ d m) *
            ∑' κ, (starRingEnd ℂ) (treeSummand L γ δ p m b s q.2 κ)) *
          (treePrefactor L γ δ d r * ∑' κ, treeSummand L γ δ p r b s (n - q.1 + q.2) κ)
        = P * (pairFactor L γ δ n q s * ((∑' κ, treeSummand L γ δ p l b s q.1 κ) *
            ((∑' κ, (starRingEnd ℂ) (treeSummand L γ δ p m b s q.2 κ)) *
              ∑' κ, treeSummand L γ δ p r b s (n - q.1 + q.2) κ))) := by ring
      _ = P * ∑' y : DecFiber l m r n q, nodeSummand l m r L γ δ p b n ⟨q, y⟩ s := by
        rw [hbc, habc, ← tsum_mul_left]
        rfl
  rw [aNonlin_eq_tsum_aNonlinTerm, tsum_congr hq, tsum_mul_left,
    (summable_nodeSummand l m r L γ δ p hb n s).tsum_sigma]
  unfold coupling
  ring

/-! ### Step 2: the sum commutes with the time integral -/

theorem stronglyMeasurable_nodeSummand (p : ℕ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) :
    StronglyMeasurable fun s => nodeSummand l m r L γ δ p b n x s := by
  unfold nodeSummand
  simp only [treeSummand_eq]
  have hl := stronglyMeasurable_timeInt L γ δ l x.2.1.1 p
  have hm := stronglyMeasurable_timeInt L γ δ m x.2.2.1.1 p
  have hr := stronglyMeasurable_timeInt L γ δ r x.2.2.2.1 p
  exact (continuous_pairFactor L γ δ n x.1).stronglyMeasurable.mul
    (((stronglyMeasurable_const.mul hl).mul stronglyMeasurable_const).mul
      ((Complex.continuous_conj.comp_stronglyMeasurable
        ((stronglyMeasurable_const.mul hm).mul stronglyMeasurable_const)).mul
        ((stronglyMeasurable_const.mul hr).mul stronglyMeasurable_const)))

theorem integral_tsum_nodeSummand (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖)
    {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    ∫ s in (p : ℝ)..t, ∑' x, nodeSummand l m r L γ δ p b n x s =
      ∑' x, ∫ s in (p : ℝ)..t, nodeSummand l m r L γ δ p b n x s := by
  set C := boxVol l p t * (boxVol m p t * boxVol r p t)
  have hint : ∀ x, IntegrableOn (fun s => nodeSummand l m r L γ δ p b n x s) (Ioc (p : ℝ) t) :=
    fun x => Measure.integrableOn_of_bounded (M := C * nodeWeight l m r b n x) measure_Ioc_lt_top.ne
      (stronglyMeasurable_nodeSummand l m r L γ δ p b n x).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
        norm_nodeSummand_le l m r L γ δ p b n x hs.2)
  have hsum : Summable fun x => ∫ s in Ioc (p : ℝ) t, ‖nodeSummand l m r L γ δ p b n x s‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg fun _ => norm_nonneg _) (fun x => ?_)
      (((summable_nodeWeight l m r hb n).mul_left C).mul_left (volume.real (Ioc (p : ℝ) t)))
    calc ∫ s in Ioc (p : ℝ) t, ‖nodeSummand l m r L γ δ p b n x s‖
        ≤ ∫ _ in Ioc (p : ℝ) t, C * nodeWeight l m r b n x :=
          setIntegral_mono_on (hint x).norm (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc fun s hs => norm_nodeSummand_le l m r L γ δ p b n x hs.2
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [intervalIntegral.integral_of_le ht]
  simp only [intervalIntegral.integral_of_le ht]
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

/-! ### Step 3: one decoration of `node l m r` -/

theorem integral_nodeSummand_decSplit (p : ℕ) (b : (Fin d → ℤ) → ℂ) {t : ℝ} (ht : (p : ℝ) ≤ t)
    (n : Fin d → ℤ) (κ : TreeDecoration (TTree.node l m r) d n) :
    (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
        ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r)) *
        ∫ s in (p : ℝ)..t, nodeSummand l m r L γ δ p b n (decSplit l m r n κ) s =
      treePrefactor L γ δ d (TTree.node l m r) * treeSummand L γ δ p (TTree.node l m r) b t n κ := by
  rw [← treePrefactor_node]
  congr 1
  have hc2 : n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1) =
      κ.1 ((rootB l m r).child 2) := ((decSplit l m r n κ).2.2.2.2.2).symm
  have hn : latticePoint L n = latticePoint L (κ.1 (rootB l m r).toNode) := by
    rw [show κ.1 (rootB l m r).toNode = n from κ.2.2]
  have hE : ∀ s, pairFactor L γ δ n (decSplit l m r n κ).1 s =
      (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
        (κ.1 ((rootB l m r).child 2)) : ℂ) * rootPhase l m r L γ δ κ.1 s := by
    intro s
    show (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
        (n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1)) : ℂ) *
      Complex.exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
        resFactor (latticePoint L (κ.1 ((rootB l m r).child 0)))
          (latticePoint L (κ.1 ((rootB l m r).child 1)))
          (latticePoint L (n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1)))
          (latticePoint L n) * s : ℝ) : ℂ) * Complex.I) = _
    rw [hc2, hn]
    simp only [rootPhase, Int.cast_one, one_mul]
  set κl := (isSubtreeAt_left l m r).res κ.1
  set κm := (isSubtreeAt_mid l m r).res κ.1
  set κr := (isSubtreeAt_right l m r).res κ.1
  set Cst := (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
      (κ.1 ((rootB l m r).child 2)) : ℂ) * (epsProd l κl * (epsProd m κm * epsProd r κr)) *
    (leafProd l b κl * ((starRingEnd ℂ) (leafProd m b κm) * leafProd r b κr))
  have hpt : ∀ s, nodeSummand l m r L γ δ p b n (decSplit l m r n κ) s =
      Cst * (rootPhase l m r L γ δ κ.1 s * (timeInt L γ δ l κl p s *
        ((starRingEnd ℂ) (timeInt L γ δ m κm p s) * timeInt L γ δ r κr p s))) := by
    intro s
    unfold nodeSummand
    rw [hE]
    simp only [treeSummand_eq]
    rw [map_mul, map_mul, conj_epsProd]
    show _ * (epsProd l κl * timeInt L γ δ l κl p s * leafProd l b κl *
      (epsProd m κm * (starRingEnd ℂ) (timeInt L γ δ m κm p s) * (starRingEnd ℂ) (leafProd m b κm) *
        (epsProd r κr * timeInt L γ δ r κr p s * leafProd r b κr))) = _
    ring
  rw [intervalIntegral.integral_congr fun s _ => hpt s, intervalIntegral.integral_const_mul,
    ← timeInt_node l m r L γ δ κ.1 ht, treeSummand_eq, epsProd_node, leafProd_node]
  ring

/-! ### The root splitting -/

/-- **Obligation O-TR1, proved** (T (defjt), (defjn)): for `t ≥ p` and summable data, the tree term of
`node l m r` is the Duhamel integral of `𝒞₊` of the tree terms of `l`, `m`, `r`. -/
theorem treeTerm_node (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) {t : ℝ}
    (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    treeTerm L γ δ p (TTree.node l m r) b t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTerm L γ δ p l b s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b s k)) (treeTerm L γ δ p r b s) n := by
  set K := (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
    ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r))
  symm
  calc ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTerm L γ δ p l b s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b s k)) (treeTerm L γ δ p r b s) n
      = ∫ s in (p : ℝ)..t, K * ∑' x, nodeSummand l m r L γ δ p b n x s :=
        intervalIntegral.integral_congr fun s _ => aNonlin_treeTerms_eq l m r L γ δ p hb s n
    _ = K * ∑' x, ∫ s in (p : ℝ)..t, nodeSummand l m r L γ δ p b n x s := by
        rw [intervalIntegral.integral_const_mul, integral_tsum_nodeSummand l m r L γ δ p hb ht n]
    _ = ∑' κ : TreeDecoration (TTree.node l m r) d n,
          K * ∫ s in (p : ℝ)..t, nodeSummand l m r L γ δ p b n (decSplit l m r n κ) s := by
        rw [← tsum_mul_left]
        exact ((decSplit l m r n).tsum_eq
          (fun x => K * ∫ s in (p : ℝ)..t, nodeSummand l m r L γ δ p b n x s)).symm
    _ = ∑' κ : TreeDecoration (TTree.node l m r) d n,
          treePrefactor L γ δ d (TTree.node l m r) * treeSummand L γ δ p (TTree.node l m r) b t n κ :=
        tsum_congr fun κ => integral_nodeSummand_decSplit l m r L γ δ p b ht n κ
    _ = treeTerm L γ δ p (TTree.node l m r) b t n := by
        rw [tsum_mul_left]
        rfl

end Node

end WaveTurbulence.SysAPI
