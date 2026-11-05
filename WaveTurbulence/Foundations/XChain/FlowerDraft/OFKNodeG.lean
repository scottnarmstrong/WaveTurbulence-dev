/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKTreeG

/-!
# O-FK, part 2: the root splitting of `treeTermG`

`treeTermG_node`: for `t ≥ p`,
`𝒥^G_{node l m r}(t)_n = ∫_p^t 𝒞₊(𝒥^G_l(s), 𝒥̄^G_m(s), 𝒥^G_r(s))_n ds`.
Each subtree carries the restricted leaf data. This generalizes `treeTerm_node` (O-TR1) to leaf inputs depending on
the parent's time, and the proof follows the same four steps.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

/-! ## Summands and weights -/

/-- The decoration summand of `treeTermG`. -/
noncomputable def treeSummandG (p : ℕ) (T : TTree) (D : LeafData T d) (t : ℝ) (n : Fin d → ℤ)
    (κ : TreeDecoration T d n) : ℂ :=
  epsProd T κ.1 * timeIntG L γ δ T κ.1 D p t

theorem treeTermG_eq (p : ℕ) (T : TTree) (D : LeafData T d) (t : ℝ) (n : Fin d → ℤ) :
    treeTermG L γ δ p T D t n = treePrefactor L γ δ d T * ∑' κ, treeSummandG L γ δ p T D t n κ := rfl

theorem norm_treeSummandG_le (p : ℕ) (T : TTree) (D : LeafData T d) (t : ℝ) (n : Fin d → ℤ)
    (κ : TreeDecoration T d n) :
    ‖treeSummandG L γ δ p T D t n κ‖ ≤ boxVol T p t * leafBound T D κ.1 := by
  unfold treeSummandG
  rw [norm_mul]
  calc ‖epsProd T κ.1‖ * ‖timeIntG L γ δ T κ.1 D p t‖ ≤ 1 * (boxVol T p t * leafBound T D κ.1) :=
        mul_le_mul (norm_epsProd_le T κ.1) (norm_timeIntG_le L γ δ T κ.1 D p t) (norm_nonneg _)
          zero_le_one
    _ = _ := one_mul _

theorem summable_leafBound (T : TTree) (D : LeafData T d) (n : Fin d → ℤ) :
    Summable fun κ : TreeDecoration T d n => leafBound T D κ.1 := by
  classical
  let Φ : TreeDecoration T d n → (GLeaf (single T) → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.toNode
  have hΦ : Function.Injective Φ := fun κ κ' h =>
    Subtype.ext (treeDecoration_eq_of_leaves κ κ' fun ℓ => congrFun h ℓ)
  exact (summable_pi_prod D.U (fun ℓ k => D.nonneg ℓ k) D.summ).comp_injective hΦ

theorem summable_treeSummandG (p : ℕ) (T : TTree) (D : LeafData T d) (t : ℝ) (n : Fin d → ℤ) :
    Summable fun κ : TreeDecoration T d n => ‖treeSummandG L γ δ p T D t n κ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => norm_treeSummandG_le L γ δ p T D t n κ)
    ((summable_leafBound T D n).mul_left _)

section Node

variable (l m r : TTree)

/-- The weight of a joint decoration. -/
noncomputable def nodeWeightG (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) : ℝ :=
  leafBound l (D.res (isSubtreeAt_left l m r)) x.2.1.1 *
    (leafBound m (D.res (isSubtreeAt_mid l m r)) x.2.2.1.1 *
      leafBound r (D.res (isSubtreeAt_right l m r)) x.2.2.2.1)

theorem summable_nodeWeightG (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ) :
    Summable (nodeWeightG l m r D n) := by
  refine (decSplit l m r n).summable_iff.1 ?_
  convert summable_leafBound (TTree.node l m r) D n using 1
  funext κ
  show nodeWeightG l m r D n (decSplit l m r n κ) = _
  unfold leafBound
  rw [prod_gLeaf_node (M := ℝ)]
  rfl

theorem nodeWeightG_nonneg (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) : 0 ≤ nodeWeightG l m r D n x :=
  mul_nonneg (leafBound_nonneg _ _ _) (mul_nonneg (leafBound_nonneg _ _ _) (leafBound_nonneg _ _ _))

/-- The joint summand. -/
noncomputable def nodeSummandG (p : ℕ) (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) (s : ℝ) : ℂ :=
  pairFactor L γ δ n x.1 s * (treeSummandG L γ δ p l (D.res (isSubtreeAt_left l m r)) s x.1.1 x.2.1 *
    ((starRingEnd ℂ) (treeSummandG L γ δ p m (D.res (isSubtreeAt_mid l m r)) s x.1.2 x.2.2.1) *
      treeSummandG L γ δ p r (D.res (isSubtreeAt_right l m r)) s (n - x.1.1 + x.1.2) x.2.2.2))

theorem norm_nodeSummandG_le (p : ℕ) (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ)
    (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) {s t : ℝ} (hst : s ≤ t) :
    ‖nodeSummandG L γ δ l m r p D n x s‖ ≤
      boxVol l p t * (boxVol m p t * boxVol r p t) * nodeWeightG l m r D n x := by
  unfold nodeSummandG nodeWeightG
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
  have h1 := norm_treeSummandG_le L γ δ p l (D.res (isSubtreeAt_left l m r)) s x.1.1 x.2.1
  have h2 := norm_treeSummandG_le L γ δ p m (D.res (isSubtreeAt_mid l m r)) s x.1.2 x.2.2.1
  have h3 := norm_treeSummandG_le L γ δ p r (D.res (isSubtreeAt_right l m r)) s
    (n - x.1.1 + x.1.2) x.2.2.2
  have hb1 := boxVol_mono l (p : ℝ) hst
  have hb2 := boxVol_mono m (p : ℝ) hst
  have hb3 := boxVol_mono r (p : ℝ) hst
  have hE := norm_pairFactor_le L γ δ n x.1 s
  have P1 := leafBound_nonneg l (D.res (isSubtreeAt_left l m r)) x.2.1.1
  have P2 := leafBound_nonneg m (D.res (isSubtreeAt_mid l m r)) x.2.2.1.1
  have P3 := leafBound_nonneg r (D.res (isSubtreeAt_right l m r)) x.2.2.2.1
  have B1 := boxVol_nonneg l (p : ℝ) s
  have B2 := boxVol_nonneg m (p : ℝ) s
  have B3 := boxVol_nonneg r (p : ℝ) s
  calc _ ≤ 1 * ((boxVol l p s * leafBound l (D.res (isSubtreeAt_left l m r)) x.2.1.1) *
        ((boxVol m p s * leafBound m (D.res (isSubtreeAt_mid l m r)) x.2.2.1.1) *
          (boxVol r p s * leafBound r (D.res (isSubtreeAt_right l m r)) x.2.2.2.1))) := by
        gcongr
    _ ≤ 1 * ((boxVol l p t * leafBound l (D.res (isSubtreeAt_left l m r)) x.2.1.1) *
        ((boxVol m p t * leafBound m (D.res (isSubtreeAt_mid l m r)) x.2.2.1.1) *
          (boxVol r p t * leafBound r (D.res (isSubtreeAt_right l m r)) x.2.2.2.1))) := by
        gcongr
        all_goals exact mul_nonneg (boxVol_nonneg _ _ _) (leafBound_nonneg _ _ _)
    _ = _ := by ring

theorem summable_nodeSummandG (p : ℕ) (D : LeafData (TTree.node l m r) d) (n : Fin d → ℤ) (s : ℝ) :
    Summable fun x => nodeSummandG L γ δ l m r p D n x s :=
  Summable.of_norm_bounded ((summable_nodeWeightG l m r D n).mul_left _)
    fun x => norm_nodeSummandG_le L γ δ l m r p D n x le_rfl

/-! ## Step 1: for each time, one absolutely convergent sum -/

theorem aNonlin_treeTermsG_eq (p : ℕ) (D : LeafData (TTree.node l m r) d) (s : ℝ) (n : Fin d → ℤ) :
    aNonlin L γ δ 1 s (treeTermG L γ δ p l (D.res (isSubtreeAt_left l m r)) s)
        (fun k => (starRingEnd ℂ) (treeTermG L γ δ p m (D.res (isSubtreeAt_mid l m r)) s k))
        (treeTermG L γ δ p r (D.res (isSubtreeAt_right l m r)) s) n =
      (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
        ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r)) *
        ∑' x, nodeSummandG L γ δ l m r p D n x s := by
  set Dl := D.res (isSubtreeAt_left l m r)
  set Dm := D.res (isSubtreeAt_mid l m r)
  set Dr := D.res (isSubtreeAt_right l m r)
  set P := treePrefactor L γ δ d l * ((starRingEnd ℂ) (treePrefactor L γ δ d m) *
    treePrefactor L γ δ d r)
  have hq : ∀ q : (Fin d → ℤ) × (Fin d → ℤ),
      aNonlinTerm L γ δ 1 s (treeTermG L γ δ p l Dl s)
        (fun k => (starRingEnd ℂ) (treeTermG L γ δ p m Dm s k)) (treeTermG L γ δ p r Dr s) n q =
      P * ∑' y : DecFiber l m r n q, nodeSummandG L γ δ l m r p D n ⟨q, y⟩ s := by
    intro q
    rw [aNonlinTerm_eq]
    simp only [treeTermG_eq]
    rw [map_mul, Complex.conj_tsum]
    have ha := summable_treeSummandG L γ δ p l Dl s q.1
    have hb' : Summable fun κ : TreeDecoration m d q.2 =>
        ‖(starRingEnd ℂ) (treeSummandG L γ δ p m Dm s q.2 κ)‖ := by
      simpa using summable_treeSummandG L γ δ p m Dm s q.2
    have hc := summable_treeSummandG L γ δ p r Dr s (n - q.1 + q.2)
    have hbc := tsum_mul_tsum_of_summable_norm hb' hc
    have hbc' : Summable fun w : TreeDecoration m d q.2 × TreeDecoration r d (n - q.1 + q.2) =>
        ‖(starRingEnd ℂ) (treeSummandG L γ δ p m Dm s q.2 w.1) *
          treeSummandG L γ δ p r Dr s (n - q.1 + q.2) w.2‖ := by
      simp only [norm_mul]
      exact summable_mul_of_summable_norm (f := fun κ => ‖(starRingEnd ℂ)
        (treeSummandG L γ δ p m Dm s q.2 κ)‖) (g := fun κ => ‖treeSummandG L γ δ p r Dr s
          (n - q.1 + q.2) κ‖) (by simpa using hb') (by simpa using hc)
    have habc := tsum_mul_tsum_of_summable_norm ha hbc'
    calc pairFactor L γ δ n q s * (treePrefactor L γ δ d l * ∑' κ, treeSummandG L γ δ p l Dl s q.1 κ) *
          ((starRingEnd ℂ) (treePrefactor L γ δ d m) *
            ∑' κ, (starRingEnd ℂ) (treeSummandG L γ δ p m Dm s q.2 κ)) *
          (treePrefactor L γ δ d r * ∑' κ, treeSummandG L γ δ p r Dr s (n - q.1 + q.2) κ)
        = P * (pairFactor L γ δ n q s * ((∑' κ, treeSummandG L γ δ p l Dl s q.1 κ) *
            ((∑' κ, (starRingEnd ℂ) (treeSummandG L γ δ p m Dm s q.2 κ)) *
              ∑' κ, treeSummandG L γ δ p r Dr s (n - q.1 + q.2) κ))) := by ring
      _ = P * ∑' y : DecFiber l m r n q, nodeSummandG L γ δ l m r p D n ⟨q, y⟩ s := by
        rw [hbc, habc, ← tsum_mul_left]
        rfl
  rw [aNonlin_eq_tsum_aNonlinTerm, tsum_congr hq, tsum_mul_left,
    (summable_nodeSummandG L γ δ l m r p D n s).tsum_sigma]
  unfold coupling
  ring

/-! ## Step 2: the sum commutes with the time integral -/

theorem stronglyMeasurable_nodeSummandG (p : ℕ) (D : LeafData (TTree.node l m r) d)
    (n : Fin d → ℤ) (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) :
    StronglyMeasurable fun s => nodeSummandG L γ δ l m r p D n x s := by
  unfold nodeSummandG treeSummandG
  have hl := stronglyMeasurable_timeIntG L γ δ l x.2.1.1 (D.res (isSubtreeAt_left l m r)) p
  have hm := stronglyMeasurable_timeIntG L γ δ m x.2.2.1.1 (D.res (isSubtreeAt_mid l m r)) p
  have hr := stronglyMeasurable_timeIntG L γ δ r x.2.2.2.1 (D.res (isSubtreeAt_right l m r)) p
  exact (continuous_pairFactor L γ δ n x.1).stronglyMeasurable.mul
    ((stronglyMeasurable_const.mul hl).mul
      ((Complex.continuous_conj.comp_stronglyMeasurable (stronglyMeasurable_const.mul hm)).mul
        (stronglyMeasurable_const.mul hr)))

theorem integral_tsum_nodeSummandG (p : ℕ) (D : LeafData (TTree.node l m r) d) {t : ℝ}
    (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    ∫ s in (p : ℝ)..t, ∑' x, nodeSummandG L γ δ l m r p D n x s =
      ∑' x, ∫ s in (p : ℝ)..t, nodeSummandG L γ δ l m r p D n x s := by
  set C := boxVol l p t * (boxVol m p t * boxVol r p t)
  have hint : ∀ x, IntegrableOn (fun s => nodeSummandG L γ δ l m r p D n x s) (Ioc (p : ℝ) t) :=
    fun x => Measure.integrableOn_of_bounded (M := C * nodeWeightG l m r D n x)
      measure_Ioc_lt_top.ne
      (stronglyMeasurable_nodeSummandG L γ δ l m r p D n x).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
        norm_nodeSummandG_le L γ δ l m r p D n x hs.2)
  have hsum : Summable fun x => ∫ s in Ioc (p : ℝ) t, ‖nodeSummandG L γ δ l m r p D n x s‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg fun _ => norm_nonneg _) (fun x => ?_)
      (((summable_nodeWeightG l m r D n).mul_left C).mul_left (volume.real (Ioc (p : ℝ) t)))
    calc ∫ s in Ioc (p : ℝ) t, ‖nodeSummandG L γ δ l m r p D n x s‖
        ≤ ∫ _ in Ioc (p : ℝ) t, C * nodeWeightG l m r D n x :=
          setIntegral_mono_on (hint x).norm (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc fun s hs => norm_nodeSummandG_le L γ δ l m r p D n x hs.2
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [intervalIntegral.integral_of_le ht]
  simp only [intervalIntegral.integral_of_le ht]
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

/-! ## Step 3: one decoration of `node l m r` -/

theorem integral_nodeSummandG_decSplit (p : ℕ) (D : LeafData (TTree.node l m r) d) {t : ℝ}
    (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) (κ : TreeDecoration (TTree.node l m r) d n) :
    (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
        ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r)) *
        ∫ s in (p : ℝ)..t, nodeSummandG L γ δ l m r p D n (decSplit l m r n κ) s =
      treePrefactor L γ δ d (TTree.node l m r) * treeSummandG L γ δ p (TTree.node l m r) D t n κ := by
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
  set Dl := D.res (isSubtreeAt_left l m r)
  set Dm := D.res (isSubtreeAt_mid l m r)
  set Dr := D.res (isSubtreeAt_right l m r)
  set Cst := (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
      (κ.1 ((rootB l m r).child 2)) : ℂ) * (epsProd l κl * (epsProd m κm * epsProd r κr))
  have hpt : ∀ s, nodeSummandG L γ δ l m r p D n (decSplit l m r n κ) s =
      Cst * (rootPhase l m r L γ δ κ.1 s * (timeIntG L γ δ l κl Dl p s *
        ((starRingEnd ℂ) (timeIntG L γ δ m κm Dm p s) * timeIntG L γ δ r κr Dr p s))) := by
    intro s
    unfold nodeSummandG treeSummandG
    rw [hE, map_mul, conj_epsProd]
    show _ * (epsProd l κl * timeIntG L γ δ l κl Dl p s *
      (epsProd m κm * (starRingEnd ℂ) (timeIntG L γ δ m κm Dm p s) *
        (epsProd r κr * timeIntG L γ δ r κr Dr p s))) = _
    ring
  rw [intervalIntegral.integral_congr fun s _ => hpt s, intervalIntegral.integral_const_mul,
    ← timeIntG_node L γ δ l m r D κ.1 ht]
  unfold treeSummandG
  rw [epsProd_node]

/-! ## The root splitting -/

/-- **The root splitting of `treeTermG`.** -/
theorem treeTermG_node (p : ℕ) (D : LeafData (TTree.node l m r) d) {t : ℝ} (ht : (p : ℝ) ≤ t)
    (n : Fin d → ℤ) :
    treeTermG L γ δ p (TTree.node l m r) D t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTermG L γ δ p l (D.res (isSubtreeAt_left l m r)) s)
        (fun k => (starRingEnd ℂ) (treeTermG L γ δ p m (D.res (isSubtreeAt_mid l m r)) s k))
        (treeTermG L γ δ p r (D.res (isSubtreeAt_right l m r)) s) n := by
  set K := (coupling d L γ δ : ℂ) * (Complex.I * ((1 : ℤ) : ℂ)) * (treePrefactor L γ δ d l *
    ((starRingEnd ℂ) (treePrefactor L γ δ d m) * treePrefactor L γ δ d r))
  symm
  calc ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTermG L γ δ p l (D.res (isSubtreeAt_left l m r)) s)
        (fun k => (starRingEnd ℂ) (treeTermG L γ δ p m (D.res (isSubtreeAt_mid l m r)) s k))
        (treeTermG L γ δ p r (D.res (isSubtreeAt_right l m r)) s) n
      = ∫ s in (p : ℝ)..t, K * ∑' x, nodeSummandG L γ δ l m r p D n x s :=
        intervalIntegral.integral_congr fun s _ => aNonlin_treeTermsG_eq L γ δ l m r p D s n
    _ = K * ∑' x, ∫ s in (p : ℝ)..t, nodeSummandG L γ δ l m r p D n x s := by
        rw [intervalIntegral.integral_const_mul, integral_tsum_nodeSummandG L γ δ l m r p D ht n]
    _ = ∑' κ : TreeDecoration (TTree.node l m r) d n,
          K * ∫ s in (p : ℝ)..t, nodeSummandG L γ δ l m r p D n (decSplit l m r n κ) s := by
        rw [← tsum_mul_left]
        exact ((decSplit l m r n).tsum_eq
          (fun x => K * ∫ s in (p : ℝ)..t, nodeSummandG L γ δ l m r p D n x s)).symm
    _ = ∑' κ : TreeDecoration (TTree.node l m r) d n,
          treePrefactor L γ δ d (TTree.node l m r) * treeSummandG L γ δ p (TTree.node l m r) D t n κ :=
        tsum_congr fun κ => integral_nodeSummandG_decSplit L γ δ l m r p D ht n κ
    _ = treeTermG L γ δ p (TTree.node l m r) D t n := by
        rw [tsum_mul_left]
        rfl

end Node

end WaveTurbulence.SysAPI
