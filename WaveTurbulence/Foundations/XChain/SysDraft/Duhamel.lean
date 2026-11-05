/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.Kernel

/-!
# D2 SYS-DEFS API, part 3: the Duhamel objects (scratch, snapshot 4)

Lemmas about `treeTerm`, `treeTermN`, `aTr` and the operators `ℒ_j = Lop` (T (defjt), (defjn),
(defbk), (eqnbk1.5)):

* **values**:
  - the leaf term is the datum (`treeTerm_leaf`, `treeTermN_zero`);
  - at times `t ≤ p` every tree of positive order vanishes (`treeTermN_of_le`), so `aTr(p) = a(p)`
    (`aTr_of_le`);
  - `ℒ_j b(p) = 0` (`Lop_self`);
* **summability** (stage-2 audit O2):
  - the decoration sum of `treeTerm` converges absolutely for summable data
    (`summable_treeSummand`);
  - `𝒥_𝒯`, `𝒥_N` and `a^tr` are summable in `n` (`summable_norm_treeTerm`, `…TreeTermN`, `…aTr`);
  - `𝒥_N` is a finite sum over the trees of order `N` (`treeTermN_eq_sum`);
* **the Duhamel identity for `ℒ_j`/`a^tr`** (glue list, stage-3 O6):
  - the integral `∫_p^t 𝒞₊(A, Ā, A)` of `A = a^tr + b` splits into `ℒ₀ b + ℒ₁ b + ℒ₂ b + ℒ₃ b` and
    the low-order `𝒥`-terms (`integral_aNonlin_aFull`);
  - under the tree recursion `𝒥_{K+1}(t) = ∑_{N₁+N₂+N₃=K} ∫_p^t 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})`
    (`TreeRecursion`), the low-order terms are `a^tr(t) - a(p)`. Hence `A = a(p) + ∫_p^t 𝒞₊(A,Ā,A)`
    iff `b = ∑_{j ≤ 3} ℒ_j b` (`duhamel_iff_Lop`);
  - the tree recursion itself is the obligation `treeRecursion` of `Sys-Obligations.lean`;
* `hasDerivWithinAt_of_eq_add_integral`: from the integral form back to the differential form (for
  `IsASolution.glue`).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.SysAPI

/-! ## §1 Trees of order zero, and times `t ≤ p` -/

section Values

variable (L γ δ : ℝ) {d : ℕ}

instance isEmpty_gBranch_single_leaf : IsEmpty (GBranch (single TTree.leaf)) :=
  ⟨fun c => by
    have h := c.2
    simp [single, TTree.branching] at h⟩

theorem gNode_single_leaf_eq_root (a : GNode (single TTree.leaf)) :
    a = GNode.root (single TTree.leaf) 0 := by
  obtain ⟨⟨j, q⟩, hq⟩ := a
  have hq' : q = [] := by simpa [single, TTree.nodes] using hq
  subst hq'
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rfl

theorem treeSign_root (T : TTree) : treeSign T (GNode.root (single T) 0) = 1 := by
  simp [treeSign, nodeSign, TTree.pathSign, GNode.root]

/-- The tree `•` contributes the datum: `𝒥_•(t) = b`. -/
theorem treeTerm_leaf (p : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    treeTerm L γ δ p TTree.leaf b t n = b n := by
  classical
  let κ₀ : TreeDecoration TTree.leaf d n := ⟨fun _ => n, fun c => isEmptyElim c, rfl⟩
  have hsub : ∀ κ : TreeDecoration TTree.leaf d n, κ = κ₀ := fun κ =>
    Subtype.ext (funext fun a => by rw [gNode_single_leaf_eq_root a]; exact κ.2.2)
  have hdom : treeTimeDomain TTree.leaf p t = univ := by
    ext τ
    simp only [treeTimeDomain, mem_ofPred_eq, mem_univ, iff_true]
    exact fun c => isEmptyElim c
  have hint : ∫ τ : GBranch (single TTree.leaf) → ℝ, (univ : Set (GBranch (single TTree.leaf) → ℝ)).indicator
      (fun _ => (1 : ℂ)) τ = 1 := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume)]
    simp
  have hleaf : ∀ ℓ : GLeaf (single TTree.leaf), ℓ.toNode = GNode.root (single TTree.leaf) 0 :=
    fun ℓ => gNode_single_leaf_eq_root _
  have huniq : ∀ ℓ ℓ' : GLeaf (single TTree.leaf), ℓ = ℓ' := fun ℓ ℓ' =>
    Subtype.ext (congrArg Subtype.val ((hleaf ℓ).trans (hleaf ℓ').symm))
  let ℓ₀ : GLeaf (single TTree.leaf) := ⟨(0, []), by simp [single, TTree.leaves]⟩
  unfold treeTerm
  rw [tsum_eq_single κ₀ fun κ hκ => absurd (hsub κ) hκ, hdom]
  simp only [Fintype.prod_empty, mul_one, one_mul, TTree.order, pow_zero, hint]
  rw [Fintype.prod_eq_single ℓ₀ fun ℓ hℓ => absurd (huniq ℓ ℓ₀) hℓ, hleaf, treeSign_root]
  simp [zpowSign, κ₀]

/-- `𝒥_0 = b`. -/
theorem treeTermN_zero (p : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    treeTermN L γ δ p 0 b t n = b n := by
  classical
  unfold treeTermN
  rw [finsum_eq_single _ TTree.leaf fun T hT => ?_]
  · rw [finsum_eq_if]
    simp [TTree.order, treeTerm_leaf]
  · rw [finsum_eq_if]
    split_ifs with h
    · cases T with
      | leaf => exact absurd rfl hT
      | node l m r => simp [TTree.order] at h
    · rfl

theorem treeTimeDomain_eq_empty {T : TTree} (hT : T ≠ TTree.leaf) {p t : ℝ} (ht : t ≤ p) :
    treeTimeDomain T p t = ∅ := by
  obtain ⟨l, m, r, rfl⟩ : ∃ l m r, T = TTree.node l m r := by
    cases T with
    | leaf => exact absurd rfl hT
    | node l m r => exact ⟨l, m, r, rfl⟩
  ext τ
  simp only [treeTimeDomain, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro h
  have h0 := h ⟨(0, []), by simp [single, TTree.branching]⟩
  exact absurd (h0.1.trans h0.2.1) (not_lt.2 ht)

/-- A tree of positive order vanishes at times `t ≤ p`. -/
theorem treeTerm_of_le (p : ℕ) {T : TTree} (hT : T ≠ TTree.leaf) (b : (Fin d → ℤ) → ℂ) {t : ℝ}
    (ht : t ≤ p) (n : Fin d → ℤ) : treeTerm L γ δ p T b t n = 0 := by
  unfold treeTerm
  rw [treeTimeDomain_eq_empty hT ht]
  simp

theorem treeTermN_of_le (p : ℕ) {N : ℕ} (hN : N ≠ 0) (b : (Fin d → ℤ) → ℂ) {t : ℝ} (ht : t ≤ p)
    (n : Fin d → ℤ) : treeTermN L γ δ p N b t n = 0 := by
  classical
  unfold treeTermN
  refine finsum_eq_zero_of_forall_eq_zero fun T => ?_
  rw [finsum_eq_if]
  split_ifs with h
  · refine treeTerm_of_le L γ δ p (fun hT => hN ?_) b ht n
    rw [← h, hT]
    rfl
  · rfl

/-- `a^tr(p) = a(p)` (and likewise at earlier times). -/
theorem aTr_of_le (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) {t : ℝ} (ht : t ≤ p) (n : Fin d → ℤ) :
    aTr L γ δ p Ntr b t n = b n := by
  unfold aTr
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun N _ =>
    treeTermN_of_le L γ δ p (Nat.succ_ne_zero N) b ht n, treeTermN_zero, zero_add]

/-- `ℒ_j b (p) = 0`. -/
theorem Lop_self (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (j : ℕ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr aP j b p n = 0 := by
  unfold Lop
  simp

end Values

/-! ## §2 Summability (stage-2 audit O2) -/

section Summability

variable (L γ δ : ℝ) {d : ℕ}

/-- The decoration summand of `treeTerm`. -/
noncomputable def treeSummand (p : ℕ) (T : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ)
    (κ : TreeDecoration T d n) : ℂ :=
  (∏ c : GBranch (single T),
      (epsCoef (κ.1 (c.child 0)) (κ.1 (c.child 1)) (κ.1 (c.child 2)) : ℂ)) *
    (∫ τ : GBranch (single T) → ℝ, (treeTimeDomain T p t).indicator
      (fun τ => ∏ c : GBranch (single T), Complex.exp ((Real.pi *
        ((treeSign T c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        resFactor (latticePoint L (κ.1 (c.child 0))) (latticePoint L (κ.1 (c.child 1)))
          (latticePoint L (κ.1 (c.child 2))) (latticePoint L (κ.1 c.toNode)) *
        τ c : ℝ) * Complex.I)) τ) *
    ∏ ℓ : GLeaf (single T), zpowSign (treeSign T ℓ.toNode) (b (κ.1 ℓ.toNode))

/-- The prefactor `(δ/(2L^{d-γ}))^{n(𝒯)} ∏_𝔫 (iζ_𝔫)` of `treeTerm`. -/
noncomputable def treePrefactor (d : ℕ) (T : TTree) : ℂ :=
  (coupling d L γ δ : ℂ) ^ T.order *
    ∏ c : GBranch (single T), (Complex.I * (((treeSign T c.toNode : ℤˣ) : ℤ) : ℂ))

theorem treeTerm_eq (p : ℕ) (T : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    treeTerm L γ δ p T b t n =
      treePrefactor L γ δ d T * ∑' κ, treeSummand L γ δ p T b t n κ := rfl

/-- A time integral over `treeTimeDomain` of a function of modulus `≤ 1` is bounded by the volume
of the box `[p, t]^{𝒩}`. -/
theorem norm_integral_treeTimeDomain_le (T : TTree) (p t : ℝ)
    (f : (GBranch (single T) → ℝ) → ℂ) (hf : ∀ τ, ‖f τ‖ ≤ 1) :
    ‖∫ τ, (treeTimeDomain T p t).indicator f τ‖ ≤
      (volume : Measure (GBranch (single T) → ℝ)).real (Set.pi univ fun _ => Icc p t) := by
  set Box : Set (GBranch (single T) → ℝ) := Set.pi univ fun _ => Icc p t
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  rw [← integral_indicator_one hBm]
  refine norm_integral_le_of_norm_le ((integrable_indicator_iff hBm).2
    (integrableOn_const hBc.measure_lt_top.ne)) (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hD : τ ∈ treeTimeDomain T p t
  · have hτ : τ ∈ Box := fun c _ => by
      have h := hD c
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
    exact hf τ
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem norm_zpowSign (ζ : ℤˣ) (z : ℂ) : ‖zpowSign ζ z‖ = ‖z‖ := by
  unfold zpowSign
  split_ifs <;> simp

theorem norm_treeSummand_le (p : ℕ) (T : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ)
    (n : Fin d → ℤ) (κ : TreeDecoration T d n) :
    ‖treeSummand L γ δ p T b t n κ‖ ≤
      (volume : Measure (GBranch (single T) → ℝ)).real (Set.pi univ fun _ => Icc (p : ℝ) t) *
        ∏ ℓ : GLeaf (single T), ‖b (κ.1 ℓ.toNode)‖ := by
  unfold treeSummand
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_zpowSign]
  have h1 : ∏ c : GBranch (single T),
      ‖(epsCoef (κ.1 (c.child 0)) (κ.1 (c.child 1)) (κ.1 (c.child 2)) : ℂ)‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun c _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold epsCoef
    split_ifs <;> simp
  have hP : 0 ≤ ∏ ℓ : GLeaf (single T), ‖b (κ.1 ℓ.toNode)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc _ ≤ 1 * (volume : Measure (GBranch (single T) → ℝ)).real
          (Set.pi univ fun _ => Icc (p : ℝ) t) * ∏ ℓ : GLeaf (single T), ‖b (κ.1 ℓ.toNode)‖ := by
        gcongr
        exact norm_integral_treeTimeDomain_le T p t _ fun τ => by
          rw [norm_prod]
          exact le_of_eq (Finset.prod_eq_one fun c _ => Complex.norm_exp_ofReal_mul_I _)
    _ = _ := by ring

/-- A decoration of a tree is determined by its leaf values. -/
theorem treeDecoration_eq_of_leaves {T : TTree} {n n' : Fin d → ℤ} (κ : TreeDecoration T d n)
    (κ' : TreeDecoration T d n') (h : ∀ ℓ : GLeaf (single T), κ.1 ℓ.toNode = κ'.1 ℓ.toNode) :
    κ.1 = κ'.1 := by
  funext a
  refine sub_eq_zero.1 (eq_zero_of_leaves_zero (fun a => κ.1 a - κ'.1 a) (fun c => ?_) a
    fun ℓ _ => sub_eq_zero.2 (h ℓ))
  simp only [κ.2.1 c, κ'.2.1 c]
  abel

/-- **Obligation O2 (stage-2 audit), proved.** The decoration sum of `treeTerm` converges
absolutely for data with summable norms. -/
theorem summable_treeSummand (p : ℕ) (T : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (t : ℝ) (n : Fin d → ℤ) :
    Summable fun κ : TreeDecoration T d n => ‖treeSummand L γ δ p T b t n κ‖ := by
  classical
  let Φ : TreeDecoration T d n → (GLeaf (single T) → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.toNode
  have hΦ : Function.Injective Φ := fun κ κ' h =>
    Subtype.ext (treeDecoration_eq_of_leaves κ κ' fun ℓ => congrFun h ℓ)
  have hf := summable_pi_prod (fun (_ : GLeaf (single T)) m => ‖b m‖) (fun _ _ => norm_nonneg _)
    fun _ => hb
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_treeSummand_le L γ δ p T b t n κ) ((hf.comp_injective hΦ).mul_left _)

/-- `𝒥_𝒯(t)` is summable in `n` for data with summable norms. -/
theorem summable_norm_treeTerm (p : ℕ) (T : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (t : ℝ) :
    Summable fun n => ‖treeTerm L γ δ p T b t n‖ := by
  classical
  set C := (volume : Measure (GBranch (single T) → ℝ)).real (Set.pi univ fun _ => Icc (p : ℝ) t)
  let g : (Σ n : Fin d → ℤ, TreeDecoration T d n) → ℝ := fun x =>
    ∏ ℓ : GLeaf (single T), ‖b (x.2.1 ℓ.toNode)‖
  let Ψ : (Σ n : Fin d → ℤ, TreeDecoration T d n) → (GLeaf (single T) → (Fin d → ℤ)) :=
    fun x ℓ => x.2.1 ℓ.toNode
  have hΨ : Function.Injective Ψ := by
    rintro ⟨n, κ⟩ ⟨n', κ'⟩ h
    have hκ : κ.1 = κ'.1 := treeDecoration_eq_of_leaves κ κ' fun ℓ => congrFun h ℓ
    have hn : n = n' := κ.2.2.symm.trans ((congrFun hκ _).trans κ'.2.2)
    subst hn
    have hκκ : κ = κ' := Subtype.ext hκ
    subst hκκ
    rfl
  have hg : Summable g := (summable_pi_prod (fun (_ : GLeaf (single T)) m => ‖b m‖)
    (fun _ _ => norm_nonneg _) fun _ => hb).comp_injective hΨ
  have hg0 : ∀ x, 0 ≤ g x := fun x => Finset.prod_nonneg fun _ _ => norm_nonneg _
  obtain ⟨hgκ, hgn⟩ := (summable_sigma_of_nonneg hg0).1 hg
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((hgn.mul_left C).mul_left ‖treePrefactor L γ δ d T‖)
  rw [treeTerm_eq, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑' κ, treeSummand L γ δ p T b t n κ‖
      ≤ ∑' κ, ‖treeSummand L γ δ p T b t n κ‖ :=
        norm_tsum_le_tsum_norm (summable_treeSummand L γ δ p T hb t n)
    _ ≤ ∑' κ : TreeDecoration T d n, C * g ⟨n, κ⟩ :=
        Summable.tsum_le_tsum (fun κ => norm_treeSummand_le L γ δ p T b t n κ)
          (summable_treeSummand L γ δ p T hb t n) ((hgκ n).mul_left C)
    _ = C * ∑' κ : TreeDecoration T d n, g ⟨n, κ⟩ := tsum_mul_left

theorem finite_order_eq (N : ℕ) : {T : TTree | T.order = N}.Finite :=
  (Canon.finite_order_le N).subset fun _ hT => le_of_eq hT

/-- The (finitely many) trees of order `N`. -/
noncomputable def treesOfOrder (N : ℕ) : Finset TTree := (finite_order_eq N).toFinset

theorem mem_treesOfOrder {N : ℕ} {T : TTree} : T ∈ treesOfOrder N ↔ T.order = N := by
  simp [treesOfOrder]

/-- `𝒥_N` as a finite sum over the trees of order `N`. -/
theorem treeTermN_eq_sum (p N : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    treeTermN L γ δ p N b t n = ∑ T ∈ treesOfOrder N, treeTerm L γ δ p T b t n := by
  unfold treeTermN treesOfOrder
  rw [← finsum_mem_eq_finite_toFinset_sum _ (finite_order_eq N)]
  rfl

theorem summable_norm_treeTermN (p N : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (t : ℝ) : Summable fun n => ‖treeTermN L γ δ p N b t n‖ := by
  simp only [treeTermN_eq_sum]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_sum_le _ _)
    (summable_sum fun T _ => summable_norm_treeTerm L γ δ p T hb t)

theorem summable_norm_aTr (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (t : ℝ) : Summable fun n => ‖aTr L γ δ p Ntr b t n‖ := by
  unfold aTr
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_sum_le _ _)
    (summable_sum fun N _ => summable_norm_treeTermN L γ δ p N hb t)

end Summability

/-! ## §3 The Duhamel identity for `ℒ_j` / `a^tr` -/

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- The slot values of `ℒ_j`: `none ↦ b` (extended from `[p, p+1]`), `some N ↦ 𝒥_N`. -/
noncomputable def slotVal (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) : Slot Ntr → ℝ → (Fin d → ℤ) → ℂ :=
  fun o s => match o with
    | none => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s
    | some N => treeTermN L γ δ p N aP s

theorem Lop_eq_sum (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (j : ℕ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr aP j b t n =
      ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
          (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)),
        ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
          (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
          (slotVal L γ δ p Ntr aP b x.2.2 s) n := rfl

/-- `a^tr + b` as the sum of all slot values. -/
theorem aTr_add_eq_sum_slotVal (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (s : ℝ) (m : Fin d → ℤ) :
    aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m =
      ∑ o : Slot Ntr, slotVal L γ δ p Ntr aP b o s m := by
  rw [Fintype.sum_option]
  simp only [slotVal, aTr]
  rw [Fin.sum_univ_eq_sum_range (fun N => treeTermN L γ δ p N aP s m) (Ntr + 1), add_comm]

theorem summable_slotVal (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun m => ‖aP m‖)
    {b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ} (hb : ∀ s, Summable fun m => ‖b s m‖)
    (o : Slot Ntr) (s : ℝ) : Summable fun m => ‖slotVal L γ δ p Ntr aP b o s m‖ := by
  cases o with
  | none => exact hb _
  | some N => exact summable_norm_treeTermN L γ δ p N haP s

/-- Pointwise expansion of `𝒞₊(A, Ā, A)`, `A = a^tr + b`, into the `(Ntr + 2)³` slot triples. -/
theorem aNonlin_aTr_add_eq_sum (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (s : ℝ) (n : Fin d → ℤ)
    (hsum : ∀ o : Slot Ntr, Summable fun m => ‖slotVal L γ δ p Ntr aP b o s m‖) :
    aNonlin L γ δ 1 s
        (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
        (fun m => (starRingEnd ℂ)
          (aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m))
        (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
        n =
      ∑ x : Slot Ntr × Slot Ntr × Slot Ntr, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
        (slotVal L γ δ p Ntr aP b x.2.2 s) n := by
  simp only [aTr_add_eq_sum_slotVal, map_sum]
  rw [aNonlin_sum L γ δ 1 s univ univ univ (fun o => slotVal L γ δ p Ntr aP b o s)
    (fun o m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b o s m))
    (fun o => slotVal L γ δ p Ntr aP b o s) hsum (fun o => by simpa using hsum o) hsum n]
  simp only [Fintype.sum_prod_type]

theorem slotCountB_le (Ntr : ℕ) (x : Slot Ntr × Slot Ntr × Slot Ntr) : slotCountB x ≤ 3 := by
  unfold slotCountB
  exact (List.count_le_length ..).trans (by simp)

/-- The slot triples split into `ℒ₀, …, ℒ₃` and the low-order `𝒥`-triples. -/
theorem sum_slot_partition {M : Type*} [AddCommMonoid M] (Ntr : ℕ)
    (F : Slot Ntr × Slot Ntr × Slot Ntr → M) :
    ∑ x, F x = ∑ j ∈ range 4, ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)), F x +
      ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = 0 ∧ slotOrder x < Ntr), F x := by
  have hpt : ∀ x, F x = ∑ j ∈ range 4,
      (if slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x) then F x else 0) +
      (if slotCountB x = 0 ∧ slotOrder x < Ntr then F x else 0) := by
    intro x
    have h3 := slotCountB_le Ntr x
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    by_cases ho : Ntr ≤ slotOrder x
    · obtain h | h | h | h : slotCountB x = 0 ∨ slotCountB x = 1 ∨ slotCountB x = 2 ∨
          slotCountB x = 3 := by omega
      all_goals simp [h, ho, not_lt.2 ho]
    · obtain h | h | h | h : slotCountB x = 0 ∨ slotCountB x = 1 ∨ slotCountB x = 2 ∨
          slotCountB x = 3 := by omega
      all_goals simp [h, ho, not_le.1 ho]
  calc ∑ x, F x = ∑ x, (∑ j ∈ range 4,
          (if slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x) then F x else 0) +
          (if slotCountB x = 0 ∧ slotOrder x < Ntr then F x else 0)) :=
        Finset.sum_congr rfl fun x _ => hpt x
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [Finset.sum_filter]

theorem slotCountB_eq_zero {Ntr : ℕ} {x : Slot Ntr × Slot Ntr × Slot Ntr}
    (hx : slotCountB x = 0) : ∃ a b c : Fin (Ntr + 1), x = (some a, some b, some c) := by
  rcases x with ⟨_ | a, _ | b, _ | c⟩ <;> simp [slotCountB] at hx
  exact ⟨a, b, c, rfl⟩

theorem slotOrder_some {Ntr : ℕ} (a b c : Fin (Ntr + 1)) :
    slotOrder ((some a, some b, some c) : Slot Ntr × Slot Ntr × Slot Ntr) =
      (a : ℕ) + (b : ℕ) + (c : ℕ) := by
  simp [slotOrder, add_assoc]

/-- The slot index of an order `k ≤ Ntr`. -/
def slotIdx (Ntr k : ℕ) : Fin (Ntr + 1) := ⟨k % (Ntr + 1), Nat.mod_lt _ Ntr.succ_pos⟩

theorem slotIdx_val {Ntr k : ℕ} (hk : k < Ntr + 1) : (slotIdx Ntr k : ℕ) = k :=
  Nat.mod_eq_of_lt hk

theorem slotIdx_self {Ntr : ℕ} (a : Fin (Ntr + 1)) : slotIdx Ntr a = a :=
  Fin.ext (slotIdx_val a.2)

/-- Reindexing the low-order `𝒥`-triples by their total order. -/
theorem sum_low_slots {M : Type*} [AddCommMonoid M] (Ntr : ℕ)
    (F : Slot Ntr × Slot Ntr × Slot Ntr → M) :
    ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = 0 ∧ slotOrder x < Ntr), F x =
      ∑ K ∈ range Ntr, ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
        (fun y => y.1 + y.2.1 + y.2.2 = K),
          F (some (slotIdx Ntr y.1), some (slotIdx Ntr y.2.1), some (slotIdx Ntr y.2.2)) := by
  set S := (range Ntr ×ˢ range Ntr ×ˢ range Ntr).filter (fun y => y.1 + y.2.1 + y.2.2 < Ntr)
  have hfib : ∀ K ∈ range Ntr, (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
      (fun y => y.1 + y.2.1 + y.2.2 = K) = S.filter (fun y => y.1 + y.2.1 + y.2.2 = K) := by
    intro K hK
    rw [Finset.mem_range] at hK
    ext y
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hmaps : ∀ y ∈ S, (fun y : ℕ × ℕ × ℕ => y.1 + y.2.1 + y.2.2) y ∈ range Ntr := fun y hy => by
    simp only [S, Finset.mem_filter] at hy
    exact Finset.mem_range.2 hy.2
  have hR : ∑ K ∈ range Ntr, ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
        (fun y => y.1 + y.2.1 + y.2.2 = K),
          F (some (slotIdx Ntr y.1), some (slotIdx Ntr y.2.1), some (slotIdx Ntr y.2.2)) =
      ∑ y ∈ S, F (some (slotIdx Ntr y.1), some (slotIdx Ntr y.2.1), some (slotIdx Ntr y.2.2)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    exact Finset.sum_congr rfl fun K hK => by rw [hfib K hK]
  rw [hR]
  refine Finset.sum_nbij'
    (fun x => (x.1.elim 0 Fin.val, x.2.1.elim 0 Fin.val, x.2.2.elim 0 Fin.val))
    (fun y => (some (slotIdx Ntr y.1), some (slotIdx Ntr y.2.1), some (slotIdx Ntr y.2.2)))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, b, c, rfl⟩ := slotCountB_eq_zero hx.1
    have ho := hx.2
    rw [slotOrder_some] at ho
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Option.elim_some]
    omega
  · intro y hy
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simp [slotCountB], ?_⟩
    rw [slotOrder_some, slotIdx_val (by omega), slotIdx_val (by omega), slotIdx_val (by omega)]
    exact hy.2
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, b, c, rfl⟩ := slotCountB_eq_zero hx.1
    simp [slotIdx_self]
  · intro y hy
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    simp only [Option.elim_some]
    rw [slotIdx_val (by omega), slotIdx_val (by omega), slotIdx_val (by omega)]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, b, c, rfl⟩ := slotCountB_eq_zero hx.1
    simp [slotIdx_self]

/-- **The tree recursion** `𝒥_{K+1}(t) = ∑_{N₁+N₂+N₃=K} ∫_p^t 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})(s) ds`
(T (defjt), (defjn): splitting a tree at its root) at the time `t` and mode `n`, for all `K`.
The obligation `treeRecursion` (`Sys-Obligations.lean`) states it for summable data and `t ≥ p`. -/
def TreeRecursion (p : ℕ) (aP : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : Prop :=
  ∀ K : ℕ, treeTermN L γ δ p (K + 1) aP t n =
    ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
        (fun y => y.1 + y.2.1 + y.2.2 = K),
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTermN L γ δ p y.1 aP s)
        (fun m => (starRingEnd ℂ) (treeTermN L γ δ p y.2.1 aP s m)) (treeTermN L γ δ p y.2.2 aP s) n

/-- Under the tree recursion, the low-order `𝒥`-triples give `a^tr(t) - a(p)`. -/
theorem sum_low_eq_aTr_sub (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ)
    (hrec : TreeRecursion L γ δ p aP t n) :
    ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = 0 ∧ slotOrder x < Ntr),
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
        (slotVal L γ δ p Ntr aP b x.2.2 s) n =
      aTr L γ δ p Ntr aP t n - aP n := by
  rw [sum_low_slots]
  have hK : ∀ K ∈ range Ntr, ∑ y ∈ (range (K + 1) ×ˢ range (K + 1) ×ˢ range (K + 1)).filter
      (fun y => y.1 + y.2.1 + y.2.2 = K),
        ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s
          (slotVal L γ δ p Ntr aP b (some (slotIdx Ntr y.1)) s)
          (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b (some (slotIdx Ntr y.2.1)) s m))
          (slotVal L γ δ p Ntr aP b (some (slotIdx Ntr y.2.2)) s) n =
      treeTermN L γ δ p (K + 1) aP t n := by
    intro K hK
    rw [Finset.mem_range] at hK
    rw [hrec K]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    have e1 : (slotIdx Ntr y.1 : ℕ) = y.1 := slotIdx_val (by omega)
    have e2 : (slotIdx Ntr y.2.1 : ℕ) = y.2.1 := slotIdx_val (by omega)
    have e3 : (slotIdx Ntr y.2.2 : ℕ) = y.2.2 := slotIdx_val (by omega)
    simp only [slotVal, e1, e2, e3]
  rw [Finset.sum_congr rfl hK]
  unfold aTr
  rw [Finset.sum_range_succ', treeTermN_zero]
  ring

/-- **The Duhamel expansion.** For `A = a^tr + b` on `[p, t]`: `∫_p^t 𝒞₊(A, Ā, A) = ∑_{j ≤ 3} ℒ_j b(t)
+ (a^tr(t) - a(p))`, given the tree recursion at `t`, summable slot values on `[p, t]`, and
interval-integrable slot integrands. -/
theorem integral_aNonlin_aFull (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ)
    (hsum : ∀ s ∈ uIcc (p : ℝ) t, ∀ o : Slot Ntr,
      Summable fun m => ‖slotVal L γ δ p Ntr aP b o s m‖)
    (hint : ∀ x : Slot Ntr × Slot Ntr × Slot Ntr, IntervalIntegrable
      (fun s => aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
        (slotVal L γ δ p Ntr aP b x.2.2 s) n) volume p t)
    (hrec : TreeRecursion L γ δ p aP t n) :
    ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s
        (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
        (fun m => (starRingEnd ℂ)
          (aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m))
        (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
        n =
      ∑ j ∈ range 4, Lop L γ δ p Ntr aP j b t n + (aTr L γ δ p Ntr aP t n - aP n) := by
  rw [intervalIntegral.integral_congr fun s hs =>
      aNonlin_aTr_add_eq_sum L γ δ p Ntr aP b s n (hsum s hs),
    intervalIntegral.integral_finsetSum fun x _ => hint x, sum_slot_partition,
    sum_low_eq_aTr_sub L γ δ p Ntr aP b t n hrec]
  simp only [Lop_eq_sum]

/-- **The Duhamel identity for `ℒ_j`/`a^tr`** (glue list): given the tree recursion, `A = a^tr + b`
satisfies `A(t) = a(p) + ∫_p^t 𝒞₊(A, Ā, A)` iff `b(t) = ℒ₀ b(t) + ℒ₁ b(t) + ℒ₂ b(t) + ℒ₃ b(t)`.
The data `a(p)` and the values of `b` are summable. -/
theorem duhamel_iff_Lop (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun m => ‖aP m‖)
    {b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ} (hb : ∀ s, Summable fun m => ‖b s m‖) (t : ℝ)
    (n : Fin d → ℤ)
    (hint : ∀ x : Slot Ntr × Slot Ntr × Slot Ntr, IntervalIntegrable
      (fun s => aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
        (slotVal L γ δ p Ntr aP b x.2.2 s) n) volume p t)
    (hrec : TreeRecursion L γ δ p aP t n) :
    (aTr L γ δ p Ntr aP t n + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n =
        aP n + ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s
          (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
          (fun m => (starRingEnd ℂ)
            (aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m))
          (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
          n) ↔
      Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n =
        ∑ j ∈ range 4, Lop L γ δ p Ntr aP j b t n := by
  rw [integral_aNonlin_aFull L γ δ p Ntr aP b t n
    (fun s _ o => summable_slotVal L γ δ p Ntr haP hb o s) hint hrec]
  constructor <;> intro h <;> linear_combination h

end Duhamel

/-! ## §4 From the integral form to the differential form -/

/-- If `u(t) = u(p) + ∫_p^t F` on `[p, q]` with `F` continuous there, then `u' = F` within `[p, q]`
(the derivative conjunct of `IsASolution`, for `IsASolution.glue`). -/
theorem hasDerivWithinAt_of_eq_add_integral {u F : ℝ → ℂ} {p q : ℝ}
    (hu : ∀ t ∈ Icc p q, u t = u p + ∫ s in p..t, F s) (hF : ContinuousOn F (Icc p q))
    {t : ℝ} (ht : t ∈ Icc p q) : HasDerivWithinAt u (F t) (Icc p q) t := by
  have : Fact (t ∈ Icc p q) := ⟨ht⟩
  have hint : IntervalIntegrable F volume p t :=
    (hF.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hD : HasDerivWithinAt (fun x => ∫ s in p..x, F s) (F t) (Icc p q) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hF.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hF.continuousWithinAt ht)
  exact (hD.const_add (u p)).congr (fun x hx => hu x hx) (hu t ht)

end WaveTurbulence.SysAPI
