/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.DuhCarriers

/-!
# Measurability and boundedness of the tree terms in time; obligation O-TR2 (scratch, snapshot 5)

* The time integral `timeInt S κ p t = ∫_{treeTimeDomain S p t} ∏ e^{iπζδL^{2γ}Ωτ}` is strongly
  measurable in `t`:
  - `{(t, τ) | τ ∈ treeTimeDomain S p t}` is open;
  - then `StronglyMeasurable.integral_prod_right'`.
* It is bounded by the volume of `[p, t]^{𝒩}`, which is monotone in `t`.
* `t ↦ 𝒥_S(t)_k` is strongly measurable: a countable `tsum` of strongly measurable functions.
* `∑_k |𝒥_S(s)_k|` is bounded uniformly for `s ≤ t` (`tsum_norm_treeTerm_le`).
* `‖𝒞₊(f, g, h)‖ ≤ |coupling| ‖f‖₁ ‖g‖₁ ‖h‖₁` (`norm_aNonlin_le_tsum`).
* **O-TR2** (`intervalIntegrable_treeTriple`): `s ↦ 𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)(s)_n` is interval
  integrable.
-/

@[expose] public section

open MeasureTheory Finset Set Filter Topology

namespace WaveTurbulence.SysAPI

section Defs

variable (L γ δ : ℝ) {d : ℕ}

/-- The phase product `∏_𝔫 e^{iπ ζ_𝔫 δ L^{2γ} Ω_𝔫 τ_𝔫}` of a labelling of a tree. -/
noncomputable def phaseFn (S : TTree) (κ : GNode (single S) → (Fin d → ℤ))
    (τ : GBranch (single S) → ℝ) : ℂ :=
  ∏ c : GBranch (single S), Complex.exp ((Real.pi * ((treeSign S c.toNode : ℤˣ) : ℤ) * δ *
    L ^ (2 * γ) * resFactor (latticePoint L (κ (c.child 0))) (latticePoint L (κ (c.child 1)))
      (latticePoint L (κ (c.child 2))) (latticePoint L (κ c.toNode)) * τ c : ℝ) * Complex.I)

/-- The time integral of a labelling of a tree over `treeTimeDomain S p t`. -/
noncomputable def timeInt (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) (p t : ℝ) : ℂ :=
  ∫ τ, (treeTimeDomain S p t).indicator (phaseFn L γ δ S κ) τ

/-- The product of the `ε` coefficients. -/
noncomputable def epsProd (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) : ℂ :=
  ∏ c : GBranch (single S), (epsCoef (κ (c.child 0)) (κ (c.child 1)) (κ (c.child 2)) : ℂ)

/-- The leaf factor `∏_ℓ b_{κ_ℓ}^{ζ_ℓ}`. -/
noncomputable def leafProd (S : TTree) (b : (Fin d → ℤ) → ℂ) (κ : GNode (single S) → (Fin d → ℤ)) :
    ℂ :=
  ∏ ℓ : GLeaf (single S), zpowSign (treeSign S ℓ.toNode) (b (κ ℓ.toNode))

theorem treeSummand_eq (p : ℕ) (S : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ)
    (κ : TreeDecoration S d n) :
    treeSummand L γ δ p S b t n κ = epsProd S κ.1 * timeInt L γ δ S κ.1 p t * leafProd S b κ.1 :=
  rfl

theorem continuous_phaseFn (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) :
    Continuous (phaseFn L γ δ S κ) := by
  unfold phaseFn
  fun_prop

theorem norm_phaseFn (S : TTree) (κ : GNode (single S) → (Fin d → ℤ))
    (τ : GBranch (single S) → ℝ) : ‖phaseFn L γ δ S κ τ‖ = 1 := by
  unfold phaseFn
  rw [norm_prod]
  exact Finset.prod_eq_one fun c _ => Complex.norm_exp_ofReal_mul_I _

/-- The volume of the box `[p, t]^{𝒩}`. -/
noncomputable def boxVol (S : TTree) (p t : ℝ) : ℝ :=
  (volume : Measure (GBranch (single S) → ℝ)).real (Set.pi univ fun _ => Icc p t)

theorem boxVol_nonneg (S : TTree) (p t : ℝ) : 0 ≤ boxVol S p t := measureReal_nonneg

theorem boxVol_mono (S : TTree) (p : ℝ) {s t : ℝ} (hst : s ≤ t) : boxVol S p s ≤ boxVol S p t :=
  measureReal_mono (Set.pi_mono fun _ _ => Icc_subset_Icc le_rfl hst)
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne

theorem norm_timeInt_le (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) (p t : ℝ) :
    ‖timeInt L γ δ S κ p t‖ ≤ boxVol S p t :=
  norm_integral_treeTimeDomain_le S p t _ fun τ => (norm_phaseFn L γ δ S κ τ).le

theorem norm_epsProd_le (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) :
    ‖epsProd S κ‖ ≤ 1 := by
  unfold epsProd
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun c _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold epsCoef
  split_ifs <;> simp

end Defs

/-! ## Measurability in time -/

section Measurability

variable (L γ δ : ℝ) {d : ℕ}

theorem isOpen_setOf_imp {X : Type*} [TopologicalSpace X] (P : Prop) {U : Set X} (hU : IsOpen U) :
    IsOpen {x | P → x ∈ U} := by
  by_cases h : P
  · simpa [h] using hU
  · simp [h]

/-- `{(t, τ) | τ ∈ treeTimeDomain S p t}` is open. -/
theorem isOpen_domSet (S : TTree) (p : ℝ) :
    IsOpen {z : ℝ × (GBranch (single S) → ℝ) | z.2 ∈ treeTimeDomain S p z.1} := by
  have e : {z : ℝ × (GBranch (single S) → ℝ) | z.2 ∈ treeTimeDomain S p z.1} =
      ⋂ c, ({z | p < z.2 c} ∩ {z | z.2 c < z.1} ∩
        ⋂ c' : GBranch (single S), {z | c'.IsChildOf c → z ∈ {z | z.2 c' < z.2 c}}) := by
    ext z
    simp [treeTimeDomain, and_assoc]
  rw [e]
  refine isOpen_iInter_of_finite fun c => ((isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt (by fun_prop) continuous_fst)).inter (isOpen_iInter_of_finite fun c' => ?_)
  exact isOpen_setOf_imp _ (isOpen_lt (by fun_prop) (by fun_prop))

theorem stronglyMeasurable_timeInt (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) (p : ℝ) :
    StronglyMeasurable fun t => timeInt L γ δ S κ p t := by
  have hU := (isOpen_domSet S p).measurableSet
  have hF : StronglyMeasurable fun z : ℝ × (GBranch (single S) → ℝ) =>
      {z : ℝ × (GBranch (single S) → ℝ) | z.2 ∈ treeTimeDomain S p z.1}.indicator
        (fun z => phaseFn L γ δ S κ z.2) z :=
    ((continuous_phaseFn L γ δ S κ).comp continuous_snd).stronglyMeasurable.indicator hU
  convert hF.integral_prod_right' (ν := (volume : Measure (GBranch (single S) → ℝ))) using 1
  funext t
  unfold timeInt
  congr 1

instance (S : TTree) (d : ℕ) (n : Fin d → ℤ) : Countable (TreeDecoration S d n) :=
  Subtype.countable

/-- A pointwise summable countable sum of strongly measurable functions is strongly measurable. -/
theorem stronglyMeasurable_tsum {ι : Type*} [Countable ι] {f : ι → ℝ → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ s, Summable fun i => f i s) :
    StronglyMeasurable fun s => ∑' i, f i s :=
  stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι))
    (fun F => Finset.stronglyMeasurable_fun_sum F fun i _ => hf i)
    (tendsto_pi_nhds.2 fun s => (hs s).hasSum)

/-- `t ↦ 𝒥_S(t)_n` is strongly measurable. -/
theorem stronglyMeasurable_treeTerm (p : ℕ) (S : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun k => ‖b k‖) (n : Fin d → ℤ) :
    StronglyMeasurable fun t => treeTerm L γ δ p S b t n := by
  simp only [treeTerm_eq, treeSummand_eq]
  refine stronglyMeasurable_const.mul (stronglyMeasurable_tsum (fun κ => ?_) fun s =>
    (summable_treeSummand L γ δ p S hb s n).of_norm)
  exact (stronglyMeasurable_const.mul (stronglyMeasurable_timeInt L γ δ S κ.1 p)).mul
    stronglyMeasurable_const

end Measurability

/-! ## Uniform `ℓ¹` bounds -/

section Bounds

variable (L γ δ : ℝ) {d : ℕ}

theorem summable_leafNorm_sigma (S : TTree) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) :
    Summable fun x : (Σ n : Fin d → ℤ, TreeDecoration S d n) =>
      ∏ ℓ : GLeaf (single S), ‖b (x.2.1 ℓ.toNode)‖ := by
  classical
  let Ψ : (Σ n : Fin d → ℤ, TreeDecoration S d n) → (GLeaf (single S) → (Fin d → ℤ)) :=
    fun x ℓ => x.2.1 ℓ.toNode
  have hΨ : Function.Injective Ψ := by
    rintro ⟨n, κ⟩ ⟨n', κ'⟩ h
    have hκ : κ.1 = κ'.1 := treeDecoration_eq_of_leaves κ κ' fun ℓ => congrFun h ℓ
    have hn : n = n' := κ.2.2.symm.trans ((congrFun hκ _).trans κ'.2.2)
    subst hn
    have hκκ : κ = κ' := Subtype.ext hκ
    subst hκκ
    rfl
  exact (summable_pi_prod (fun (_ : GLeaf (single S)) m => ‖b m‖) (fun _ _ => norm_nonneg _)
    fun _ => hb).comp_injective hΨ

theorem norm_treeTerm_le (p : ℕ) (S : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun k => ‖b k‖) (t : ℝ) (n : Fin d → ℤ) :
    ‖treeTerm L γ δ p S b t n‖ ≤ ‖treePrefactor L γ δ d S‖ * (boxVol S p t *
      ∑' κ : TreeDecoration S d n, ∏ ℓ : GLeaf (single S), ‖b (κ.1 ℓ.toNode)‖) := by
  have hg := summable_leafNorm_sigma S hb
  have hg0 : ∀ x : (Σ n : Fin d → ℤ, TreeDecoration S d n),
      0 ≤ ∏ ℓ : GLeaf (single S), ‖b (x.2.1 ℓ.toNode)‖ :=
    fun x => Finset.prod_nonneg fun _ _ => norm_nonneg _
  obtain ⟨hgκ, -⟩ := (summable_sigma_of_nonneg hg0).1 hg
  rw [treeTerm_eq, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑' κ, treeSummand L γ δ p S b t n κ‖
      ≤ ∑' κ, ‖treeSummand L γ δ p S b t n κ‖ :=
        norm_tsum_le_tsum_norm (summable_treeSummand L γ δ p S hb t n)
    _ ≤ ∑' κ : TreeDecoration S d n, boxVol S p t * ∏ ℓ : GLeaf (single S), ‖b (κ.1 ℓ.toNode)‖ :=
        Summable.tsum_le_tsum (fun κ => norm_treeSummand_le L γ δ p S b t n κ)
          (summable_treeSummand L γ δ p S hb t n) ((hgκ n).mul_left _)
    _ = _ := tsum_mul_left

/-- **Uniform `ℓ¹` bound:** `∑_k |𝒥_S(s)_k| ≤ |pref| · vol([p,t]^{𝒩}) · ∑_z ∏_ℓ |b_{z_ℓ}|` for `s ≤ t`. -/
theorem tsum_norm_treeTerm_le (p : ℕ) (S : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun k => ‖b k‖) {s t : ℝ} (hst : s ≤ t) :
    ∑' k, ‖treeTerm L γ δ p S b s k‖ ≤ ‖treePrefactor L γ δ d S‖ * (boxVol S p t *
      ∑' z : GLeaf (single S) → (Fin d → ℤ), ∏ ℓ : GLeaf (single S), ‖b (z ℓ)‖) := by
  classical
  have hg := summable_leafNorm_sigma S hb
  have hg0 : ∀ x : (Σ n : Fin d → ℤ, TreeDecoration S d n),
      0 ≤ ∏ ℓ : GLeaf (single S), ‖b (x.2.1 ℓ.toNode)‖ :=
    fun x => Finset.prod_nonneg fun _ _ => norm_nonneg _
  obtain ⟨hgκ, hgn⟩ := (summable_sigma_of_nonneg hg0).1 hg
  have hz := summable_pi_prod (fun (_ : GLeaf (single S)) m => ‖b m‖) (fun _ _ => norm_nonneg _)
    fun _ => hb
  let Ψ : (Σ n : Fin d → ℤ, TreeDecoration S d n) → (GLeaf (single S) → (Fin d → ℤ)) :=
    fun x ℓ => x.2.1 ℓ.toNode
  have hΨ : Function.Injective Ψ := by
    rintro ⟨n, κ⟩ ⟨n', κ'⟩ h
    have hκ : κ.1 = κ'.1 := treeDecoration_eq_of_leaves κ κ' fun ℓ => congrFun h ℓ
    have hn : n = n' := κ.2.2.symm.trans ((congrFun hκ _).trans κ'.2.2)
    subst hn
    have hκκ : κ = κ' := Subtype.ext hκ
    subst hκκ
    rfl
  have hP := norm_nonneg (treePrefactor L γ δ d S)
  calc ∑' k, ‖treeTerm L γ δ p S b s k‖
      ≤ ∑' k, ‖treePrefactor L γ δ d S‖ * (boxVol S p s *
          ∑' κ : TreeDecoration S d k, ∏ ℓ : GLeaf (single S), ‖b (κ.1 ℓ.toNode)‖) :=
        Summable.tsum_le_tsum (fun k => norm_treeTerm_le L γ δ p S hb s k)
          (summable_norm_treeTerm L γ δ p S hb s) ((hgn.mul_left _).mul_left _)
    _ = ‖treePrefactor L γ δ d S‖ * (boxVol S p s *
          ∑' x : (Σ n : Fin d → ℤ, TreeDecoration S d n),
            ∏ ℓ : GLeaf (single S), ‖b (x.2.1 ℓ.toNode)‖) := by
        rw [tsum_mul_left, tsum_mul_left, hg.tsum_sigma]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (boxVol_mono S p hst)
        (tsum_comp_le_tsum_of_inj hz (fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) hΨ)
        (tsum_nonneg hg0) (boxVol_nonneg S p t)) hP

theorem norm_le_tsum_norm {f : (Fin d → ℤ) → ℂ} (hf : Summable fun k => ‖f k‖) (k : Fin d → ℤ) :
    ‖f k‖ ≤ ∑' k, ‖f k‖ :=
  hf.le_tsum k fun _ _ => norm_nonneg _

/-- `‖𝒞_ζ(f, g, h)_n‖ ≤ |coupling · ζ| ‖f‖₁ ‖g‖₁ ‖h‖₁`. -/
theorem norm_aNonlin_le_tsum (ζ : ℤ) (t : ℝ) {f g h : (Fin d → ℤ) → ℂ}
    (hf : Summable fun k => ‖f k‖) (hg : Summable fun k => ‖g k‖) (hh : Summable fun k => ‖h k‖)
    (n : Fin d → ℤ) :
    ‖aNonlin L γ δ ζ t f g h n‖ ≤ ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ)‖ *
      ((∑' k, ‖f k‖) * (∑' k, ‖g k‖) * ∑' k, ‖h k‖) := by
  rw [aNonlin_eq_tsum_aNonlinTerm, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hfg : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) => ‖f q.1‖ * ‖g q.2‖ :=
    summable_mul_of_summable_norm (f := fun m => ‖f m‖) (g := fun m => ‖g m‖)
      (by simpa using hf) (by simpa using hg)
  calc ‖∑' q, aNonlinTerm L γ δ ζ t f g h n q‖
      ≤ ∑' q, ‖aNonlinTerm L γ δ ζ t f g h n q‖ :=
        norm_tsum_le_tsum_norm (summable_aNonlinTerm L γ δ ζ t hf hg
          (norm_le_tsum_norm hh) n)
    _ ≤ ∑' q : (Fin d → ℤ) × (Fin d → ℤ), ‖f q.1‖ * ‖g q.2‖ * ∑' k, ‖h k‖ :=
        Summable.tsum_le_tsum (fun q => (norm_aNonlinTerm_le L γ δ ζ t f g h n q).trans
          (mul_le_mul_of_nonneg_left (norm_le_tsum_norm hh _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
          (summable_aNonlinTerm L γ δ ζ t hf hg (norm_le_tsum_norm hh) n) (hfg.mul_right _)
    _ = _ := by
        rw [tsum_mul_right, tsum_mul_tsum_of_summable_norm (f := fun k => ‖f k‖)
          (g := fun k => ‖g k‖) (by simpa using hf) (by simpa using hg)]

/-- `s ↦ 𝒞₊(F(s), Ḡ(s), H(s))_n` is strongly measurable when the coefficients are, with summable
norms at every time. -/
theorem stronglyMeasurable_aNonlin {F G H : ℝ → (Fin d → ℤ) → ℂ}
    (hF : ∀ k, StronglyMeasurable fun s => F s k) (hG : ∀ k, StronglyMeasurable fun s => G s k)
    (hH : ∀ k, StronglyMeasurable fun s => H s k) (hFs : ∀ s, Summable fun k => ‖F s k‖)
    (hGs : ∀ s, Summable fun k => ‖G s k‖) (hHs : ∀ s, Summable fun k => ‖H s k‖)
    (n : Fin d → ℤ) :
    StronglyMeasurable fun s => aNonlin L γ δ 1 s (F s) (fun k => (starRingEnd ℂ) (G s k)) (H s) n := by
  simp only [aNonlin_eq_tsum_aNonlinTerm]
  refine stronglyMeasurable_const.mul (stronglyMeasurable_tsum (fun q => ?_) fun s =>
    (summable_aNonlinTerm L γ δ 1 s (hFs s) (by simpa using hGs s)
      (norm_le_tsum_norm (hHs s)) n).of_norm)
  unfold aNonlinTerm
  refine (((stronglyMeasurable_const.mul ?_).mul (hF q.1)).mul ?_).mul (hH _)
  · exact (by fun_prop : Continuous fun s : ℝ => Complex.exp (((((1 : ℤ) : ℝ) * Real.pi * δ *
      L ^ (2 * γ) * resFactor (latticePoint L q.1) (latticePoint L q.2)
        (latticePoint L (n - q.1 + q.2)) (latticePoint L n) * s : ℝ) : ℂ) * Complex.I)).stronglyMeasurable
  · exact Complex.continuous_conj.comp_stronglyMeasurable (hG q.2)

/-- **Obligation O-TR2, proved**: the tree triples are interval integrable. -/
theorem intervalIntegrable_treeTriple (p : ℕ) (l m r : TTree) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun k => ‖b k‖) (t : ℝ) (n : Fin d → ℤ) :
    IntervalIntegrable (fun s => aNonlin L γ δ 1 s (treeTerm L γ δ p l b s)
      (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b s k)) (treeTerm L γ δ p r b s) n)
      volume p t := by
  set t' := max (p : ℝ) t
  set B : TTree → ℝ := fun S => ‖treePrefactor L γ δ d S‖ * (boxVol S p t' *
    ∑' z : GLeaf (single S) → (Fin d → ℤ), ∏ ℓ : GLeaf (single S), ‖b (z ℓ)‖)
  have hmeas := stronglyMeasurable_aNonlin L γ δ
    (fun k => stronglyMeasurable_treeTerm L γ δ p l hb k)
    (fun k => stronglyMeasurable_treeTerm L γ δ p m hb k)
    (fun k => stronglyMeasurable_treeTerm L γ δ p r hb k)
    (fun s => summable_norm_treeTerm L γ δ p l hb s) (fun s => summable_norm_treeTerm L γ δ p m hb s)
    (fun s => summable_norm_treeTerm L γ δ p r hb s) n
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) *
      (Complex.I * ((1 : ℤ) : ℂ))‖ * (B l * B m * B r))
    (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne) hmeas.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_)
  have hst : s ≤ t' := by
    rw [Set.uIoc] at hs
    exact hs.2
  refine (norm_aNonlin_le_tsum L γ δ 1 s (summable_norm_treeTerm L γ δ p l hb s)
    (by simpa using summable_norm_treeTerm L γ δ p m hb s) (summable_norm_treeTerm L γ δ p r hb s)
    n).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h1 := tsum_norm_treeTerm_le L γ δ p l hb hst
  have h2 := tsum_norm_treeTerm_le L γ δ p m hb hst
  have h3 := tsum_norm_treeTerm_le L γ δ p r hb hst
  simp only [Complex.norm_conj]
  have n1 : 0 ≤ ∑' k, ‖treeTerm L γ δ p l b s k‖ := tsum_nonneg fun _ => norm_nonneg _
  have n2 : 0 ≤ ∑' k, ‖treeTerm L γ δ p m b s k‖ := tsum_nonneg fun _ => norm_nonneg _
  have n3 : 0 ≤ ∑' k, ‖treeTerm L γ δ p r b s k‖ := tsum_nonneg fun _ => norm_nonneg _
  exact mul_le_mul (mul_le_mul h1 h2 n2 (n1.trans h1)) h3 n3
    (mul_nonneg (n1.trans h1) (n2.trans h2))

end Bounds

end WaveTurbulence.SysAPI
