/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Lemma72

/-!
# DH21 Lemma 7.1: a regular chain with class `J`/`R` insertions integrates to zero

DH21 Lemma 7.1 (L1715–L1725). Let `I = X₀ I_{β₁+λ₁} X₁ ⋯ I_{β_{2m}+λ_{2m}} X_{2m}` be as in Lemma 5.9
(`chainX`, `m ≥ 1`), and `K = I(e^{πiλ_*s})(t)` as a function of all its variables `α[W]`. Then
`K ∈ L¹` and `∫ K dα[W] = 0`.

The proof follows DH21. Fix all variables but the variable `α_1` of the first pair. Then
`K(α_1) = Y₀ I_{εα_1} Y₁ I_{μ_1-εα_1} G(t)` with bounded kernels `Y₀`, `Y₁` and bounded `G`. The
Gaussian regularization in `α_1` tends to `0` (`regTo_sand`). Here `Y₀ = X₀` (or `Id`),
`Y₁ = X₁ ⋯` (the inner chain, never `Id` by `AdjOK`) and `G` is the rest of the chain applied to
`e^{πiλ_*s}`. Their kernels are replaced on the triangle `0 ≤ s ≤ t ≤ 1` by continuous representatives
(`mJR_exists_rep`): finite sums of basic class `J`/`R` kernels, which are continuous
(`kcont_JSym_kernel`, `kcont_RSym_kernel`).

* `regchaincancel1`: **DH21 Lemma 7.1**.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-! ### Continuity of the basic kernels -/

section Basic

variable {ι : Type*} [Fintype ι]

theorem kcont_JSym_kernel (R : JSym ι) (hR : SymReg R.m) (β : ι → ℝ) : KCont (R.kernel β) := by
  unfold KCont JSym.kernel
  have hj : ∀ γ : ℝ × ℝ, Continuous fun x : ℝ × ℝ => jker (bundle R.y β) γ.1 γ.2 x.1 x.2 := by
    intro γ; unfold jker; fun_prop
  refine continuous_of_dominated (bound := fun γ => ‖R.m β γ‖) (fun x => ?_) (fun x => ?_)
    (hR.integrable β).norm (Eventually.of_forall fun γ => continuous_const.mul (hj γ))
  · exact (hR.integrable β).aestronglyMeasurable.mul
      (Continuous.aestronglyMeasurable (by unfold jker; fun_prop))
  · exact Eventually.of_forall fun γ => by rw [norm_mul, norm_jker, mul_one]

theorem kcont_RSym_kernel (R : RSym ι) (hR : SymReg R.m) (β : Option ι → ℝ) :
    KCont (R.kernel β) := by
  unfold KCont RSym.kernel
  have hχ : Continuous fun y : ℝ => (chiInvR y : ℂ) := continuous_ofReal.comp contDiff_chiInvR.continuous
  refine continuous_of_dominated (bound := fun γ => CPhi * ‖R.m (nsp β) γ‖) (fun x => ?_)
    (fun x => ?_) ((hR.integrable (nsp β)).norm.const_mul CPhi)
    (Eventually.of_forall fun γ => continuous_const.mul ?_)
  · refine (hR.integrable (nsp β)).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    unfold rker jker
    exact (hχ.comp (continuous_const.add continuous_snd.snd)).mul (by fun_prop)
  · refine Eventually.of_forall fun γ => ?_
    rw [norm_mul, rker, norm_mul, norm_jker, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_chiInvR_le _) (norm_nonneg _)
  · unfold rker jker
    exact continuous_const.mul (by fun_prop)

end Basic

/-! ### Continuous representatives of masked operators -/

section Reps

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A N : ℝ}

theorem keqOn_trans {K L M : ℝ → ℝ → ℂ} (h₁ : KEqOn K L) (h₂ : KEqOn L M) : KEqOn K M :=
  fun t s h0 h1 h2 => (h₁ t s h0 h1 h2).trans (h₂ t s h0 h1 h2)

theorem mJ_exists_rep {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MJ θ A N S T) (p : P)
    (α : V → ℝ) : ∃ K, KCont K ∧ ∀ α' : V → ℝ, (∀ v ∈ S, α' v = α v) → KEqOn (T p α') K := by
  obtain ⟨ι, _, f, _, hr, T', ⟨n, R, c, hb, -, he'⟩, he⟩ := h
  refine ⟨fun t s => ∑ i, ((R i).get p).kernel (α ∘ f) t s, ?_, fun α' hα' => ?_⟩
  · show Continuous fun x : ℝ × ℝ => ∑ i, ((R i).get p).kernel (α ∘ f) x.1 x.2
    exact continuous_finsetSum _ fun i _ => kcont_JSym_kernel _ ((hb i).bound p).reg _
  · have e : α' ∘ f = α ∘ f := funext fun i => hα' (f i) (hr ▸ ⟨i, rfl⟩)
    have := keqOn_trans (he p α') (he' p (α' ∘ f))
    rwa [e] at this

theorem mR0_exists_rep {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MR0 θ A N S T) (p : P)
    (α : V → ℝ) : ∃ K, KCont K ∧ ∀ α' : V → ℝ, (∀ v ∈ S, α' v = α v) → KEqOn (T p α') K := by
  rcases h with ⟨v₀, ι, _, f, _, hr, -, T', ⟨n, R, c, hb, -, he'⟩, he⟩ | ⟨-, hz⟩
  · refine ⟨fun t s => ∑ i, ((R i).get p).kernel (α ∘ f) t s, ?_, fun α' hα' => ?_⟩
    · show Continuous fun x : ℝ × ℝ => ∑ i, ((R i).get p).kernel (α ∘ f) x.1 x.2
      exact continuous_finsetSum _ fun i _ => kcont_RSym_kernel _ ((hb i).bound p).reg _
    · have e : α' ∘ f = α ∘ f := funext fun i => hα' (f i) (hr ▸ ⟨i, rfl⟩)
      have := keqOn_trans (he p α') (he' p (α' ∘ f))
      rwa [e] at this
  · exact ⟨fun _ _ => 0, continuous_const, fun α' _ => hz p α'⟩

/-- **A continuous representative of a masked class `J` + `R` operator**, valid for every
assignment of the variables that agrees with `α` on `S`. -/
theorem mJR_exists_rep {S : Set V} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (h : MJR θ A N S T) (p : P)
    (α : V → ℝ) : ∃ K, KCont K ∧ ∀ α' : V → ℝ, (∀ v ∈ S, α' v = α v) → KEqOn (T p α') K := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, -, he⟩ := h
  obtain ⟨KJ, hKJ, hJ'⟩ := mJ_exists_rep hJ p α
  obtain ⟨KR, hKR, hR'⟩ := mR0_exists_rep hR p α
  refine ⟨fun t s => KJ t s + KR t s, hKJ.add hKR, fun α' hα' => ?_⟩
  exact keqOn_trans (he p α') (KEqOn.add (hJ' α' hα') (hR' α' hα'))

omit [MeasurableSpace P] in
/-- The sandwich `I_{εx} Y I_{μ-εx}` at `α_v = x`, with `Y` replaced by a representative. -/
theorem sandw_keqOn_rep [DecidableEq V] (e : ℤ) (v : V) (m : P → ℝ) {T : P → (V → ℝ) → ℝ → ℝ → ℂ} (p : P)
    (α : V → ℝ) (x : ℝ) {KY : ℝ → ℝ → ℂ} (hKY : KCont KY) (hY : KEqOn (T p (update α v x)) KY) :
    KEqOn (sandw e v m T p (update α v x)) (sandK e (m p) KY x) := by
  intro t s hs0 hst ht1
  show kcomp (kcomp (iker (e * update α v x v)) (T p (update α v x)))
    (iker (m p - e * update α v x v)) t s = _
  rw [update_self, KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) hY) (KEqOn.refl _) t s hs0 hst ht1]
  exact kcomp_assoc (kcont_iker _) hKY (kcont_iker _) hst

theorem volterra_zero_fun (K : ℝ → ℝ → ℂ) : volterra K (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext z; simp [volterra]

end Reps

/-! ### The statement -/

section Statement

variable {P : Type*} [MeasurableSpace P] {V : Type} [DecidableEq V] {θ A : ℝ}
variable {X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}
variable {Aset : ℕ → Set V} {Nb : ℕ → ℝ}

/-- **DH21 Lemma 7.1** (`regchaincancel1`, L1715–L1725). Let `c` be a legal partition (Catalan form,
`m ≥ 1` pairs `q, …`, positions `o, …, o+2m`) with signs `ε_j = ±1`, variables `α_j = α (σ j)` and
measurable `μ_j = μf j p`. Let `X_a` be class `J` plus class `R` operators (or `Id`) in pairwise
disjoint variable sets `Aset a`, with `X_a ≠ Id` whenever `{a, a+1}` is a pair (`AdjOK`,
`ChainDisj`). Let `I = X₀ I_{β₁+λ₁} X₁ ⋯ I_{β_{2m}+λ_{2m}} X_{2m}` (`chainX`). Let
`K = I(e^{πiλ_*s})(t)` with `t ∈ [0,1]`, as a function of all its variables `α[W]`,
`W = chainVars`. Then `K ∈ L¹(α[W])` (the other variables fixed at `α₀`) and `∫ K dα[W] = 0`. -/
theorem regchaincancel1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) (hX : ∀ a T, X a = some T → MJR θ A (Nb a) (Aset a) T)
    (hXn : ∀ a, X a = none → Aset a = ∅) {c : LegalCode} (hc : c ≠ .nil) {o q : ℕ}
    (hadj : AdjOK X c o) (hdisj : ChainDisj σ Aset c o q) {W : Finset V}
    (hW : (W : Set V) = chainVars σ Aset c o q) {T : P → (V → ℝ) → ℝ → ℝ → ℂ}
    (hT : chainX X σ ε μf c o q = some T) (p : P) (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (α₀ : V → ℝ) :
    MInt W (fun α => volterra (T p α) (expF lam) t) α₀ ∧
    mint W (fun α => volterra (T p α) (expF lam) t) α₀ = 0 := by
  -- the class bounds (DH21 Lemma 5.9) give `K ∈ L¹`
  have hint : MInt W (fun α => volterra (T p α) (expF lam) t) α₀ := by
    rcases chainX_spec h0 h1 hA hε hμ hX hXn c o q hadj hdisj with ⟨hn, -, -⟩ | ⟨T', hT', hM⟩
    · exact absurd hn hc
    · rw [hT, Option.some.injEq] at hT'
      subst hT'
      rw [← hW] at hM
      exact mJR_mInt_volterra hM h0 p lam ht α₀
  refine ⟨hint, ?_⟩
  obtain ⟨i, r, rfl⟩ : ∃ i r, c = .node i r := by
    cases c with
    | nil => exact absurd rfl hc
    | node i r => exact ⟨i, r, rfl⟩
  obtain ⟨hadji, hadj1, hadj2⟩ := hadj
  obtain ⟨hvq, hdir, hdo, hd1, hd2⟩ := hdisj
  -- the inner chain `Y₁` is a genuine operator
  obtain ⟨Y, hY, hMY⟩ : ∃ Y, chainX X σ ε μf i (o + 1) (q + 1) = some Y ∧
      MJR θ A (Cch θ ^ i.size * chainNorm X Nb i (o + 1)) (chainVars σ Aset i (o + 1) (q + 1)) Y := by
    rcases chainX_spec h0 h1 hA hε hμ hX hXn i (o + 1) (q + 1) hadj1 hd1 with ⟨rfl, hnone, -⟩ | h
    · exact absurd (by simpa [chainX] using hnone) (hadji rfl)
    · exact h
  -- peel the variable `α_q` of the first pair
  have hqW : σ q ∈ W := by
    rw [← Finset.mem_coe, hW]
    simp [chainVars]
  have hWe : W = W.erase (σ q) ∪ {σ q} := (Finset.erase_union_eq _ _ hqW).symm
  rw [hWe] at hint ⊢
  refine mint_eq_zero_of_peel (Finset.notMem_erase _ _) hint fun α hi => ?_
  -- continuous representatives of the factors that do not see `α_q`
  obtain ⟨KY, hKYc, hKY⟩ := mJR_exists_rep hMY p α
  have hKY' : ∀ x, KEqOn (Y p (update α (σ q) x)) KY := fun x =>
    hKY _ fun v hv => update_of_ne (by rintro rfl; exact hvq hv) _ _
  have hS : ∀ x, KEqOn (sandw (ε q) (σ q) (μf q) Y p (update α (σ q) x))
      (sandK (ε q) (μf q p) KY x) := fun x => sandw_keqOn_rep _ _ _ p α x hKYc (hKY' x)
  have hSc : ∀ x, KCont (sandK (ε q) (μf q p) KY x) := fun x => (pcont_sandK (ε q) (μf q p) hKYc).apply x
  have hT2 : ocomp (X o) (ocomp (some (sandw (ε q) (σ q) (μf q) Y))
      (chainX X σ ε μf r (o + 2 * i.size + 2) (q + i.size + 1))) = some T := by
    rw [← hT]; simp only [chainX, hY]; rfl
  have hg := continuous_expF lam
  -- the operator after the first pair
  have hB : ∀ B, chainX X σ ε μf r (o + 2 * i.size + 2) (q + i.size + 1) = some B →
      ∃ KB, KCont KB ∧ ∀ x, KEqOn (B p (update α (σ q) x)) KB := by
    intro B hBe
    rcases chainX_spec h0 h1 hA hε hμ hX hXn r _ _ hadj2 hd2 with ⟨-, hn, -⟩ | ⟨B', hB', hMB⟩
    · rw [hBe] at hn; exact absurd hn (by simp)
    · rw [hBe, Option.some.injEq] at hB'
      subst hB'
      obtain ⟨KB, hKBc, hKB⟩ := mJR_exists_rep hMB p α
      exact ⟨KB, hKBc, fun x => hKB _ fun v hv => update_of_ne
        (by rintro rfl; exact Set.disjoint_left.1 hdir (Set.mem_insert _ _) hv) _ _⟩
  -- the operator before the first pair
  have hA' : ∀ A', X o = some A' → ∃ KA, KCont KA ∧ ∀ x, KEqOn (A' p (update α (σ q) x)) KA := by
    intro A' hAe
    obtain ⟨KA, hKAc, hKA⟩ := mJR_exists_rep (hX o A' hAe) p α
    exact ⟨KA, hKAc, fun x => hKA _ fun v hv => update_of_ne
      (by rintro rfl; exact Set.disjoint_left.1 hdo hv (Or.inl (Set.mem_insert _ _))) _ _⟩
  -- the section is a regularizable family with limit `0`
  suffices hreg : ∃ Φ : ℝ → ℝ → ℂ, RegTo Φ (fun _ => 0) ∧
      ∀ x, volterra (T p (update α (σ q) x)) (expF lam) t = Φ x t by
    obtain ⟨Φ, hΦ, he⟩ := hreg
    have e : (fun x : ℝ => volterra (T p (update α (σ q) x)) (expF lam) t) = fun x => Φ x t :=
      funext he
    rw [e] at hi ⊢
    exact hΦ.integral_eq ht hi
  rcases hXo : X o with _ | A' <;>
    rcases hBo : chainX X σ ε μf r (o + 2 * i.size + 2) (q + i.size + 1) with _ | B <;>
    simp only [hXo, hBo, ocomp, Option.some.injEq] at hT2 <;> subst hT2
  · -- `T = I Y₁ I`
    refine ⟨fun x z => volterra (sandK (ε q) (μf q p) KY x) (expF lam) z,
      regTo_sand (hε q) _ hKYc hg, fun x => volterra_congr_tri (hS x) _ ht⟩
  · -- `T = (I Y₁ I) B`
    obtain ⟨KB, hKBc, hKB⟩ := hB B hBo
    refine ⟨fun x z => volterra (sandK (ε q) (μf q p) KY x) (volterra KB (expF lam)) z,
      regTo_sand (hε q) _ hKYc (continuous_volterra hKBc hg), fun x => ?_⟩
    rw [volterra_congr_tri (KEqOn.kcomp (hS x) (hKB x)) _ ht,
      volterra_kcomp (hSc x) hKBc hg ht.1]
  · -- `T = A (I Y₁ I)`
    obtain ⟨KA, hKAc, hKA⟩ := hA' A' hXo
    have hR := (regTo_sand (hε q) (μf q p) hKYc hg).volterra_left hKAc
    rw [volterra_zero_fun] at hR
    refine ⟨_, hR, fun x => ?_⟩
    rw [volterra_congr_tri (KEqOn.kcomp (hKA x) (hS x)) _ ht,
      volterra_kcomp hKAc (hSc x) hg ht.1]
  · -- `T = A ((I Y₁ I) B)`
    obtain ⟨KA, hKAc, hKA⟩ := hA' A' hXo
    obtain ⟨KB, hKBc, hKB⟩ := hB B hBo
    have hR := (regTo_sand (hε q) (μf q p) hKYc (continuous_volterra hKBc hg)).volterra_left hKAc
    rw [volterra_zero_fun] at hR
    refine ⟨_, hR, fun x => ?_⟩
    rw [volterra_congr_tri (KEqOn.kcomp (hKA x) (KEqOn.kcomp (hS x) (hKB x))) _ ht,
      volterra_kcomp hKAc (continuous_kcomp (hSc x) hKBc) hg ht.1]
    exact volterra_congr _ (fun s hs => volterra_kcomp (hSc x) hKBc hg hs.1) ht

end Statement

end WaveTurbulence.Cancel
