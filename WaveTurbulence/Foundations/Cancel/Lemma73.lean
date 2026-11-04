/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Cores

/-!
# DH21 Lemma 7.3: the dominant regular chain, with the corrected sign (F61)

For the dominant partition `𝒫 = {{1,2}, …, {2m-1,2m}}` (`domCode m` in Catalan form) every pair is
adjacent. Lemma 5.10 writes `I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}} = ∑_Z ∏_{j∈Z} Φ(ε_jα_j) Ĩ_Z`. Here `Ĩ_Z` is
the composition of the pieces `𝒥_{α[ ],μ_j} = -I_{μ_j}` (`j ∈ Z`) and
`𝒥_{α_j,μ_j} + ℛ_{α_j,μ_j}` (`j ∉ Z`). DH21 Lemma 7.3 (L1732–L1746) states, for
`K̃ = Ĩ_Z(e^{πiλ₀s})(t)`,
`∫ K̃ dα[W] = ∫_{t>t₁>⋯>t_m>0} e^{πi(μ₁t₁+⋯+μ_mt_m)+πiλ₀t_m} dt`.

**Erratum (F61, CONFIRMED).** The correct right side is `(-1)^{|Z|}` times this integral. Each
`j ∈ Z` contributes `𝒥_{α[ ],μ_j} = -I_{μ_j}` (Lemma 5.8). For `j ∉ Z` the integral over `α_j` of
the `𝒥 + ℛ` piece is `+I_{μ_j}` (`regTo_tr58`). `regchaincal` carries the sign.

The proof peels one variable `α_j`, `j ∉ Z`, at a time. Fubini splits off the `α_j` integral, and the
inner integral is the Gaussian-regularized limit (`RegTo`). It equals the same chain with `j ∈ Z`,
up to a sign `-1`. The chain is written as iterated Volterra operators (`chainV`).

* `domCode`, `adjSet_domCode`: the dominant code; all its pairs are adjacent.
* `chainV K f m q = volterra (K q) (volterra (K (q+1)) ⋯ f)`; `simplexInt` is the right side of
  (regchaincalref).
* `volterra_tildeP_domCode`: `Ĩ_Z(f)(t) = chainV (pieces) f`.
* `regchaincal`: **DH21 Lemma 7.3, corrected**.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-! ### The dominant code -/

/-- **The dominant legal partition** `{{1,2}, …, {2m-1,2m}}` in Catalan form. -/
@[expose] def domCode : ℕ → LegalCode
  | 0 => .nil
  | m + 1 => .node .nil (domCode m)

theorem size_domCode : ∀ m, (domCode m).size = m
  | 0 => rfl
  | m + 1 => by simp [domCode, LegalCode.size, size_domCode m]

theorem domCode_ne_nil {m : ℕ} (hm : m ≠ 0) : domCode m ≠ .nil := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  simp [domCode]

/-- Every pair of the dominant code is adjacent. -/
theorem adjSet_domCode : ∀ (m q : ℕ), adjSet (domCode m) q = Finset.Ico q (q + m)
  | 0, q => by simp [domCode, adjSet]
  | m + 1, q => by
    rw [show adjSet (domCode (m + 1)) q = insert q (adjSet (domCode m) (q + 1)) from rfl,
      adjSet_domCode m (q + 1), show q + 1 + m = q + (m + 1) by omega]
    exact Finset.insert_Ico_add_one_left_eq_Ico (by omega)

/-! ### Iterated Volterra operators -/

/-- **The chain of Volterra operators** `K_q ∘ K_{q+1} ∘ ⋯ ∘ K_{q+m-1}` applied to `f`. -/
@[expose] noncomputable def chainV (K : ℕ → ℝ → ℝ → ℂ) (f : ℝ → ℂ) : ℕ → ℕ → ℝ → ℂ
  | 0, _ => f
  | m + 1, q => volterra (K q) (chainV K f m (q + 1))

/-- **The right side of DH21 (regchaincalref)**:
`∫_{t>t₁>⋯>t_m>0} e^{πi(μ_q t₁ + ⋯ + μ_{q+m-1} t_m) + πiλ₀t_m} dt₁ ⋯ dt_m`, i.e.
`I_{μ_q} I_{μ_{q+1}} ⋯ I_{μ_{q+m-1}} (e^{πiλ₀s})(t)`. -/
@[expose] noncomputable def simplexInt (μ : ℕ → ℝ) (lam : ℝ) (m q : ℕ) : ℝ → ℂ :=
  chainV (fun j => iker (μ j)) (expF lam) m q

theorem chainV_congr {K K' : ℕ → ℝ → ℝ → ℂ} (f : ℝ → ℂ) :
    ∀ (m q : ℕ), (∀ j, q ≤ j → j < q + m → K j = K' j) → chainV K f m q = chainV K' f m q
  | 0, _, _ => rfl
  | m + 1, q, h => by
    simp only [chainV]
    rw [h q le_rfl (by omega), chainV_congr f m (q + 1) fun j h1 h2 => h j (by omega) (by omega)]

theorem continuous_chainV {K : ℕ → ℝ → ℝ → ℂ} (hK : ∀ j, KCont (K j)) {f : ℝ → ℂ}
    (hf : Continuous f) : ∀ (m q : ℕ), Continuous (chainV K f m q)
  | 0, _ => hf
  | m + 1, q => continuous_volterra (hK q) (continuous_chainV hK hf m (q + 1))

theorem volterra_neg_kernel (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ) :
    volterra (fun t s => -K t s) g t = -volterra K g t := by
  unfold volterra
  rw [← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun s _ => by ring

theorem volterra_neg_fun (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ) :
    volterra K (fun s => -g s) t = -volterra K g t := by
  unfold volterra
  rw [← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun s _ => by ring

/-- All kernels negated: `chainV (-K) = (-1)^m chainV K`. -/
theorem chainV_neg (K : ℕ → ℝ → ℝ → ℂ) (f : ℝ → ℂ) :
    ∀ (m q : ℕ) (t : ℝ), chainV (fun j t s => -K j t s) f m q t = (-1) ^ m * chainV K f m q t
  | 0, _, t => by simp [chainV]
  | m + 1, q, t => by
    simp only [chainV]
    have e : chainV (fun j t s => -K j t s) f m (q + 1) =
        fun s => (-1) ^ m * chainV K f m (q + 1) s := funext (chainV_neg K f m (q + 1))
    rw [e, volterra_neg_kernel]
    unfold volterra
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [pow_succ]
    ring

/-- One kernel negated. -/
theorem chainV_update_neg (K : ℕ → ℝ → ℝ → ℂ) (L : ℝ → ℝ → ℂ) (f : ℝ → ℂ) {j : ℕ} :
    ∀ (m q : ℕ), q ≤ j → j < q + m → ∀ t,
      chainV (update K j fun t s => -L t s) f m q t = -chainV (update K j L) f m q t
  | 0, _, h1, h2, _ => by omega
  | m + 1, q, h1, h2, t => by
    simp only [chainV]
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · rw [update_self, update_self, volterra_neg_kernel]
      congr 1
      have hc : ∀ (M : ℝ → ℝ → ℂ), chainV (update K q M) f m (q + 1) = chainV K f m (q + 1) :=
        fun M => chainV_congr f m (q + 1) fun i hi _ => update_of_ne (by omega) _ _
      rw [hc, hc]
    · rw [update_of_ne (by omega), update_of_ne (by omega)]
      have e : chainV (update K j fun t s => -L t s) f m (q + 1) =
          fun s => -chainV (update K j L) f m (q + 1) s :=
        funext (chainV_update_neg K L f m (q + 1) (by omega) (by omega))
      rw [e, volterra_neg_fun]

/-- **`RegTo` through a chain**: one factor `j` depends on the variable `x`. -/
theorem regTo_chainV {K : ℕ → ℝ → ℝ → ℂ} (hK : ∀ i, KCont (K i)) {f : ℝ → ℂ} (hf : Continuous f)
    {M : ℝ → ℝ → ℝ → ℂ} {L : ℝ → ℝ → ℂ}
    (hML : ∀ g : ℝ → ℂ, Continuous g → RegTo (fun x z => volterra (M x) g z) (volterra L g))
    {j : ℕ} : ∀ (m q : ℕ), q ≤ j → j < q + m →
      RegTo (fun x => chainV (update K j (M x)) f m q) (chainV (update K j L) f m q)
  | 0, _, h1, h2 => by omega
  | m + 1, q, h1, h2 => by
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · have hc : ∀ (M' : ℝ → ℝ → ℂ), chainV (update K q M') f m (q + 1) = chainV K f m (q + 1) :=
        fun M' => chainV_congr f m (q + 1) fun i hi _ => update_of_ne (by omega) _ _
      have e1 : (fun x => chainV (update K q (M x)) f (m + 1) q) =
          fun x z => volterra (M x) (chainV K f m (q + 1)) z := by
        funext x z; simp only [chainV, update_self, hc]
      have e2 : chainV (update K q L) f (m + 1) q = volterra L (chainV K f m (q + 1)) := by
        simp only [chainV, update_self, hc]
      rw [e1, e2]
      exact hML _ (continuous_chainV hK hf m (q + 1))
    · have e1 : (fun x => chainV (update K j (M x)) f (m + 1) q) =
          fun x z => volterra (K q) (chainV (update K j (M x)) f m (q + 1)) z := by
        funext x z; simp only [chainV, update_of_ne (Nat.ne_of_lt hlt)]
      have e2 : chainV (update K j L) f (m + 1) q = volterra (K q) (chainV (update K j L) f m (q + 1)) := by
        simp only [chainV, update_of_ne (Nat.ne_of_lt hlt)]
      rw [e1, e2]
      exact (regTo_chainV hK hf hML m (q + 1) (by omega) (by omega)).volterra_left (hK q)

/-! ### The dominant chain -/

section Dominant

variable {P : Type*} {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

omit [DecidableEq V] in
/-- **`Ĩ_Z(g)(t)` for the dominant code is the chain of its pieces.** -/
theorem volterra_tildeP_domCode (Z : Finset ℕ) (p : P) (α : V → ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    ∀ (m q : ℕ) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 →
      volterra (tildeP σ ε μf Z (domCode (m + 1)) q p α) g t =
        chainV (fun j => piece58 σ ε μf Z j p α) g (m + 1) q t
  | 0, q, t, _ => rfl
  | m + 1, q, t, ht => by
    have e : tildeP σ ε μf Z (domCode (m + 2)) q p α =
        kcomp (piece58 σ ε μf Z q p α) (tildeP σ ε μf Z (domCode (m + 1)) (q + 1) p α) := rfl
    rw [e, volterra_kcomp (continuous_piece58 Z q p α) (continuous_tildeP Z p α _ _) hg ht.1]
    show _ = volterra (piece58 σ ε μf Z q p α)
      (chainV (fun j => piece58 σ ε μf Z j p α) g (m + 1) (q + 1)) t
    exact volterra_congr _ (fun s hs => volterra_tildeP_domCode Z p α hg m (q + 1) hs) ht

/-- The pieces with `α_j` updated: only the factor `j` sees the update. -/
theorem pieces_update {Z : Finset ℕ} {m q j : ℕ} (hinj : Set.InjOn σ (Set.Ico q (q + m)))
    (hj : j ∈ Finset.Ico q (q + m)) (hjZ : j ∉ Z) (p : P) (α : V → ℝ) (x : ℝ) :
    ∀ i, q ≤ i → i < q + m → piece58 σ ε μf Z i p (update α (σ j) x) =
      update (fun i => piece58 σ ε μf Z i p α) j (tr58K (ε j) (μf j p) x) i := by
  intro i hi1 hi2
  have hj' : j ∈ Set.Ico q (q + m) := by simpa using hj
  rcases eq_or_ne i j with rfl | hne
  · rw [update_self]
    funext t s
    simp only [piece58, hjZ, ite_false]
    rw [TR58_eq, update_self]
  · rw [update_of_ne hne]
    have hσ : σ i ≠ σ j := fun h => hne (hinj ⟨hi1, hi2⟩ hj' h)
    by_cases hiZ : i ∈ Z
    · simp only [piece58, hiZ, ite_true]; rfl
    · funext t s
      simp only [piece58, hiZ, ite_false]
      rw [TR58_eq, TR58_eq, update_of_ne hσ]

omit [DecidableEq V] in
/-- The `I_μ` limit is minus the `j ∈ Z` piece. -/
theorem pieces_insert {Z : Finset ℕ} (j : ℕ) (p : P) (α : V → ℝ) :
    ∀ i, piece58 σ ε μf (insert j Z) i p α =
      update (fun i => piece58 σ ε μf Z i p α) j (fun t s => -iker (μf j p) t s) i := by
  intro i
  rcases eq_or_ne i j with rfl | hne
  · rw [update_self]
    simp only [piece58, Finset.mem_insert_self, ite_true]
    rfl
  · rw [update_of_ne hne]
    show piece58 σ ε μf (insert j Z) i p α = piece58 σ ε μf Z i p α
    rw [piece58_congr (σ := σ) (ε := ε) (μf := μf) (Z := insert j Z) (Z' := Z) (q := i)
      (by simp [hne])]

omit [DecidableEq V] in
theorem kcont_piece58 (Z : Finset ℕ) (p : P) (α : V → ℝ) (j : ℕ) :
    KCont (piece58 σ ε μf Z j p α) := continuous_piece58 Z j p α

/-- **The peeling induction** on the number of `j ∉ Z`. -/
theorem mint_chainV_domCode (hε : ∀ j, ε j = 1 ∨ ε j = -1) {m q : ℕ}
    (hinj : Set.InjOn σ (Set.Ico q (q + m))) (p : P) {f : ℝ → ℂ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ)
    (hint : ∀ Z ⊆ Finset.Ico q (q + m), MInt ((Finset.Ico q (q + m) \ Z).image σ)
      (fun α => chainV (fun j => piece58 σ ε μf Z j p α) f m q t) α₀) :
    ∀ (n : ℕ) (Z : Finset ℕ), Z ⊆ Finset.Ico q (q + m) → (Finset.Ico q (q + m) \ Z).card = n →
      mint ((Finset.Ico q (q + m) \ Z).image σ)
        (fun α => chainV (fun j => piece58 σ ε μf Z j p α) f m q t) α₀ =
        (-1) ^ Z.card * chainV (fun j => iker (μf j p)) f m q t := by
  intro n
  induction n with
  | zero =>
    intro Z hZ hn
    have hZe : Z = Finset.Ico q (q + m) :=
      Finset.Subset.antisymm hZ (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hn))
    subst hZe
    rw [Finset.sdiff_self, Finset.image_empty, mint_empty, Nat.card_Ico, Nat.add_sub_cancel_left]
    rw [chainV_congr f m q (K' := fun j t s => -iker (μf j p) t s) fun j h1 h2 => by
      simp only [piece58, show j ∈ Finset.Ico q (q + m) by simp; omega, ite_true]; rfl]
    exact chainV_neg _ f m q t
  | succ n ih =>
    intro Z hZ hn
    obtain ⟨j, hj⟩ : (Finset.Ico q (q + m) \ Z).Nonempty := Finset.card_pos.1 (by omega)
    have hjI : j ∈ Finset.Ico q (q + m) := (Finset.mem_sdiff.1 hj).1
    have hjZ : j ∉ Z := (Finset.mem_sdiff.1 hj).2
    have hjI' : q ≤ j ∧ j < q + m := by simpa using hjI
    set Z' := insert j Z with hZ'
    have hZ'I : Z' ⊆ Finset.Ico q (q + m) := Finset.insert_subset hjI hZ
    have hsd : Finset.Ico q (q + m) \ Z = insert j (Finset.Ico q (q + m) \ Z') := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert, hZ']
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr ⟨h1, by tauto⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hjI, hjZ⟩
        · exact ⟨h1, by tauto⟩
    have hjn : j ∉ Finset.Ico q (q + m) \ Z' := by simp [hZ']
    have hn' : (Finset.Ico q (q + m) \ Z').card = n := by
      rw [hsd, Finset.card_insert_of_notMem hjn] at hn; omega
    set W' := (Finset.Ico q (q + m) \ Z').image σ with hW'
    have hσj : σ j ∉ W' := by
      rw [hW', Finset.mem_image]
      rintro ⟨i, hi, hij⟩
      have hiI : i ∈ Set.Ico q (q + m) := by
        have := (Finset.mem_sdiff.1 hi).1; simpa using this
      have := hinj hiI (by simpa using hjI) hij
      subst this
      exact hjn hi
    have hW : (Finset.Ico q (q + m) \ Z).image σ = W' ∪ {σ j} := by
      rw [hsd, Finset.image_insert, Finset.insert_eq, Finset.union_comm]
    set F : (V → ℝ) → ℂ := fun α => chainV (fun j => piece58 σ ε μf Z j p α) f m q t with hF
    have hFint : MInt (W' ∪ {σ j}) F α₀ := by rw [← hW]; exact hint Z hZ
    rw [hW, mint_union_singleton hσj hFint]
    -- the inner integral, for almost every value of the other variables
    have hsec := hFint.union_singleton hσj
    have hinner : ∀ α : V → ℝ, Integrable (fun x : ℝ => F (update α (σ j) x)) →
        ∫ x : ℝ, F (update α (σ j) x) =
          -chainV (fun i => piece58 σ ε μf Z' i p α) f m q t := by
      intro α hi
      have e1 : (fun x : ℝ => F (update α (σ j) x)) = fun x =>
          chainV (update (fun i => piece58 σ ε μf Z i p α) j (tr58K (ε j) (μf j p) x)) f m q t := by
        funext x
        exact congrFun (chainV_congr f m q fun i h1 h2 => pieces_update hinj hjI hjZ p α x i h1 h2) t
      have hR := regTo_chainV (K := fun i => piece58 σ ε μf Z i p α) (kcont_piece58 Z p α) hf
        (M := tr58K (ε j) (μf j p)) (L := iker (μf j p)) (fun g hg => regTo_tr58 (hε j) _ hg)
        m q hjI'.1 hjI'.2
      rw [e1] at hi ⊢
      rw [hR.integral_eq ht hi]
      rw [chainV_congr f m q (K' := update (fun i => piece58 σ ε μf Z i p α) j
        (fun t s => -iker (μf j p) t s)) fun i _ _ => pieces_insert j p α i]
      rw [chainV_update_neg _ _ f m q hjI'.1 hjI'.2, neg_neg]
    rw [mint_congr_ae (G := fun α => -chainV (fun i => piece58 σ ε μf Z' i p α) f m q t)
      (hsec.mono fun y hy => hinner _ hy), mint_neg, ih Z' hZ'I hn',
      Finset.card_insert_of_notMem hjZ, pow_succ]
    ring

end Dominant

/-! ### The statement -/

section Statement

variable {P : Type*} [MeasurableSpace P] {V : Type} [DecidableEq V] {θ A : ℝ}
variable {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem image_Ico_sdiff_domCode {m q : ℕ} {Z : Finset ℕ} (hZ : Z ⊆ Finset.Ico q (q + m)) :
    σ '' (Set.Ico q (q + (domCode m).size) \ (↑Z ∩ ↑(adjSet (domCode m) q))) =
      ↑((Finset.Ico q (q + m) \ Z).image σ) := by
  rw [size_domCode, adjSet_domCode, Finset.coe_image, Finset.coe_sdiff, Finset.coe_Ico]
  congr 1
  ext j
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_coe, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h, by simpa using hZ h⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.1⟩

/-- **DH21 Lemma 7.3** (`regchaincal`, L1732–L1746), **with the corrected sign (F61)**. Let
`𝒫 = {{1,2}, …, {2m-1,2m}}` be the dominant partition (`domCode m`, pairs `q, …, q+m-1`, `m ≥ 1`),
with signs `ε_j = ±1`, distinct variables `α_j = α (σ j)` and measurable `μ_j = μf j p`. For
`Z ⊆ {q, …, q+m-1}`, let `Ĩ_Z` be the operator of Lemma 5.10, `K̃ = Ĩ_Z(e^{πiλ₀s})(t)` with
`t ∈ [0,1]`, and `W = {α_j : j ∉ Z}`. Then `K̃ ∈ L¹(α[W])` (the other variables fixed at `α₀`), and
`∫ K̃ dα[W] = (-1)^{|Z|} ∫_{t>t₁>⋯>t_m>0} e^{πi(μ₁t₁+⋯+μ_mt_m)+πiλ₀t_m} dt`.
DH21 (regchaincalref) omits the factor `(-1)^{|Z|}`. -/
theorem regchaincal (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) {m q : ℕ} (hm : m ≠ 0) (hinj : Set.InjOn σ (Set.Ico q (q + m)))
    {Z : Finset ℕ} (hZ : Z ⊆ Finset.Ico q (q + m)) (p : P) (lam : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (α₀ : V → ℝ) :
    MInt ((Finset.Ico q (q + m) \ Z).image σ)
      (fun α => volterra (tildeP σ ε μf Z (domCode m) q p α) (expF lam) t) α₀ ∧
    mint ((Finset.Ico q (q + m) \ Z).image σ)
      (fun α => volterra (tildeP σ ε μf Z (domCode m) q p α) (expF lam) t) α₀ =
      (-1) ^ Z.card * simplexInt (fun j => μf j p) lam m q t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hinj' : Set.InjOn σ (Set.Ico q (q + (domCode (k + 1)).size)) := by
    rwa [size_domCode]
  -- integrability, from the class `J` + `R` bounds (Lemma 5.10)
  have hint : ∀ Z' ⊆ Finset.Ico q (q + (k + 1)), MInt ((Finset.Ico q (q + (k + 1)) \ Z').image σ)
      (fun α => volterra (tildeP σ ε μf Z' (domCode (k + 1)) q p α) (expF lam) t) α₀ := by
    intro Z' hZ'
    have hM := (lemma510 (σ := σ) (ε := ε) (μf := μf) h0 h1 hA hε hμ (domCode_ne_nil hm)
      hinj').2.2 Z'
    rw [image_Ico_sdiff_domCode hZ'] at hM
    exact mJR_mInt_volterra hM h0 p lam ht α₀
  have e : ∀ Z' : Finset ℕ, (fun α => volterra (tildeP σ ε μf Z' (domCode (k + 1)) q p α)
      (expF lam) t) = fun α => chainV (fun j => piece58 σ ε μf Z' j p α) (expF lam) (k + 1) q t :=
    fun Z' => funext fun α => volterra_tildeP_domCode Z' p α (continuous_expF lam) k q ht
  refine ⟨hint Z hZ, ?_⟩
  rw [e]
  exact mint_chainV_domCode hε hinj p (continuous_expF lam) ht α₀
    (fun Z' hZ' => by rw [← e]; exact hint Z' hZ') _ Z hZ rfl

end Statement

end WaveTurbulence.Cancel
