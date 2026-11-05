/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.NLS.AkUnique
public import WaveTurbulence.Foundations.NLS.AkClass
public import WaveTurbulence.Foundations.NLS.AkMass
public import WaveTurbulence.Foundations.NLS.Convolution
public import WaveTurbulence.Foundations.Cumulant.Inversion
public import WaveTurbulence.Foundations.Cumulant.Symmetry
public import WaveTurbulence.Foundations.Cumulant.ProductsFormula

/-!
# D2 SYS-DEFS API, part 1 (scratch, against snapshot 4)

Basic lemmas about the frozen system objects of `WaveB1-System`, for the gate provers:

* §1 classed `a`-system solutions `IsASolution`: initial value, derivative, restriction (`mono`),
  **gluing at a time `p`** (the inductive step of `propansatz`), and, through the definitional bridge to
  the landed `NLS.IsAkSolution`, uniqueness, the integral (Duhamel) form, mass conservation,
  continuity and the weighted bound;
* §2 named accessors for the conjuncts of `AnsatzAt`;
* §3 `jointCumulant`: empty and singleton values, scaling, the moment–cumulant inversion, gauge and
  translation vanishing, invariance under equality in law, and the products formula (all from the
  landed cumulant layer, `jointCumulant = cumulant` by definition);
* §4 the nonlinearity `aNonlin`: the pair form, absolute summability of its terms, the weighted bound,
  and **multilinearity** over finite sums (for inputs with summable norms).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.SysAPI

/-! ## §1 Classed solutions -/

namespace IsASolution

variable {d : ℕ} {L γ δ T : ℝ} {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

theorem toNLS (h : IsASolution L γ δ T c a) : NLS.IsAkSolution L γ δ T c a := h

theorem ofNLS (h : NLS.IsAkSolution L γ δ T c a) : IsASolution L γ δ T c a := h

theorem initial (h : IsASolution L γ δ T c a) : a 0 = c := h.1

theorem hasDerivWithinAt (h : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => a s n)
      (aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n) (Icc 0 T) t :=
  h.2.2 t ht n

/-- A solution on `[0, T]` is a solution on every `[0, T']`, `T' ≤ T` (glue list, delta-stage-3 O5). -/
theorem mono (h : IsASolution L γ δ T c a) {T' : ℝ} (hT' : T' ≤ T) : IsASolution L γ δ T' c a := by
  obtain ⟨h0, ⟨C, hC⟩, hD⟩ := h
  exact ⟨h0, ⟨C, fun t ht n => hC t ⟨ht.1, ht.2.trans hT'⟩ n⟩,
    fun t ht n => (hD t ⟨ht.1, ht.2.trans hT'⟩ n).mono (Icc_subset_Icc le_rfl hT')⟩

/-- **Uniqueness** in the class (landed `NLS.IsAkSolution.eq_of_eq`). -/
theorem unique (hL : 0 < L) {b : ℝ → (Fin d → ℤ) → ℂ} (ha : IsASolution L γ δ T c a)
    (hb : IsASolution L γ δ T c b) : ∀ t ∈ Icc 0 T, a t = b t :=
  NLS.IsAkSolution.eq_of_eq hL ha hb

/-- **The integral form** `a_n(t) = c_n + ∫_0^t 𝒞₊(a, ā, a)_n` (landed `eq_add_integral`). -/
theorem eq_add_integral (hL : 0 < L) (ha : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) :
    a t n = c n + ∫ s in (0 : ℝ)..t,
      aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n :=
  NLS.IsAkSolution.eq_add_integral hL ha ht n

/-- **Mass conservation** `∑_n |a_n(t)|² = ∑_n |c_n|²` (landed `tsum_normSq_eq`; glue list). -/
theorem tsum_normSq_eq (hL : 0 < L) (ha : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∑' n, ‖a t n‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 :=
  NLS.IsAkSolution.tsum_normSq_eq hL ha ht

theorem continuousOn (ha : IsASolution L γ δ T c a) (n : Fin d → ℤ) :
    ContinuousOn (fun s => a s n) (Icc 0 T) :=
  NLS.IsAkSolution.continuousOn ha n

/-- The class bound in the form `|a_n(t)| ≤ C (1 + |n|)^{-(d+1)}`. -/
theorem exists_norm_le (hL : 0 < L) (ha : IsASolution L γ δ T c a) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ n, ‖a t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ :=
  NLS.IsAkBounded.exists_norm_le hL ha.2.1

/-- A classed solution has summable lattice values at every time of `[0, T]` (the data condition of the
Duhamel lemmas). -/
theorem summable_norm (hL : 0 < L) (ha : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Summable fun n => ‖a t n‖ := by
  obtain ⟨C, -, hC⟩ := exists_norm_le hL ha
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hC t ht n)
    (NLS.summable_inv_one_add_norm_pow.mul_left C)

/-- **Gluing** (the inductive step of `propansatz`): a classed solution on `[0, p]` and a classed
solution of the same (non-autonomous) equation on `[p, q]` starting from its value at `p` give a
classed solution on `[0, q]` (the one-sided derivatives at `p` agree, both being `𝒞₊(a(p))`). -/
theorem glue {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (ha : IsASolution L γ δ p c a)
    (b : ℝ → (Fin d → ℤ) → ℂ) (hb0 : b p = a p)
    (hbC : ∃ C, ∀ t ∈ Icc p q, ∀ n,
      (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖b t n‖ ≤ C)
    (hbD : ∀ t ∈ Icc p q, ∀ n, HasDerivWithinAt (fun s => b s n)
      (aNonlin L γ δ 1 t (b t) (fun m => (starRingEnd ℂ) (b t m)) (b t) n) (Icc p q) t) :
    IsASolution L γ δ q c (fun s => if s ≤ p then a s else b s) := by
  obtain ⟨ha0, ⟨Ca, hCa⟩, haD⟩ := ha
  obtain ⟨Cb, hCb⟩ := hbC
  set g : ℝ → (Fin d → ℤ) → ℂ := fun s => if s ≤ p then a s else b s with hg
  have hga : ∀ s ∈ Icc 0 p, g s = a s := fun s hs => by simp [hg, hs.2]
  have hgb : ∀ s ∈ Icc p q, g s = b s := by
    intro s hs
    by_cases h : s ≤ p
    · have : s = p := le_antisymm h hs.1
      subst this
      simp [hg, hb0]
    · simp [hg, h]
  refine ⟨?_, ⟨max Ca Cb, fun t ht n => ?_⟩, fun t ht n => ?_⟩
  · simpa [hg, hp] using ha0
  · by_cases htp : t ≤ p
    · rw [hga t ⟨ht.1, htp⟩]
      exact (hCa t ⟨ht.1, htp⟩ n).trans (le_max_left _ _)
    · rw [hgb t ⟨(not_le.1 htp).le, ht.2⟩]
      exact (hCb t ⟨(not_le.1 htp).le, ht.2⟩ n).trans (le_max_right _ _)
  · have hunion : Icc 0 q = Icc 0 p ∪ Icc p q := (Icc_union_Icc_eq_Icc hp hpq).symm
    rw [hunion]
    refine HasDerivWithinAt.union ?_ ?_
    · by_cases htp : t ∈ Icc 0 p
      · have h1 := haD t htp n
        rw [hga t htp]
        exact h1.congr (fun s hs => by rw [hga s hs]) (by rw [hga t htp])
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rwa [closure_Icc]
    · by_cases htp : t ∈ Icc p q
      · have h1 := hbD t htp n
        rw [hgb t htp]
        exact h1.congr (fun s hs => by rw [hgb s hs]) (by rw [hgb t htp])
      · refine HasFDerivWithinAt.of_notMem_closure ?_
        rwa [closure_Icc]

end IsASolution

/-! ## §2 The conjuncts of `AnsatzAt` -/

namespace AnsatzAt

variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ} {Fev : ℕ → Set Ω}
  {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ} {p : ℕ}

theorem measurableSet (h : AnsatzAt P μ g a Fev R E Et p) : MeasurableSet (Fev p) := h.1.1

theorem isSymmetricEvent (h : AnsatzAt P μ g a Fev R E Et p) :
    IsSymmetricEvent P.L P.φin g (Fev p) := h.1.2.1

theorem nested (h : AnsatzAt P μ g a Fev R E Et p) (hp : 1 ≤ p) : Fev p ⊆ Fev (p - 1) :=
  h.1.2.2.1 hp

theorem prob_ge (h : AnsatzAt P μ g a Fev R E Et p) :
    1 - Real.exp (-(P.N p : ℝ)) ≤ μ.real (Fev p) := h.1.2.2.2.1

theorem isASolution (h : AnsatzAt P μ g a Fev R E Et p) {ω : Ω} (hω : ω ∈ Fev p) :
    IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) := (h.1.2.2.2.2.1 ω hω).1

theorem eq_of_isASolution (h : AnsatzAt P μ g a Fev R E Et p) {ω : Ω} (hω : ω ∈ Fev p)
    {b : ℝ → (Fin P.d → ℤ) → ℂ} (hb : IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) b) :
    ∀ t ∈ Icc (0 : ℝ) p, b t = a ω t := (h.1.2.2.2.2.1 ω hω).2 b hb

theorem measurable (h : AnsatzAt P μ g a Fev R E Et p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) p)
    (n : Fin P.d → ℤ) : Measurable fun ω => a ω t n := h.1.2.2.2.2.2.1 t ht n

theorem integrable_prod (h : AnsatzAt P μ g a Fev R E Et p) (r : ℕ) (t : Fin r → Icc (0 : ℝ) p)
    (n : Fin r → (Fin P.d → ℤ)) (ζ : Fin r → ℤˣ) :
    Integrable (fun ω => ∏ j, zpowSign (ζ j) (a ω (t j) (n j))) (μ.restrict (Fev p)) :=
  h.1.2.2.2.2.2.2 r t n ζ

theorem remainder_bound (h : AnsatzAt P μ g a Fev R E Et p) :
    SNormR (P.Lambda p) (P.Lambda p) (R p) ≤ ENNReal.ofReal (P.L ^ (-P.theta p)) := h.2.1.1

theorem error_bound (h : AnsatzAt P μ g a Fev R E Et p) (n : Fin P.d → ℤ) :
    |E p n| ≤ jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)) * Real.exp (-(P.N p : ℝ)) :=
  h.2.1.2.1 n

theorem two_point (h : AnsatzAt P μ g a Fev R E Et p) (n n' : Fin P.d → ℤ) :
    ∫ ω in Fev p, a ω p n * (starRingEnd ℂ) (a ω p n') ∂μ =
      if n = n' then ((P.φ (P.δ * p) (latticePoint P.L n) + R p (latticePoint P.L n) + E p n : ℝ)
        : ℂ) else 0 := h.2.1.2.2 n n'

theorem two_point_intermediate (h : AnsatzAt P μ g a Fev R E Et p) (hp : 1 ≤ p) {t : ℝ}
    (ht : t ∈ Icc ((p : ℝ) - 1) p) (n : Fin P.d → ℤ) :
    |(∫ ω in Fev p, ‖a ω t n‖ ^ 2 ∂μ) - P.φ (P.δ * t) (latticePoint P.L n)| ≤
      2 * P.L ^ (-P.theta p) := h.2.2.1 hp t ht n

theorem cumulant_expansion (h : AnsatzAt P μ g a Fev R E Et p) {m : ℕ} (hm : 2 ≤ m)
    (hmR : m ≤ P.R p) {ζ : Fin (2 * m) → ℤˣ} (hζ : ∑ j, ((ζ j : ℤˣ) : ℤ) = 0)
    (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    jointCumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (ζ j) (a ω p (n j))) Finset.univ =
        (∑ N ∈ Finset.range (P.N p + 1), truncSum P (inputsF P R) p N (p : ℝ) ζ n) +
          Et p m ζ n ∧
      (∑ j, ((ζ j : ℤˣ) : ℤ) • n j ≠ 0 → Et p m ζ n = 0) ∧
      ‖Et p m ζ n‖ ≤ (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
        Real.exp (-(P.N p : ℝ)) := h.2.2.2.1 m hm hmR ζ hζ n

theorem order_bound (h : AnsatzAt P μ g a Fev R E Et p) {m : ℕ} (hm : 2 ≤ m) (hmR : m ≤ P.R p)
    {ζ : Fin (2 * m) → ℤˣ} (hζ : ∑ j, ((ζ j : ℤˣ) : ℤ) = 0) (n : Fin (2 * m) → (Fin P.d → ℤ))
    {N : ℕ} (hN : N ≤ P.N p) :
    ‖truncSum P (inputsF P R) p N (p : ℝ) ζ n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
        P.L ^ (-((m : ℝ) - 1) / 6) * P.δ ^ (P.ν * N) := h.2.2.2.2 m hm hmR ζ hζ n N hN

end AnsatzAt

/-! ## §3 Joint cumulants (landed cumulant layer; `jointCumulant = cumulant` by definition) -/

section Cumulant

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

theorem jointCumulant_eq_cumulant (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) :
    jointCumulant μ X s = cumulant μ X s := rfl

theorem jointCumulant_empty (μ : Measure Ω) (X : ι → Ω → ℂ) : jointCumulant μ X ∅ = 1 :=
  cumulant_empty μ X

theorem jointCumulant_singleton (μ : Measure Ω) (X : ι → Ω → ℂ) (i : ι) :
    jointCumulant μ X {i} = ∫ ω, X i ω ∂μ := cumulant_singleton μ X i

theorem jointCumulant_mul (μ : Measure Ω) (X : ι → Ω → ℂ) (c : ι → ℂ) (s : Finset ι) :
    jointCumulant μ (fun j ω => c j * X j ω) s = (∏ j ∈ s, c j) * jointCumulant μ X s :=
  cumulant_mul μ X c s

/-- **Moment–cumulant inversion** (T (eqncm2)). -/
theorem integral_prod_eq_sum_jointCumulant (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι)
    (hs : s.Nonempty) :
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) = ∑ P : Finpartition s, ∏ A ∈ P.parts, jointCumulant μ X A :=
  integral_prod_eq_sum_cumulant μ X s hs

/-- **Gauge vanishing** (cumulants of gauge-covariant variables with nonzero total charge vanish). -/
theorem jointCumulant_eq_zero_of_gauge_invariant {μ : Measure Ω} {X : ι → Ω → ℂ}
    (hX : ∀ j, Measurable (X j)) (q : ι → ℝ)
    (hinv : ∀ θ : ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (q j * θ) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) : jointCumulant μ X s = 0 :=
  cumulant_eq_zero_of_gauge_invariant hX q hinv s hq

/-- **Translation vanishing** (momentum conservation in cumulants). -/
theorem jointCumulant_eq_zero_of_translation_invariant {d : ℕ} {μ : Measure Ω} {X : ι → Ω → ℂ}
    (hX : ∀ j, Measurable (X j)) (q : ι → Fin d → ℝ)
    (hinv : ∀ x : Fin d → ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (∑ l, q j l * x l) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) : jointCumulant μ X s = 0 :=
  cumulant_eq_zero_of_translation_invariant hX q hinv s hq

/-- Cumulants depend only on the joint law. -/
theorem jointCumulant_congr_map {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω}
    {ν : Measure Ω'} {X : ι → Ω → ℂ} {Y : ι → Ω' → ℂ} (hX : ∀ j, Measurable (X j))
    (hY : ∀ j, Measurable (Y j)) (hmap : μ.map (fun ω j => X j ω) = ν.map (fun ω j => Y j ω))
    (s : Finset ι) : jointCumulant μ X s = jointCumulant ν Y s :=
  cumulant_congr_map hX hY hmap s

open scoped Classical in
/-- **The products formula** (Leonov–Shiryaev; T Prop `propertycm`). -/
theorem jointCumulant_prod {J : Type*} [DecidableEq J] (μ : Measure Ω) (X : J → Ω → ℂ)
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) :
    jointCumulant μ (fun i ω => ∏ j ∈ S i, X j ω) I =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (I.biUnion S))).filter
        (IsIrreduciblePartition I S), ∏ B ∈ P.parts, jointCumulant μ X B :=
  cumulant_prod μ X I S hS hne

end Cumulant

/-! ## §4 The nonlinearity `aNonlin` -/

section Nonlin

variable {d : ℕ}

/-- `aNonlin` as a sum over pairs `(n₁, n₂)` (`n₃ = n - n₁ + n₂`). -/
theorem aNonlin_eq_tsum_pairs (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) :
    aNonlin L γ δ ζ t f g h n =
      ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ) *
        ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
          (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
            Complex.exp (((ζ * Real.pi * δ * L ^ (2 * γ) *
              resFactor (latticePoint L q.1) (latticePoint L q.2) (latticePoint L (n - q.1 + q.2))
                (latticePoint L n) * t : ℝ) : ℂ) * Complex.I) * f q.1 * g q.2 * h (n - q.1 + q.2) :=
  NLS.aNonlin_eq_tsum_pairs L γ δ ζ t f g h n

/-- The pair terms of `aNonlin`. -/
noncomputable def aNonlinTerm (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
    Complex.exp (((ζ * Real.pi * δ * L ^ (2 * γ) *
      resFactor (latticePoint L q.1) (latticePoint L q.2) (latticePoint L (n - q.1 + q.2))
        (latticePoint L n) * t : ℝ) : ℂ) * Complex.I) * f q.1 * g q.2 * h (n - q.1 + q.2)

theorem norm_aNonlinTerm_le (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖aNonlinTerm L γ δ ζ t f g h n q‖ ≤ ‖f q.1‖ * ‖g q.2‖ * ‖h (n - q.1 + q.2)‖ := by
  unfold aNonlinTerm
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    mul_one]
  have h1 : ‖epsCoef q.1 q.2 (n - q.1 + q.2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    unfold epsCoef
    split_ifs <;> simp
  calc ‖epsCoef q.1 q.2 (n - q.1 + q.2)‖ * ‖f q.1‖ * ‖g q.2‖ * ‖h (n - q.1 + q.2)‖
      ≤ 1 * ‖f q.1‖ * ‖g q.2‖ * ‖h (n - q.1 + q.2)‖ := by gcongr
    _ = _ := by ring

theorem exists_norm_le_of_summable {f : (Fin d → ℤ) → ℂ} (hf : Summable fun m => ‖f m‖) :
    ∃ C, 0 ≤ C ∧ ∀ m, ‖f m‖ ≤ C :=
  ⟨∑' m, ‖f m‖, tsum_nonneg fun _ => norm_nonneg _,
    fun m => hf.le_tsum m fun _ _ => norm_nonneg _⟩

/-- **Absolute summability** of the pair terms for `f, g` with summable norms and `h` bounded. -/
theorem summable_aNonlinTerm (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) {f g h : (Fin d → ℤ) → ℂ}
    (hf : Summable fun m => ‖f m‖) (hg : Summable fun m => ‖g m‖) {C : ℝ} (hh : ∀ m, ‖h m‖ ≤ C)
    (n : Fin d → ℤ) : Summable fun q => ‖aNonlinTerm L γ δ ζ t f g h n q‖ := by
  have hfg : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) => ‖f q.1‖ * ‖g q.2‖ :=
    summable_mul_of_summable_norm (f := fun m => ‖f m‖) (g := fun m => ‖g m‖)
      (by simpa using hf) (by simpa using hg)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hfg.mul_right C)
  refine (norm_aNonlinTerm_le L γ δ ζ t f g h n q).trans ?_
  exact mul_le_mul_of_nonneg_left (hh _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem aNonlin_eq_tsum_aNonlinTerm (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) :
    aNonlin L γ δ ζ t f g h n = ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ) *
      ∑' q, aNonlinTerm L γ δ ζ t f g h n q :=
  aNonlin_eq_tsum_pairs L γ δ ζ t f g h n

/-- **Multilinearity** of `aNonlin` over finite sums, for inputs with summable norms. -/
theorem aNonlin_sum {ι₁ ι₂ ι₃ : Type*} (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (s₁ : Finset ι₁)
    (s₂ : Finset ι₂) (s₃ : Finset ι₃) (f : ι₁ → (Fin d → ℤ) → ℂ) (g : ι₂ → (Fin d → ℤ) → ℂ)
    (h : ι₃ → (Fin d → ℤ) → ℂ) (hf : ∀ i, Summable fun m => ‖f i m‖)
    (hg : ∀ j, Summable fun m => ‖g j m‖) (hh : ∀ k, Summable fun m => ‖h k m‖)
    (n : Fin d → ℤ) :
    aNonlin L γ δ ζ t (fun m => ∑ i ∈ s₁, f i m) (fun m => ∑ j ∈ s₂, g j m)
        (fun m => ∑ k ∈ s₃, h k m) n =
      ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃, aNonlin L γ δ ζ t (f i) (g j) (h k) n := by
  have hsum : ∀ i j k, Summable fun q => aNonlinTerm L γ δ ζ t (f i) (g j) (h k) n q := by
    intro i j k
    obtain ⟨C, -, hC⟩ := exists_norm_le_of_summable (hh k)
    exact (summable_aNonlinTerm L γ δ ζ t (hf i) (hg j) hC n).of_norm
  have hterm : ∀ q, aNonlinTerm L γ δ ζ t (fun m => ∑ i ∈ s₁, f i m) (fun m => ∑ j ∈ s₂, g j m)
      (fun m => ∑ k ∈ s₃, h k m) n q =
      ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃, aNonlinTerm L γ δ ζ t (f i) (g j) (h k) n q := by
    intro q
    unfold aNonlinTerm
    simp only [Finset.mul_sum (s := s₁), Finset.sum_mul (s := s₁)]
    simp only [Finset.mul_sum (s := s₂), Finset.sum_mul (s := s₂)]
    simp only [Finset.mul_sum (s := s₃)]
  have hswap : (∑' q, ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃,
      aNonlinTerm L γ δ ζ t (f i) (g j) (h k) n q) =
      ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃, ∑' q, aNonlinTerm L γ δ ζ t (f i) (g j) (h k) n q := by
    rw [Summable.tsum_finsetSum fun i _ =>
      summable_sum fun j _ => summable_sum fun k _ => hsum i j k]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => summable_sum fun k _ => hsum i j k]
    exact Finset.sum_congr rfl fun j _ => Summable.tsum_finsetSum fun k _ => hsum i j k
  simp only [aNonlin_eq_tsum_aNonlinTerm, hterm]
  rw [hswap]
  simp only [Finset.mul_sum]

end Nonlin

end WaveTurbulence.SysAPI
