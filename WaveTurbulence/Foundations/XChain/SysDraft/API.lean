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

/-- **Uniqueness** in the class (landed `NLS.IsAkSolution.eq_of_eq`). -/
theorem unique (hL : 0 < L) {b : ℝ → (Fin d → ℤ) → ℂ} (ha : IsASolution L γ δ T c a)
    (hb : IsASolution L γ δ T c b) : ∀ t ∈ Icc 0 T, a t = b t :=
  NLS.IsAkSolution.eq_of_eq hL ha hb

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

theorem measurable (h : AnsatzAt P μ g a Fev R E Et p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) p)
    (n : Fin P.d → ℤ) : Measurable fun ω => a ω t n := h.1.2.2.2.2.2.1 t ht n

end AnsatzAt

/-! ## §3 Joint cumulants (landed cumulant layer; `jointCumulant = cumulant` by definition) -/

section Cumulant

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

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
