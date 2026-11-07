/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.MixIndicator

/-! # `ε` as a character mixture (DEGEN-VINE)

`ε_{k₁k₂k₃} = 1 - 1[k₂ = k₁] - 1[k₂ = k₃]` (`DegenVine.epsCoef_eq_one_sub`), with each `kᵢ` an affine form
`∑ᵥ cᵥ Xᵥ + ∑ₖ hₖ Eₖ` (a row of the `sumint` datum or a boundary vector).  Hence the node factor is a
character mixture of mass `3`, and a product over `n` nodes a mixture of mass `3^n`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence MeasureTheory

variable {d : ℕ} {S : SumintShape}

/-- `ε_{k₁k₂k₃}` on physical momenta (T (defcoef0)); `epsCoef` on lattice indices. -/
noncomputable def epsMom (a b c : Mom d) : ℝ := if b ≠ a ∧ b ≠ c then 1 else if a = b ∧ b = c then -1 else 0

theorem epsMom_eq_one_sub (a b c : Mom d) :
    epsMom a b c = 1 - (if b = a then 1 else 0) - (if b = c then 1 else 0) := by
  unfold epsMom
  by_cases h1 : b = a
  · by_cases h3 : b = c
    · subst h1; subst h3; simp
    · subst h1; simp [h3]
  · by_cases h3 : b = c
    · subst h3; simp [h1]; exact fun h => h1 h.symm
    · simp [h1, h3]

theorem latticePoint_injective {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro m n h
  funext j
  have := congrArg (fun p : Mom d => p j) h
  simp only [latticePoint, PiLp.toLp_apply] at this
  have h2 : (m j : ℝ) = (n j : ℝ) := by
    field_simp at this; exact this
  exact_mod_cast h2

/-- **`epsMom` on lattice-shifted momenta is `epsCoef`** (the bridge to V4's `clRegionalEpsilon`). -/
theorem epsMom_latticePoint {L : ℝ} (hL : L ≠ 0) (base : Mom d) (n₁ n₂ n₃ : Fin d → ℤ) :
    epsMom (base + latticePoint L n₁) (base + latticePoint L n₂) (base + latticePoint L n₃) =
      epsCoef n₁ n₂ n₃ := by
  have inj := latticePoint_injective (d := d) hL
  unfold epsMom epsCoef
  simp only [ne_eq, add_right_inj, inj.eq_iff]

/-- An affine form `∑ᵥ cᵥ Xᵥ + ∑ₖ hₖ Eₖ` with coefficient sum `∑ₖ hₖ = 1` (a coset-preserving label). -/
structure AffRef (S : SumintShape) where
  c : S.VIdx → ℤ
  h : Fin 4 → ℤ
  hsum : ∑ k, h k = 1

/-- The label value. -/
noncomputable def AffRef.val (r : AffRef S) (L : ℝ) (x : S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) : Mom d :=
  CharMix.affVal S L r.c r.h x E

namespace CharMix

/-- The (negated) indicator of `r₂ = r₁`. -/
noncomputable def negInd (S : SumintShape) (d : ℕ) (L : ℝ) (r₁ r₂ : AffRef S) : CharMix S d :=
  neg (indicator S d L (fun v => r₂.c v - r₁.c v) (fun k => r₂.h k - r₁.h k))

/-- The node mixture `1 - 1[k₂ = k₁] - 1[k₂ = k₃]`. -/
noncomputable def epsNode (S : SumintShape) (d : ℕ) (L : ℝ) (r₁ r₂ r₃ : AffRef S) : CharMix S d :=
  add (add (one S d) (negInd S d L r₁ r₂)) (negInd S d L r₃ r₂)

theorem mass_epsNode (L : ℝ) (r₁ r₂ r₃ : AffRef S) : (epsNode S d L r₁ r₂ r₃).mass = 3 := by
  unfold epsNode negInd
  rw [mass_add, mass_add, mass_one, mass_neg, mass_neg, mass_indicator, mass_indicator]
  norm_num

theorem affVal_sub (L : ℝ) (c c' : S.VIdx → ℤ) (h h' : Fin 4 → ℤ) (x : S.VIdx → Fin d → ℤ)
    (E : Fin 4 → Mom d) :
    affVal S L (fun v => c v - c' v) (fun k => h k - h' k) x E =
      affVal S L c h x E - affVal S L c' h' x E := by
  unfold affVal
  simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
  abel

/-- A difference of two labels is a lattice point, for coset-valued outputs. -/
theorem exists_lattice_affVal {L : ℝ} (hL : L ≠ 0) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ)
    (hsum : ∑ k, h k = 0) (wBar : Mom d) (E : Fin 4 → Mom d)
    (hE : ∀ k, ∃ nv : Fin d → ℤ, E k = wBar + latticePoint L nv) (x : S.VIdx → Fin d → ℤ) :
    ∃ n : Fin d → ℤ, affVal S L c h x E = latticePoint L n := by
  choose nv hnv using hE
  let f : (Fin d → ℤ) →+ Mom d :=
    { toFun := latticePoint L
      map_zero' := by ext j; simp [latticePoint]
      map_add' := fun m n => by ext j; simp [latticePoint, add_div] }
  refine ⟨∑ v, c v • x v + ∑ k, h k • nv k, ?_⟩
  have e1 : ∀ n, latticePoint L n = f n := fun n => rfl
  rw [e1, map_add, map_sum, map_sum]
  unfold affVal
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, e1]; simp [Int.cast_smul_eq_zsmul]
  · have : ∑ k, (h k : ℝ) • E k = ∑ k, ((h k : ℝ) • wBar + (h k : ℝ) • latticePoint L (nv k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hnv k, smul_add]
    rw [this, Finset.sum_add_distrib, ← Finset.sum_smul]
    have h0 : (∑ k, (h k : ℝ)) = 0 := by exact_mod_cast hsum
    rw [h0, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, e1]; simp [Int.cast_smul_eq_zsmul]

/-- **The node mixture computes `ε`.** -/
theorem val_epsNode {L : ℝ} (hL : L ≠ 0) (r₁ r₂ r₃ : AffRef S) (wBar : Mom d) (E : Fin 4 → Mom d)
    (hE : ∀ k, ∃ nv : Fin d → ℤ, E k = wBar + latticePoint L nv) (x : S.VIdx → Fin d → ℤ) :
    (epsNode S d L r₁ r₂ r₃).val L E x = ((epsMom (r₁.val L x E) (r₂.val L x E) (r₃.val L x E) : ℝ) : ℂ) := by
  have hind : ∀ (ra rb : AffRef S), (indicator S d L (fun v => rb.c v - ra.c v)
      (fun k => rb.h k - ra.h k)).val L E x = if rb.val L x E = ra.val L x E then 1 else 0 := by
    intro ra rb
    have hs : ∑ k, (rb.h k - ra.h k) = 0 := by rw [Finset.sum_sub_distrib, rb.hsum, ra.hsum]; simp
    obtain ⟨n, hn⟩ := exists_lattice_affVal hL (fun v => rb.c v - ra.c v) (fun k => rb.h k - ra.h k)
      hs wBar E hE x
    rw [val_indicator hL _ _ E x n hn]
    have : rb.val L x E = ra.val L x E ↔ n = 0 := by
      have h2 : rb.val L x E - ra.val L x E = latticePoint L n := by
        rw [← hn]; exact (affVal_sub L rb.c ra.c rb.h ra.h x E).symm
      rw [← sub_eq_zero, h2]
      constructor
      · intro h0
        funext j
        have := congrArg (fun p : Mom d => p j) h0
        simp [latticePoint, hL] at this
        simpa using this
      · intro h0; subst h0; ext j; simp [latticePoint]
    simp only [this]
  unfold epsNode negInd
  rw [val_add, val_add, val_one, val_neg, val_neg, hind r₁ r₂, hind r₃ r₂, epsMom_eq_one_sub]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, apply_ite Complex.ofReal, Complex.ofReal_zero]
  ring


/-- Finite products of mixtures are mixtures. -/
theorem exists_prod_mix {ι : Type*} (s : Finset ι) (M : ι → CharMix S d) :
    ∃ N : CharMix S d, (∀ L E x, N.val L E x = ∏ i ∈ s, (M i).val L E x) ∧
      N.mass = ∏ i ∈ s, (M i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨one S d, fun L E x => by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, hN, hm⟩ := ih
    refine ⟨mul (M a) N, fun L E x => ?_, ?_⟩
    · rw [val_mul, hN, Finset.prod_insert ha]
    · rw [mass_mul, hm, Finset.prod_insert ha]

end CharMix

/-- **`ε` over `n` nodes is a character mixture of mass `3^n`.**  Node `i` has the three labels
`lab₁ i, lab₂ i, lab₃ i` (affine forms in the lattice inputs and the boundary vectors). -/
theorem exists_eps_mix {ι : Type*} [Fintype ι] {L : ℝ} (hL : L ≠ 0) (lab₁ lab₂ lab₃ : ι → AffRef S)
    (wBar : Mom d) :
    ∃ N : CharMix S d, N.mass = 3 ^ Fintype.card ι ∧
      ∀ (E : Fin 4 → Mom d), (∀ k, ∃ nv : Fin d → ℤ, E k = wBar + latticePoint L nv) →
        ∀ x : S.VIdx → Fin d → ℤ, N.val L E x =
          ((∏ i, epsMom ((lab₁ i).val L x E) ((lab₂ i).val L x E) ((lab₃ i).val L x E) : ℝ) : ℂ) := by
  obtain ⟨N, hN, hm⟩ := CharMix.exists_prod_mix (Finset.univ : Finset ι)
    (fun i => CharMix.epsNode S d L (lab₁ i) (lab₂ i) (lab₃ i))
  refine ⟨N, ?_, fun E hE x => ?_⟩
  · rw [hm]; simp [CharMix.mass_epsNode]
  · rw [hN, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => CharMix.val_epsNode hL _ _ _ wBar E hE x

end WaveTurbulence.DegenVine
