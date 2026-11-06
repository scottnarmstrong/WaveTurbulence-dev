/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Integrals over a unit box of products of functions of disjoint coordinate blocks (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open MeasureTheory Set Finset

variable {X : Type*}
set_option linter.unusedSectionVars false

/-- The product of the unit intervals `[a x, a x + 1]`. -/
def ubox [Fintype X] (a : X → ℝ) : Set (X → ℝ) := Set.pi univ (fun x => Icc (a x) (a x + 1))

lemma isCompact_ubox [Fintype X] (a : X → ℝ) : IsCompact (ubox a) := isCompact_univ_pi (fun _ => isCompact_Icc)

lemma volume_ubox_real [Fintype X] (a : X → ℝ) : (volume (ubox a)).toReal = 1 := by
  have : ubox a = Icc a (fun x => a x + 1) := by
    ext t; simp [ubox, Set.mem_Icc, Pi.le_def]
  rw [this, Real.volume_Icc_pi_toReal (fun x => by simp)]
  simp

/-- **Block factorisation** (predicate form). -/
theorem block_integral_pred [Fintype X] [DecidableEq X] (a : X → ℝ) (p : X → Prop) [DecidablePred p]
    (g : ({x // p x} → ℝ) → ℝ)
    (H : (X → ℝ) → ℝ)
    (hH : ∀ t t' : X → ℝ, (∀ x, ¬ p x → t x = t' x) → H t = H t') :
    ∫ t in ubox a, g (fun v : {x // p x} => t v.1) * H t =
      (∫ s in Set.pi univ (fun v : {x // p x} => Icc (a v.1) (a v.1 + 1)), g s) *
        ∫ t in ubox a, H t := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : X => ℝ) p with he
  have hmp : MeasurePreserving e volume (volume : Measure (({x // p x} → ℝ) × ({x // ¬p x} → ℝ))) :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : X => ℝ) p
  set A : Set ({x // p x} → ℝ) := Set.pi univ (fun v : {x // p x} => Icc (a v.1) (a v.1 + 1)) with hA
  set B : Set ({x // ¬p x} → ℝ) := Set.pi univ (fun v : {x // ¬p x} => Icc (a v.1) (a v.1 + 1)) with hB
  have hbox : ubox a = e ⁻¹' (A ×ˢ B) := by
    ext t
    simp only [ubox, hA, hB, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_prod,
      he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, Subtype.forall]
    constructor
    · intro h
      exact ⟨fun x _ => h x, fun x _ => h x⟩
    · rintro ⟨h1, h2⟩ x
      by_cases hx : p x
      · exact h1 x hx
      · exact h2 x hx
  set H₂ : ({x // ¬p x} → ℝ) → ℝ := fun s₂ => H (e.symm (0, s₂)) with hH₂
  have hcomp : ∀ w : ({x // p x} → ℝ) × ({x // ¬p x} → ℝ),
      g (fun v : {x // p x} => (e.symm w) v.1) * H (e.symm w) = g w.1 * H₂ w.2 := by
    intro w
    have h1 : (fun v : {x // p x} => (e.symm w) v.1) = w.1 := by
      funext v
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, v.2]
    have h2 : H (e.symm w) = H₂ w.2 := by
      apply hH
      intro x hx
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hx]
    rw [h1, h2]
  have hint : ∀ (F : (X → ℝ) → ℝ),
      ∫ t in ubox a, F t = ∫ w in A ×ˢ B, F (e.symm w) := by
    intro F
    rw [hbox]
    have := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun w => F (e.symm w)) (A ×ˢ B)
    simpa using this
  rw [hint (fun t => g (fun v : {x // p x} => t v.1) * H t), hint H]
  simp_rw [hcomp]
  have key : ∫ w in A ×ˢ B, g w.1 * H₂ w.2 = (∫ s in A, g s) * ∫ s in B, H₂ s :=
    setIntegral_prod_mul (μ := (volume : Measure ({x // p x} → ℝ)))
      (ν := (volume : Measure ({x // ¬p x} → ℝ))) g H₂ A B
  rw [key]
  have hone : ∫ w in A ×ˢ B, H₂ w.2 = (∫ s in A, (1 : ℝ)) * ∫ s in B, H₂ s := by
    have h1 : ∫ w in A ×ˢ B, (1 : ℝ) * H₂ w.2 = (∫ s in A, (1 : ℝ)) * ∫ s in B, H₂ s :=
      setIntegral_prod_mul (μ := (volume : Measure ({x // p x} → ℝ)))
        (ν := (volume : Measure ({x // ¬p x} → ℝ))) (fun _ => (1 : ℝ)) H₂ A B
    simpa only [one_mul] using h1
  have hAvol : (∫ s in A, (1 : ℝ)) = 1 := by
    have h1 : (∫ s in A, (1 : ℝ)) = (volume A).toReal := by simp [Measure.real]
    rw [h1]
    have : A = Icc (fun v : {x // p x} => a v.1) (fun v => a v.1 + 1) := by
      ext s; simp [hA, Set.mem_Icc, Pi.le_def]
    rw [this, Real.volume_Icc_pi_toReal (fun x => by simp)]
    simp
  have hH2 : ∫ w in A ×ˢ B, H (e.symm w) = ∫ s in B, H₂ s := by
    simp_rw [show ∀ w : ({x // p x} → ℝ) × ({x // ¬p x} → ℝ), H (e.symm w) = H₂ w.2 from fun w => by
      apply hH
      intro x hx
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hx]]
    rw [hone, hAvol, one_mul]
  rw [hH2]


/-- **Product over disjoint coordinate blocks.** -/
theorem prod_block_integral [Fintype X] [DecidableEq X] {ι : Type*} [DecidableEq ι] (a : X → ℝ)
    (S : ι → Finset X) (g : (i : ι) → (S i → ℝ) → ℝ) (I : Finset ι)
    (hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    ∫ t in ubox a, ∏ i ∈ I, g i (fun v : S i => t v.1) =
      ∏ i ∈ I, ∫ s in Set.pi univ (fun v : S i => Icc (a v.1) (a v.1 + 1)), g i s := by
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, integral_const, smul_eq_mul, mul_one]
    simpa [Measure.real, Measure.restrict_apply_univ] using volume_ubox_real a
  | insert j I hj ih =>
    simp only [Finset.prod_insert hj]
    have hS' : ∀ i ∈ I, ∀ k ∈ I, i ≠ k → Disjoint (S i) (S k) :=
      fun i hi k hk hik => hS i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk) hik
    rw [← ih hS']
    have := block_integral_pred a (fun x => x ∈ S j) (g j)
      (fun t => ∏ i ∈ I, g i (fun v : S i => t v.1)) (by
        intro t t' htt'
        apply Finset.prod_congr rfl
        intro i hi
        congr 1
        funext v
        apply htt'
        have hdis := hS j (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h => hj (h ▸ hi))
        exact fun hv => Finset.disjoint_left.mp hdis hv v.2)
    convert this using 5
    all_goals (congr 1; exact Subsingleton.elim _ _)

end WaveTurbulence.CoarseSpliced
