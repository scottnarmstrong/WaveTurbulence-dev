/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SchwartzValued
public import WaveTurbulence.Foundations.WKE.Multilinear
public import WaveTurbulence.Foundations.WKE.Characterization

/-!
# Multilinearity of the collision terms on Schwartz inputs

For Schwartz inputs (and `d ≥ 2`) the four terms `𝒦ⱼ(φ₁, φ₂, φ₃)` of the collision operator (TARGET
(schappend1)–(schappend4), landed `collisionTerm`) are linear in each argument; hence on finite linear
combinations they expand into finite sums (`collisionTerm_sum₃`). Used to expand the WKE Taylor terms over
dominant couples (DH21 Prop 7.9, DH23 Prop 6.2).
-/

public section

open MeasureTheory Set Finset
open scoped SchwartzMap

namespace WaveTurbulence.Cancel

open WaveTurbulence.WKE

variable {d : ℕ}

theorem deltaIntegrable_of_schwartz (hd : 2 ≤ d) (j : Fin 4) (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    DeltaIntegrable (collisionKernel j f g h k) := by
  obtain ⟨C, hC⟩ := collisionInputs_of_schwartz f g h (N := 2 * d + 1) (by linarith)
  exact hC.deltaIntegrable hd j k

theorem collisionTerm_zero₁ (j : Fin 4) (g h : Mom d → ℝ) (k : Mom d) :
    collisionTerm j 0 g h k = 0 := by
  have : collisionKernel j 0 g h k = fun _ _ => 0 := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel]
  simp [collisionTerm, this, deltaInt]

theorem collisionTerm_zero₂ (j : Fin 4) (f h : Mom d → ℝ) (k : Mom d) :
    collisionTerm j f 0 h k = 0 := by
  have : collisionKernel j f 0 h k = fun _ _ => 0 := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel]
  simp [collisionTerm, this, deltaInt]

theorem collisionTerm_zero₃ (j : Fin 4) (f g : Mom d → ℝ) (k : Mom d) :
    collisionTerm j f g 0 k = 0 := by
  have : collisionKernel j f g 0 k = fun _ _ => 0 := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel]
  simp [collisionTerm, this, deltaInt]

theorem collisionTerm_add₁ (hd : 2 ≤ d) (j : Fin 4) (f f' g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j ⇑(f + f') g h k = collisionTerm j f g h k + collisionTerm j f' g h k := by
  have e : collisionKernel j ⇑(f + f') g h k =
      fun ℓ x => collisionKernel j f g h k ℓ x + collisionKernel j f' g h k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e]
  exact (deltaIntegrable_of_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_of_schwartz hd j f' g h k) (by omega)

theorem collisionTerm_add₂ (hd : 2 ≤ d) (j : Fin 4) (f g g' h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f ⇑(g + g') h k = collisionTerm j f g h k + collisionTerm j f g' h k := by
  have e : collisionKernel j f ⇑(g + g') h k =
      fun ℓ x => collisionKernel j f g h k ℓ x + collisionKernel j f g' h k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e]
  exact (deltaIntegrable_of_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_of_schwartz hd j f g' h k) (by omega)

theorem collisionTerm_add₃ (hd : 2 ≤ d) (j : Fin 4) (f g h h' : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f g ⇑(h + h') k = collisionTerm j f g h k + collisionTerm j f g h' k := by
  have e : collisionKernel j f g ⇑(h + h') k =
      fun ℓ x => collisionKernel j f g h k ℓ x + collisionKernel j f g h' k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e]
  exact (deltaIntegrable_of_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_of_schwartz hd j f g h' k) (by omega)

theorem collisionTerm_smul₁ (j : Fin 4) (c : ℝ) (f : 𝓢(Mom d, ℝ)) (g h : Mom d → ℝ) (k : Mom d) :
    collisionTerm j ⇑(c • f) g h k = c * collisionTerm j f g h k := by
  have e : collisionKernel j ⇑(c • f) g h k = fun ℓ x => c * collisionKernel j f g h k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e, deltaInt_smul]

theorem collisionTerm_smul₂ (j : Fin 4) (c : ℝ) (f : Mom d → ℝ) (g : 𝓢(Mom d, ℝ)) (h : Mom d → ℝ)
    (k : Mom d) : collisionTerm j f ⇑(c • g) h k = c * collisionTerm j f g h k := by
  have e : collisionKernel j f ⇑(c • g) h k = fun ℓ x => c * collisionKernel j f g h k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e, deltaInt_smul]

theorem collisionTerm_smul₃ (j : Fin 4) (c : ℝ) (f g : Mom d → ℝ) (h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f g ⇑(c • h) k = c * collisionTerm j f g h k := by
  have e : collisionKernel j f g ⇑(c • h) k = fun ℓ x => c * collisionKernel j f g h k ℓ x := by
    funext ℓ x; fin_cases j <;> simp [collisionKernel] <;> ring
  simp only [collisionTerm, e, deltaInt_smul]

theorem collisionTerm_sum₁ (hd : 2 ≤ d) (j : Fin 4) {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (f : ι → 𝓢(Mom d, ℝ)) (g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j ⇑(∑ a ∈ s, α a • f a) g h k = ∑ a ∈ s, α a * collisionTerm j (f a) g h k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using collisionTerm_zero₁ j g h k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, collisionTerm_add₁ hd, collisionTerm_smul₁, ih]

theorem collisionTerm_sum₂ (hd : 2 ≤ d) (j : Fin 4) {ι : Type*} (s : Finset ι) (β : ι → ℝ)
    (f : 𝓢(Mom d, ℝ)) (g : ι → 𝓢(Mom d, ℝ)) (h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f ⇑(∑ b ∈ s, β b • g b) h k = ∑ b ∈ s, β b * collisionTerm j f (g b) h k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using collisionTerm_zero₂ j f h k
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, collisionTerm_add₂ hd, collisionTerm_smul₂, ih]

theorem collisionTerm_sum₃' (hd : 2 ≤ d) (j : Fin 4) {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (f g : 𝓢(Mom d, ℝ)) (h : ι → 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f g ⇑(∑ c ∈ s, γ c • h c) k = ∑ c ∈ s, γ c * collisionTerm j f g (h c) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using collisionTerm_zero₃ j f g k
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, collisionTerm_add₃ hd, collisionTerm_smul₃, ih]

/-- **The collision terms on finite linear combinations of Schwartz functions.** -/
theorem collisionTerm_sum₃ (hd : 2 ≤ d) (j : Fin 4) {ι₁ ι₂ ι₃ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (s₃ : Finset ι₃) (α : ι₁ → ℝ) (β : ι₂ → ℝ) (γ : ι₃ → ℝ) (f : ι₁ → 𝓢(Mom d, ℝ))
    (g : ι₂ → 𝓢(Mom d, ℝ)) (h : ι₃ → 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j ⇑(∑ a ∈ s₁, α a • f a) ⇑(∑ b ∈ s₂, β b • g b) ⇑(∑ c ∈ s₃, γ c • h c) k =
      ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, α a * β b * γ c * collisionTerm j (f a) (g b) (h c) k := by
  rw [collisionTerm_sum₁ hd]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [collisionTerm_sum₂ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [collisionTerm_sum₃' hd, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- `𝒦 = 𝒦₀ - 𝒦₁ + 𝒦₂ - 𝒦₃` on Schwartz inputs. -/
theorem collisionOp_eq_sum_schwartz (hd : 2 ≤ d) (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionOp f g h k = collisionTerm 0 f g h k - collisionTerm 1 f g h k
      + collisionTerm 2 f g h k - collisionTerm 3 f g h k := by
  obtain ⟨C, hC⟩ := collisionInputs_of_schwartz f g h (N := 2 * d + 1) (by linarith)
  exact collisionOp_eq_sum hC hd k

end WaveTurbulence.Cancel
