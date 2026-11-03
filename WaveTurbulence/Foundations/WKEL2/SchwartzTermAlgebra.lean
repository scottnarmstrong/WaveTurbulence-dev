/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SchwartzValued

/-!
# Algebraic linearity of each Schwartz collision term
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Each literal Schwartz collision kernel has honest inner and outer integrals. -/
theorem deltaIntegrable_collisionKernel_schwartz (hd : 2 ≤ d) (j : Fin 4)
    (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) : WKE.DeltaIntegrable (collisionKernel j f g h k) := by
  obtain ⟨C, H⟩ := collisionInputs_of_schwartz f g h
    (show 2 * (d : ℝ) < 2 * d + 1 by linarith)
  exact H.deltaIntegrable hd j k

theorem collisionTerm_add_left (hd : 2 ≤ d) (j : Fin 4)
    (f f' g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j ⇑(f + f') g h k = collisionTerm j f g h k + collisionTerm j f' g h k := by
  simp only [collisionTerm]
  rw [← (deltaIntegrable_collisionKernel_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_collisionKernel_schwartz hd j f' g h k) (by omega)]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, add_apply] <;> ring

theorem collisionTerm_add_mid (hd : 2 ≤ d) (j : Fin 4)
    (f g g' h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f ⇑(g + g') h k = collisionTerm j f g h k + collisionTerm j f g' h k := by
  simp only [collisionTerm]
  rw [← (deltaIntegrable_collisionKernel_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_collisionKernel_schwartz hd j f g' h k) (by omega)]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, add_apply] <;> ring

theorem collisionTerm_add_right (hd : 2 ≤ d) (j : Fin 4)
    (f g h h' : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f g ⇑(h + h') k = collisionTerm j f g h k + collisionTerm j f g h' k := by
  simp only [collisionTerm]
  rw [← (deltaIntegrable_collisionKernel_schwartz hd j f g h k).deltaInt_add
    (deltaIntegrable_collisionKernel_schwartz hd j f g h' k) (by omega)]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, add_apply] <;> ring

theorem collisionTerm_smul_left (j : Fin 4) (c : ℝ)
    (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j ⇑(c • f) g h k = c * collisionTerm j f g h k := by
  simp only [collisionTerm]
  rw [← WKE.deltaInt_smul]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, smul_apply, smul_eq_mul] <;> ring

theorem collisionTerm_smul_mid (j : Fin 4) (c : ℝ)
    (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f ⇑(c • g) h k = c * collisionTerm j f g h k := by
  simp only [collisionTerm]
  rw [← WKE.deltaInt_smul]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, smul_apply, smul_eq_mul] <;> ring

theorem collisionTerm_smul_right (j : Fin 4) (c : ℝ)
    (f g h : 𝓢(Mom d, ℝ)) (k : Mom d) :
    collisionTerm j f g ⇑(c • h) k = c * collisionTerm j f g h k := by
  simp only [collisionTerm]
  rw [← WKE.deltaInt_smul]
  apply WKE.deltaInt_congr
  intro a b
  fin_cases j <;> simp only [collisionKernel, smul_apply, smul_eq_mul] <;> ring

end WaveTurbulence.WKEL2
