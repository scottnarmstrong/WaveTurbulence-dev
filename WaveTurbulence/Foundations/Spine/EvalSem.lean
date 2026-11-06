/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EvalBound
public import WaveTurbulence.Foundations.Spine.WordDSum
public import WaveTurbulence.Foundations.Sumint.MultiIndices
/-! AMEND6' (design P*): semantics of the operation recursion for COUPLES (function-valued evaluations):
derivatives followed by forms give `prod forms * wordD word (V h)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff NormBridgeScratch

theorem partialMom_const_mul' {d : ℕ} (j : Fin d) (c : ℂ) (f : Mom d → ℂ) (x : Mom d)
    (hf : DifferentiableAt ℝ f x) :
    partialMom j (fun y => c * f y) x = c * partialMom j f x := by
  unfold partialMom
  rw [fderiv_const_mul hf]
  simp

theorem wordD_const_mul {d : ℕ} (word : List (Fin d)) (c : ℂ) (f : Mom d → ℂ)
    (hf : ContDiff ℝ word.length f) :
    wordD word (fun x => c * f x) = fun x => c * wordD word f x := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    have hf0 : ContDiff ℝ word.length f := hf.of_le (by simp)
    change partialMom j (wordD word (fun x => c * f x)) = _
    rw [ih hf0]
    have hf1 : ContDiff ℝ (1 + word.length : ℕ) f := by simpa only [List.length_cons, Nat.add_comm] using hf
    funext x
    exact partialMom_const_mul' j c _ x
      ((ContDiff.differentiable (wordD_contDiff word 1 hf1) (by norm_num)) x)

theorem wordD_sum_const_mul {d : ℕ} {ι : Type*} (s : Finset ι) (word : List (Fin d)) (c : ι → ℂ)
    (f : ι → Mom d → ℂ) (hf : ∀ i ∈ s, ContDiff ℝ word.length (f i)) :
    wordD word (fun x => ∑ i ∈ s, c i * f i x) = fun x => ∑ i ∈ s, c i * wordD word (f i) x := by
  rw [wordD_finset_sum s word (fun i x => c i * f i x) (fun i hi => (contDiff_const.mul (hf i hi)))]
  funext x
  refine sum_congr rfl fun i hi => ?_
  rw [wordD_const_mul word (c i) (f i) (hf i hi)]

section Semantics
variable {d w : ℕ} (V : TProf d w → (Mom d → ℂ)) (M : ℕ) (lam : ℝ)
  (fv : Fin w → Fin d → (Mom d → ℂ))

theorem evalOps_apply {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (V : TProf d w → (Mom d → ℂ)) (M : ℕ) (lam : ℝ)
    (os : List (TOp d w)) (h : TProf d w) (x : Mom d) :
    evalOps V M lam os h x = evalOps (fun g => V g x) M lam os h := by
  induction os generalizing h with
  | nil => rfl
  | cons O rest ih =>
    rw [evalOps_cons, evalOps_cons]
    simp only [Finset.sum_apply, Pi.smul_apply, ih]

/-- Forms only, with a list-indexed admissibility predicate. -/
theorem evalOps_forms_list (Adm : List (TOp d w) → TProf d w → Prop)
    (hstep : ∀ O rest g (μ : ℝ), Adm (O :: rest) g → Adm rest (TProf.perturb g (O.apply g) μ))
    (hM : ∀ j0 i rest g, Adm (TOp.form j0 i :: rest) g → (fun x => ∑ m ∈ range (2 * M + 1),
      ((cw M m / lam : ℝ) : ℂ) * V (TProf.perturb g (TProf.form j0 i g) (lam * ((m : ℝ) - M))) x) =
        fv j0 i * V g) :
    ∀ (fs : List (Fin w × Fin d)) (h : TProf d w), Adm (fs.map fun f => TOp.form f.1 f.2) h →
      evalOps V M lam (fs.map fun f => TOp.form f.1 f.2) h = (fs.map fun f => fv f.1 f.2).prod * V h := by
  intro fs
  induction fs with
  | nil => intro h _; simp [evalOps_nil]
  | cons f fs ih =>
    intro h hh
    simp only [List.map_cons, evalOps_cons, List.prod_cons]
    have e : ∀ m ∈ range (2 * M + 1),
        (cw M m / lam) • evalOps V M lam (fs.map fun f => TOp.form f.1 f.2)
            (TProf.perturb h ((TOp.form f.1 f.2).apply h) (lam * ((m : ℝ) - M))) =
          fun x => ((cw M m / lam : ℝ) : ℂ) * ((fs.map fun f => fv f.1 f.2).prod x *
            V (TProf.perturb h (TProf.form f.1 f.2 h) (lam * ((m : ℝ) - M))) x) := by
      intro m _
      rw [ih _ (hstep _ _ h _ hh)]
      funext x
      simp [TOp.apply, Pi.smul_apply, Complex.real_smul, Pi.mul_apply]
    rw [sum_congr rfl e]
    have hMh := hM f.1 f.2 _ h hh
    funext x
    have := congrFun hMh x
    simp only [Pi.mul_apply] at this ⊢
    rw [Finset.sum_apply]
    calc _ = (fs.map fun f => fv f.1 f.2).prod x * ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
          V (TProf.perturb h (TProf.form f.1 f.2 h) (lam * ((m : ℝ) - M))) x := by
            rw [Finset.mul_sum]; refine sum_congr rfl fun m _ => ?_; ring
      _ = _ := by rw [this]; ring

/-- Derivatives then forms: `prod forms * wordD (reverse ders) (V h)`. -/
theorem evalOps_ders_forms (Adm : List (TOp d w) → TProf d w → Prop)
    (hstep : ∀ O rest g (μ : ℝ), Adm (O :: rest) g → Adm rest (TProf.perturb g (O.apply g) μ))
    (hsm : ∀ os g, Adm os g → ContDiff ℝ (dcnt os) (V g))
    (hD : ∀ i rest g, Adm (TOp.der i :: rest) g → (fun x => ∑ m ∈ range (2 * M + 1),
      ((cw M m / lam : ℝ) : ℂ) * V (TProf.perturb g (TProf.der i g) (lam * ((m : ℝ) - M))) x) =
        partialMom i (V g))
    (hM : ∀ j0 i rest g, Adm (TOp.form j0 i :: rest) g → (fun x => ∑ m ∈ range (2 * M + 1),
      ((cw M m / lam : ℝ) : ℂ) * V (TProf.perturb g (TProf.form j0 i g) (lam * ((m : ℝ) - M))) x) =
        fv j0 i * V g) :
    ∀ (ders : List (Fin d)) (fs : List (Fin w × Fin d)) (h : TProf d w),
      Adm (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2) h →
      evalOps V M lam (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2) h =
        (fs.map fun f => fv f.1 f.2).prod * wordD ders.reverse (V h) := by
  intro ders
  induction ders with
  | nil =>
    intro fs h hh
    simp only [List.map_nil, List.nil_append, List.reverse_nil, wordD]
    exact evalOps_forms_list V M lam fv Adm hstep hM fs h hh
  | cons i ders ih =>
    intro fs h hh
    simp only [List.map_cons, List.cons_append, evalOps_cons, List.reverse_cons] at hh ⊢
    have hh' : ∀ m : ℕ, Adm (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2)
        (TProf.perturb h ((TOp.der i).apply h) (lam * ((m : ℝ) - M))) := fun m => hstep _ _ h _ hh
    have e1 : ∀ m ∈ range (2 * M + 1),
        (cw M m / lam) • evalOps V M lam (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2)
          (TProf.perturb h ((TOp.der i).apply h) (lam * ((m : ℝ) - M))) =
        fun x => ((cw M m / lam : ℝ) : ℂ) * ((fs.map fun f => fv f.1 f.2).prod x *
          wordD ders.reverse (V (TProf.perturb h (TProf.der i h) (lam * ((m : ℝ) - M)))) x) := by
      intro m _
      rw [ih fs _ (hh' m)]
      funext x
      simp [TOp.apply, Pi.smul_apply, Complex.real_smul, Pi.mul_apply]
    rw [sum_congr rfl e1]
    have hsmooth : ∀ m ∈ range (2 * M + 1), ContDiff ℝ ders.reverse.length
        (V (TProf.perturb h (TProf.der i h) (lam * ((m : ℝ) - M)))) := by
      intro m _
      have := hsm _ _ (hh' m)
      have e : dcnt (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2) = ders.length := by
        simp [dcnt, List.map_append, List.sum_append, List.map_map, Function.comp_def, TOp.dc]
      rw [e] at this
      simpa [TOp.apply] using this
    have hDh := hD i _ h hh
    funext x
    rw [Pi.mul_apply]
    have e2 : wordD (ders.reverse ++ [i]) (V h) =
        fun x => ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
          wordD ders.reverse (V (TProf.perturb h (TProf.der i h) (lam * ((m : ℝ) - M)))) x := by
      rw [wordD_append]
      have : wordD [i] (V h) = partialMom i (V h) := rfl
      rw [this, ← hDh]
      exact wordD_sum_const_mul _ _ _ _ hsmooth
    rw [e2, Finset.sum_apply, Finset.mul_sum]
    refine sum_congr rfl fun m _ => ?_
    ring

end Semantics
end WaveTurbulence.LGSpine
