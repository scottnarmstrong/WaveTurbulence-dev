/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TypeSlopes
public import WaveTurbulence.Foundations.Spine.WordDSum
/-! AMEND6' (design P*, F4): the operation recursion `X_{O::rest}(h) = sum_k (w_k/lam) X_rest(h + lam (k-M) O h)`,
with the operation `O` acting FIRST on the profile (innermost: derivatives first, then forms), and the semantic
identities: forms only multiply, derivatives followed by forms give `prod forms * wordD word (V h)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff

/-- One elementary slope operation on pair-type profiles. -/
inductive TOp (d w : ℕ)
  | der (i : Fin d)
  | form (j0 : Fin w) (i : Fin d)

/-- The profile modification. -/
noncomputable def TOp.apply {d w : ℕ} : TOp d w → TProf d w → TProf d w
  | .der i, h => TProf.der i h
  | .form j0 i, h => TProf.form j0 i h

/-- The recursion: the first operation of the list acts innermost (on the profile). -/
noncomputable def evalOps {d w : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (V : TProf d w → Y)
    (M : ℕ) (lam : ℝ) : List (TOp d w) → TProf d w → Y
  | [], h => V h
  | O :: rest, h => ∑ m ∈ range (2 * M + 1),
      (cw M m / lam) • evalOps V M lam rest (TProf.perturb h (O.apply h) (lam * ((m : ℝ) - M)))

theorem evalOps_nil {d w : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (V : TProf d w → Y) (M : ℕ) (lam : ℝ)
    (h : TProf d w) : evalOps V M lam [] h = V h := rfl

theorem evalOps_cons {d w : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (V : TProf d w → Y) (M : ℕ) (lam : ℝ)
    (O : TOp d w) (rest : List (TOp d w)) (h : TProf d w) :
    evalOps V M lam (O :: rest) h = ∑ m ∈ range (2 * M + 1),
      (cw M m / lam) • evalOps V M lam rest (TProf.perturb h (O.apply h) (lam * ((m : ℝ) - M))) := rfl

section Semantics
variable {d w : ℕ} {Y : Type*} [CommRing Y] [Algebra ℝ Y] (V : TProf d w → Y) (M : ℕ) (lam : ℝ)
  (Adm : ℕ → TProf d w → Prop) (fv : Fin w → Fin d → Y)

/-- Forms only: the list of root linear forms multiplies the value by the product of the forms. -/
theorem evalOps_forms
    (hadm : ∀ n g (O : TOp d w) (μ : ℝ), Adm (n + 1) g → Adm n (TProf.perturb g (O.apply g) μ))
    (hM : ∀ n g j0 i, Adm (n + 1) g → ∑ m ∈ range (2 * M + 1), (cw M m / lam) •
      V (TProf.perturb g (TProf.form j0 i g) (lam * ((m : ℝ) - M))) = fv j0 i * V g) :
    ∀ (fs : List (Fin w × Fin d)) (h : TProf d w), Adm fs.length h →
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
          (fs.map fun f => fv f.1 f.2).prod * ((cw M m / lam) •
            V (TProf.perturb h (TProf.form f.1 f.2 h) (lam * ((m : ℝ) - M)))) := by
      intro m _
      rw [ih _ (hadm _ h _ _ hh)]
      simp only [TOp.apply, smul_mul_assoc, mul_smul_comm]
    rw [sum_congr rfl e, ← mul_sum, hM _ h f.1 f.2 hh]
    ring

end Semantics

end WaveTurbulence.LGSpine
