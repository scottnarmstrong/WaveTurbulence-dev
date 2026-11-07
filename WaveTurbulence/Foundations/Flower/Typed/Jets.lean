/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Sumint.Words
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import Mathlib.Data.Nat.Choose.Sum
/-! # FL-TYPED: pointwise jet bounds on coordinate words and the Leibniz rule without dimension loss. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

/-- Pointwise bounds `‖∂^l f (x)‖ ≤ e |l| x` for all coordinate words of length at most `N`. -/
def JetW (N : ℕ) (e : ℕ → Mom d → ℝ) (f : Mom d → ℂ) : Prop :=
  ∀ l : List (Fin d), l.length ≤ N → ∀ x, ‖wordD l f x‖ ≤ e l.length x

theorem wordD_concat (l : List (Fin d)) (a : Fin d) (f : Mom d → ℂ) :
    wordD (l ++ [a]) f = wordD l (partialMom a f) := by
  rw [wordD_append]; rfl

theorem contDiff_partialMom {n : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f)
    (a : Fin d) : ContDiff ℝ (n : WithTop ℕ∞) (partialMom a f) := by
  have := wordD_contDiff [a] n (f := f) (by simpa using hf)
  exact this

theorem partialMom_mul {E F : Mom d → ℂ} (hE : ContDiff ℝ 1 E) (hF : ContDiff ℝ 1 F) (a : Fin d) :
    partialMom a (fun y => E y * F y) = fun y => partialMom a E y * F y + E y * partialMom a F y := by
  funext y
  unfold partialMom
  have hE' : DifferentiableAt ℝ E y := (hE.differentiable (by norm_num)) y
  have hF' : DifferentiableAt ℝ F y := (hF.differentiable (by norm_num)) y
  rw [fderiv_fun_mul hE' hF']
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem wordD_add : ∀ (l : List (Fin d)) {f g : Mom d → ℂ},
    ContDiff ℝ (l.length : WithTop ℕ∞) f → ContDiff ℝ (l.length : WithTop ℕ∞) g →
    wordD l (fun y => f y + g y) = fun y => wordD l f y + wordD l g y
  | [], f, g, _, _ => rfl
  | j :: l, f, g, hf, hg => by
    have hf' : ContDiff ℝ (l.length : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ _)
    have hg' : ContDiff ℝ (l.length : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_succ _)
    have ih := wordD_add l hf' hg'
    have hf1 : ContDiff ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) f := by
      rw [Nat.add_comm]; simpa using hf
    have hg1 : ContDiff ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) g := by
      rw [Nat.add_comm]; simpa using hg
    have hd1 : Differentiable ℝ (wordD l f) := (wordD_contDiff l 1 hf1).differentiable (by norm_num)
    have hd2 : Differentiable ℝ (wordD l g) := (wordD_contDiff l 1 hg1).differentiable (by norm_num)
    show partialMom j (wordD l (fun y => f y + g y)) = _
    rw [ih]
    funext y
    unfold partialMom
    rw [fderiv_fun_add (hd1 y) (hd2 y)]
    rfl

theorem wordD_const_mul : ∀ (l : List (Fin d)) (c : ℂ) {f : Mom d → ℂ},
    ContDiff ℝ (l.length : WithTop ℕ∞) f →
    wordD l (fun y => c * f y) = fun y => c * wordD l f y
  | [], c, f, _ => rfl
  | j :: l, c, f, hf => by
    have hf' : ContDiff ℝ (l.length : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ _)
    have ih := wordD_const_mul l c hf'
    have hf1 : ContDiff ℝ ((1 + l.length : ℕ) : WithTop ℕ∞) f := by
      rw [Nat.add_comm]; simpa using hf
    have hd1 : Differentiable ℝ (wordD l f) := (wordD_contDiff l 1 hf1).differentiable (by norm_num)
    show partialMom j (wordD l (fun y => c * f y)) = _
    rw [ih]
    funext y
    unfold partialMom
    rw [fderiv_const_mul (hd1 y)]
    simp only [smul_apply, smul_eq_mul]
    rfl

theorem wordD_const (l : List (Fin d)) (c : ℂ) (hl : l ≠ []) :
    wordD l (fun _ => c) = fun _ => 0 := by
  induction l with
  | nil => exact absurd rfl hl
  | cons j l ih =>
    show partialMom j (wordD l (fun _ => c)) = _
    by_cases h : l = []
    · subst h
      funext y
      simp [wordD, partialMom]
    · rw [ih h]
      funext y
      simp [partialMom]

/-- The Leibniz rule for coordinate words: no dimensional loss in the leading term. -/
theorem jet_mul_aux : ∀ (n : ℕ) (E F : Mom d → ℂ) (e f : ℕ → Mom d → ℝ),
    ContDiff ℝ (n : WithTop ℕ∞) E → ContDiff ℝ (n : WithTop ℕ∞) F → JetW n e E → JetW n f F →
    ∀ l : List (Fin d), l.length = n → ∀ x,
      ‖wordD l (fun y => E y * F y) x‖ ≤
        ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℝ) * (e ij.1 x * f ij.2 x)
  | 0, E, F, e, f, _, _, hE, hF, l, hl, x => by
    have : l = [] := List.length_eq_zero_iff.mp hl
    subst this
    have h1 := hE [] (by simp) x
    have h2 := hF [] (by simp) x
    simp only [wordD, List.length_nil] at h1 h2 ⊢
    simp only [Finset.Nat.antidiagonal_zero, sum_singleton, Nat.choose_self, Nat.cast_one, one_mul]
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  | n + 1, E, F, e, f, hEc, hFc, hE, hF, l, hl, x => by
    rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
    · subst h; simp at hl
    have hl' : l'.length = n := by simpa using hl
    rw [List.concat_eq_append, wordD_concat]
    have hE1 : ContDiff ℝ 1 E := hEc.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hF1 : ContDiff ℝ 1 F := hFc.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hEn : ContDiff ℝ (n : WithTop ℕ∞) E := hEc.of_le (by exact_mod_cast Nat.le_succ n)
    have hFn : ContDiff ℝ (n : WithTop ℕ∞) F := hFc.of_le (by exact_mod_cast Nat.le_succ n)
    have hE'c : ContDiff ℝ (n : WithTop ℕ∞) (partialMom a E) := contDiff_partialMom hEc a
    have hF'c : ContDiff ℝ (n : WithTop ℕ∞) (partialMom a F) := contDiff_partialMom hFc a
    rw [partialMom_mul hE1 hF1 a]
    have hc1 : ContDiff ℝ (l'.length : WithTop ℕ∞) (fun y => partialMom a E y * F y) := by
      rw [hl']; exact hE'c.mul hFn
    have hc2 : ContDiff ℝ (l'.length : WithTop ℕ∞) (fun y => E y * partialMom a F y) := by
      rw [hl']; exact hEn.mul hF'c
    rw [wordD_add l' hc1 hc2]
    refine (norm_add_le _ _).trans ?_
    have jE : JetW n (fun k => e (k + 1)) (partialMom a E) := by
      intro l'' hl'' y
      have := hE (l'' ++ [a]) (by simp; omega) y
      rw [wordD_concat] at this
      simpa using this
    have jF : JetW n (fun k => f (k + 1)) (partialMom a F) := by
      intro l'' hl'' y
      have := hF (l'' ++ [a]) (by simp; omega) y
      rw [wordD_concat] at this
      simpa using this
    have jE0 : JetW n e E := fun l'' hl'' => hE l'' (hl''.trans (Nat.le_succ n))
    have jF0 : JetW n f F := fun l'' hl'' => hF l'' (hl''.trans (Nat.le_succ n))
    have i1 := jet_mul_aux n (partialMom a E) F (fun k => e (k + 1)) f hE'c hFn jE jF0 l' hl' x
    have i2 := jet_mul_aux n E (partialMom a F) e (fun k => f (k + 1)) hEn hF'c jE0 jF l' hl' x
    rw [sum_antidiagonal_choose_succ_mul (fun i j => e i x * f j x) n]
    refine (add_le_add i1 i2).trans_eq ?_
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun ij hij => ?_
    rw [Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]

theorem JetW.mono {N : ℕ} {e e' : ℕ → Mom d → ℝ} {f : Mom d → ℂ} (h : ∀ k x, e k x ≤ e' k x)
    (hf : JetW N e f) : JetW N e' f :=
  fun l hl x => (hf l hl x).trans (h _ x)

theorem JetW.mono_le {N N' : ℕ} {e : ℕ → Mom d → ℝ} {f : Mom d → ℂ} (h : N' ≤ N)
    (hf : JetW N e f) : JetW N' e f :=
  fun l hl x => hf l (hl.trans h) x

/-- Closed form of products of jets. -/
theorem JetW.mul {N : ℕ} {e f : ℕ → Mom d → ℝ} {E F : Mom d → ℂ}
    (hEc : ContDiff ℝ (N : WithTop ℕ∞) E) (hFc : ContDiff ℝ (N : WithTop ℕ∞) F)
    (hE : JetW N e E) (hF : JetW N f F) :
    JetW N (fun k x => ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * (e ij.1 x * f ij.2 x))
      (fun y => E y * F y) := by
  intro l hl x
  exact jet_mul_aux l.length E F e f (hEc.of_le (by exact_mod_cast hl))
    (hFc.of_le (by exact_mod_cast hl)) (hE.mono_le hl) (hF.mono_le hl) l rfl x

theorem JetW.add {N : ℕ} {e e' : ℕ → Mom d → ℝ} {f g : Mom d → ℂ}
    (hfc : ContDiff ℝ (N : WithTop ℕ∞) f) (hgc : ContDiff ℝ (N : WithTop ℕ∞) g)
    (hf : JetW N e f) (hg : JetW N e' g) :
    JetW N (fun k x => e k x + e' k x) (fun y => f y + g y) := by
  intro l hl x
  rw [wordD_add l (hfc.of_le (by exact_mod_cast hl)) (hgc.of_le (by exact_mod_cast hl))]
  exact (norm_add_le _ _).trans (add_le_add (hf l hl x) (hg l hl x))

theorem JetW.const_mul {N : ℕ} {e : ℕ → Mom d → ℝ} {f : Mom d → ℂ} (c : ℂ)
    (hfc : ContDiff ℝ (N : WithTop ℕ∞) f) (hf : JetW N e f) :
    JetW N (fun k x => ‖c‖ * e k x) (fun y => c * f y) := by
  intro l hl x
  rw [wordD_const_mul l c (hfc.of_le (by exact_mod_cast hl))]
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (hf l hl x) (norm_nonneg _)

theorem JetW.const (N : ℕ) (c : ℂ) :
    JetW N (fun k _ => if k = 0 then ‖c‖ else 0) (fun _ : Mom d => c) := by
  intro l hl x
  by_cases h : l = []
  · subst h; simp [wordD]
  · rw [wordD_const l c h]
    have : l.length ≠ 0 := by simpa using h
    simp [this]

theorem JetW.zero (N : ℕ) : JetW N (fun _ _ => 0) (fun _ : Mom d => (0 : ℂ)) := by
  intro l hl x
  by_cases h : l = []
  · subst h; simp [wordD]
  · rw [wordD_const l 0 h]; simp

/-- A function vanishing on an open ball has vanishing derivatives there. -/
theorem wordD_eq_zero_of_ball (r : ℝ) {g : Mom d → ℂ} (hg : ∀ y, ‖y‖ < r → g y = 0) :
    ∀ (l : List (Fin d)) (x : Mom d), ‖x‖ < r → wordD l g x = 0 := by
  have key : ∀ l : List (Fin d), ∀ x : Mom d, ‖x‖ < r → wordD l g x = 0 := by
    intro l
    induction l with
    | nil => intro x hx; exact hg x hx
    | cons j l ih =>
      intro x hx
      show fderiv ℝ (wordD l g) x (EuclideanSpace.single j 1) = 0
      have hev : wordD l g =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        have hn : {y : Mom d | ‖y‖ < r} ∈ nhds x :=
          (isOpen_lt continuous_norm continuous_const).mem_nhds hx
        filter_upwards [hn] with y hy
        exact ih y hy
      rw [hev.fderiv_eq]
      simp
  exact key

end WaveTurbulence.Flower.Typed
