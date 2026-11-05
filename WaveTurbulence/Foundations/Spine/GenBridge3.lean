/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenBridge2
import Mathlib.Tactic
/-! The literal Fourier family `Phi` of a class domain equals the product-model `Bprod`. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k m : ℕ}

omit [DecidableEq ι] in
theorem prod_split (e : ι ≃ Fin k ⊕ Fin m) (f : ι → ℂ) :
    ∏ v, f v = (∏ i, f (e.symm (Sum.inl i))) * ∏ j, f (e.symm (Sum.inr j)) := by
  rw [← Fintype.prod_equiv e.symm (fun s => f (e.symm s)) f (fun _ => rfl), Fintype.prod_sum_type]

theorem Gf_eq {n : ℕ} (par : Par n) (l u β t : Fin n → ℝ) (v : Fin n) :
    Gf par l u β v t = (if t v ∈ Ioc (l v) (u v) ∧ (∀ w, par v = some w → t v < t w)
      then (1 : ℂ) else 0) * Complex.exp (((β v * t v : ℝ) : ℂ) * Complex.I) := by
  unfold Gf
  rcases hv : par v with _ | w
  · by_cases h : t v ∈ Ioc (l v) (u v) <;> simp [h]
  · by_cases h : t v ∈ Ioc (l v) (u v) <;> by_cases h2 : t v < t w <;> simp [h, h2]

theorem Fd_eq {n : ℕ} (par : Par n) (l u β t : Fin n → ℝ) :
    Fd par l u β t = (if (∀ v, t v ∈ Ioc (l v) (u v)) ∧ (∀ v w, par v = some w → t v < t w)
      then (1 : ℂ) else 0) * ∏ v, Complex.exp (((β v * t v : ℝ) : ℂ) * Complex.I) := by
  unfold Fd
  simp_rw [Gf_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, forall_and]

noncomputable def cYf (e : ι ≃ Fin k ⊕ Fin m) (A : Finset ι) : ℂ :=
  ∏ j : Fin m, if e.symm (Sum.inr j) ∈ A then ((Real.pi : ℝ) : ℂ) * Complex.I else 1

noncomputable def wXf (e : ι ≃ Fin k ⊕ Fin m) (ls : ι → ℝ) (A : Finset ι) (tx : Fin k → ℝ) : ℂ :=
  cYf e A * ∏ i : Fin k, if e.symm (Sum.inl i) ∈ A then
    ((Real.pi * (tx i - ls (e.symm (Sum.inl i))) : ℝ) : ℂ) * Complex.I else 1

theorem famInt_symm (e : ι ≃ Fin k ⊕ Fin m) (ls : ι → ℝ) (A : Finset ι) (α : ι → ℝ)
    (p : (Fin k → ℝ) × (Fin m → ℝ)) :
    famInt ls A α ((Th e).symm p) =
      wXf e ls A p.1 * ((∏ i, ee (Real.pi * (Th e α).1 i) (p.1 i)) *
        ((∏ j, if e.symm (Sum.inr j) ∈ A then (((p.2 j - ls (e.symm (Sum.inr j)) : ℝ)) : ℂ) else 1) *
          ∏ j, Complex.exp ((((Real.pi • (Th e α).2) j * p.2 j : ℝ)) * Complex.I))) := by
  have hx : ∀ i, (Th e).symm p (e.symm (Sum.inl i)) = p.1 i := fun i => by
    rw [Th_symm_apply]; simp
  have hy : ∀ j, (Th e).symm p (e.symm (Sum.inr j)) = p.2 j := fun j => by
    rw [Th_symm_apply]; simp
  have hα : (Th e α) = (fun i => α (e.symm (Sum.inl i)), fun j => α (e.symm (Sum.inr j))) := Th_apply e α
  unfold famInt
  have hA : ∏ v ∈ A, (((Real.pi * (((Th e).symm p) v - ls v) : ℝ) : ℂ) * Complex.I) =
      ∏ v, if v ∈ A then (((Real.pi * (((Th e).symm p) v - ls v) : ℝ) : ℂ) * Complex.I) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hA, prod_split e, prod_split e (fun v => Complex.exp (((Real.pi * α v * ((Th e).symm p) v : ℝ) : ℂ) * Complex.I))]
  simp only [hx, hy]
  have hY : (∏ j, if e.symm (Sum.inr j) ∈ A then (((Real.pi * (p.2 j - ls (e.symm (Sum.inr j))) : ℝ) : ℂ) * Complex.I)
      else 1) = cYf e A * ∏ j, if e.symm (Sum.inr j) ∈ A then (((p.2 j - ls (e.symm (Sum.inr j)) : ℝ)) : ℂ) else 1 := by
    unfold cYf
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    by_cases h : e.symm (Sum.inr j) ∈ A
    · simp only [h, ite_true]; push_cast; ring
    · simp [h]
  have hX : ∏ i, ee (Real.pi * (Th e α).1 i) (p.1 i) =
      ∏ i, Complex.exp (((Real.pi * α (e.symm (Sum.inl i)) * p.1 i : ℝ) : ℂ) * Complex.I) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Th_apply]; unfold ee; simp only [mul_assoc]
  have hYe : ∏ j, Complex.exp ((((Real.pi • (Th e α).2) j * p.2 j : ℝ)) * Complex.I) =
      ∏ j, Complex.exp (((Real.pi * α (e.symm (Sum.inr j)) * p.2 j : ℝ) : ℂ) * Complex.I) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Th_apply]; simp only [Pi.smul_apply, smul_eq_mul]
  rw [hX, hYe, hY]
  unfold wXf
  ring

omit [DecidableEq ι] in
theorem measurableSet_OmegaC (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι)
    (Rv : Set (Fin k → ℝ)) (hRv : MeasurableSet Rv) : MeasurableSet (OmegaC ls cap lt le xv Rv) := by
  unfold OmegaC
  have e1 : MeasurableSet {t : ι → ℝ | ∀ v, t v ∈ Icc (ls v) (ls v + 1)} := by
    have : {t : ι → ℝ | ∀ v, t v ∈ Icc (ls v) (ls v + 1)} = ⋂ v, (fun t : ι → ℝ => t v) ⁻¹' Icc (ls v) (ls v + 1) := by
      ext t; simp
    rw [this]
    exact MeasurableSet.iInter (fun v => measurableSet_Icc.preimage (measurable_pi_apply v))
  have e2c : MeasurableSet {t : ι → ℝ | ∀ v, t v < cap v} := by
    have : {t : ι → ℝ | ∀ v, t v < cap v} = ⋂ v, {t : ι → ℝ | t v < cap v} := by ext t; simp
    rw [this]
    exact MeasurableSet.iInter (fun v => measurableSet_lt (measurable_pi_apply v) measurable_const)
  have e2 : MeasurableSet {t : ι → ℝ | ∀ a b, lt a b → t a < t b} := by
    have : {t : ι → ℝ | ∀ a b, lt a b → t a < t b} =
        ⋂ a, ⋂ b, {t : ι → ℝ | lt a b → t a < t b} := by ext t; simp
    rw [this]
    refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
    by_cases h : lt a b
    · simp only [h, true_implies]
      exact measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b)
    · simp [h]
  have e3 : MeasurableSet {t : ι → ℝ | ∀ a b, le a b → t a ≤ t b} := by
    have : {t : ι → ℝ | ∀ a b, le a b → t a ≤ t b} =
        ⋂ a, ⋂ b, {t : ι → ℝ | le a b → t a ≤ t b} := by ext t; simp
    rw [this]
    refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
    by_cases h : le a b
    · simp only [h, true_implies]
      exact measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b)
    · simp [h]
  have e4 : MeasurableSet {t : ι → ℝ | (fun i => t (xv i)) ∈ Rv} :=
    hRv.preimage (measurable_pi_iff.mpr (fun i => measurable_pi_apply (xv i)))
  exact e1.inter (e2c.inter (e2.inter (e3.inter e4)))

omit [DecidableEq ι] in
theorem bdd_OmegaC (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι)
    (Rv : Set (Fin k → ℝ)) : ∀ t ∈ OmegaC ls cap lt le xv Rv, ∀ v, |t v| ≤ ∑ v, (|ls v| + 1) := by
  intro t ht v
  have h := ht.1 v
  have h1 : |t v| ≤ |ls v| + 1 := by
    rw [abs_le]; constructor <;> cases abs_cases (ls v) <;> linarith [h.1, h.2]
  exact h1.trans (Finset.single_le_sum (f := fun v => |ls v| + 1) (fun v _ => by positivity) (Finset.mem_univ v))

end WaveTurbulence.Ladder
