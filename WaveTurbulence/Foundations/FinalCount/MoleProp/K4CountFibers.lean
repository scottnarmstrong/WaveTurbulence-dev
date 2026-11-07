/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountND
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountTransforms
import Mathlib.Tactic

/-! # Actual canonical K4 fibers consume the proved sphere-and-strip bound

The base labels are fixed only inside one finite projection fiber. The
remaining label maps injectively to its literal doubled integer sphere
variable, with all physical equations derived from source membership.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- The explicit majorant proved for one small-radius canonical fiber. -/
noncomputable def k4SmallFiberProfile (d : ℕ) (L τ R M : ℝ) : ℝ :=
  (4*L+1)^(d-2)*
    ((2*((d : ℝ)*(L*τ)/R)+2)*(2*Real.sqrt (2*(L^2*(2*τ)+4*(L*M)+1))+2)*9)

/-- The explicit majorant proved for one large-radius canonical fiber. -/
noncomputable def k4LargeFiberProfile (d : ℕ) (L τ M : ℝ) : ℝ :=
  (d : ℝ)*((4*L+1)^(d-2)*
    (640000*(Real.sqrt (L^2*(2*τ))+(4*L)*(L^2*(2*τ))^((3 : ℝ)/2)/(((L*M)/(d : ℝ))/2)+
      (4*L)*Real.sqrt (L^2*(2*τ))*(((L*M)/(d : ℝ))/2)^(-((1 : ℝ)/3)))))

/-- The doubled integer sphere image loses no label in an actual fixed-base fiber. -/
theorem k4_sphere_fiber_card {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    (b x y : Fin d → ℤ) (hbase : ∀ p ∈ S, p.1=x ∧ p.2.1=y) :
    (S.image (fun p => k4SphereLabel b x p.2.2)).card = S.card := by
  apply card_image_of_injOn
  intro p hp q hq he
  have hz := k4SphereLabel_injective b x he
  exact Prod.ext ((hbase p hp).1.trans (hbase q hq).1.symm)
    (Prod.ext ((hbase p hp).2.trans (hbase q hq).2.symm) hz)

/-- Actual canonical fixed-base sphere images lie in the literal integer
radius-2L box with an arbitrary but fixed affine center. -/
theorem k4_sphere_fiber_box {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L : ℝ} (hL : 0 < L) (A : Fin 6 → Mom d) (a b c x y : Fin d → ℤ) (β : Fin 3 → ℝ) (τ : ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β τ)
    (hbase : ∀ p ∈ S, p.1=x ∧ p.2.1=y) :
    ∀ n ∈ S.image (fun p => k4SphereLabel b x p.2.2), ∀ k,
      |(n k : ℝ)-(L • (2 • A 2-(latticePoint L b+latticePoint L x))) k| ≤ 2*L := by
  intro n hn k
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
  have hh := k4_integer_ball hL _ _ (k4CanonicalSet_sphere_ball (hS p hp))
  rw [(hbase p hp).1] at hh
  have hc := CountLemmas.coordinate_bound_of_ball (L := 1) (by norm_num : (0 : ℝ)<1)
    (L • (2 • A 2-(latticePoint L b+latticePoint L x))) (k4SphereLabel b x p.2.2) hh k
  simpa only [one_mul,mul_comm] using hc

/-- Concrete small-radius K4 fiber bound, with its actual source equations
and actual doubled integer image. No planar or fiber estimate is a premise. -/
theorem k4_small_sphere_fiber_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L R M τ : ℝ} (hL : 0 < L) (hR : 0 < R) (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (A : Fin 6 → Mom d) (a b c x y : Fin d → ℤ) (β : Fin 3 → ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β τ)
    (hbase : ∀ p ∈ S, p.1=x ∧ p.2.1=y)
    (hr : R ≤ ‖latticePoint L c+latticePoint L y‖)
    (hsmall : ∀ p ∈ S, ‖latticePoint L (k4SphereLabel b x p.2.2)‖ ≤ M) :
    (S.card : ℝ) ≤ (4*L+1)^(d-2)*
      ((2*((d : ℝ)*(L*τ)/R)+2)*(2*Real.sqrt (2*(L^2*(2*τ)+4*(L*M)+1))+2)*9) := by
  classical
  let T := S.image (fun p => k4SphereLabel b x p.2.2)
  have hbox := k4_sphere_fiber_box S hL A a b c x y β τ hS hbase
  have hball : ∀ n ∈ T, ‖latticePoint 1 n‖ ≤ L*M := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    have hh := k4_integer_ball hL (0 : Mom d) _ (by simpa only [sub_zero] using hsmall p hp)
    simpa only [smul_zero,sub_zero] using hh
  have hstrip : ∀ n ∈ T,
      |inner ℝ (latticePoint L c+latticePoint L y) (latticePoint 1 n)-
        L*(β 2-‖latticePoint L c+latticePoint L y‖^2+‖latticePoint L y‖^2-
          inner ℝ (latticePoint L c+latticePoint L y) (latticePoint L b+latticePoint L x))| ≤ L*τ := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    have hh := k4_integer_strip hL _ _ (k4CanonicalSet_strip (hS p hp))
    rw [(hbase p hp).1,(hbase p hp).2] at hh
    exact hh
  have hshell : ∀ n ∈ T, |‖latticePoint 1 n‖^2-
      L^2*(2*β 1-‖latticePoint L b+latticePoint L x‖^2+2*‖latticePoint L x‖^2)| ≤ L^2*(2*τ) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    have hh := k4_integer_shell hL _ (k4CanonicalSet_sphere (hS p hp))
    rw [(hbase p hp).1] at hh
    exact hh
  have hh := k4_nd_shell_strip_norm_card_le hd T (latticePoint L c+latticePoint L y)
    (fun k => (L • (2 • A 2-(latticePoint L b+latticePoint L x))) k)
    hR (mul_nonneg hL.le hM) (mul_nonneg (sq_nonneg L) (mul_nonneg (by norm_num) hτ))
    (mul_nonneg (by norm_num) hL.le) (mul_nonneg hL.le hτ) hr
    (L*(β 2-‖latticePoint L c+latticePoint L y‖^2+‖latticePoint L y‖^2-
      inner ℝ (latticePoint L c+latticePoint L y) (latticePoint L b+latticePoint L x)))
    (L^2*(2*β 1-‖latticePoint L b+latticePoint L x‖^2+2*‖latticePoint L x‖^2)) hbox hball hstrip hshell
  rw [k4_sphere_fiber_card S b x y hbase] at hh
  simpa only [show 2*(2*L)+1=4*L+1 by ring] using hh

/-- Concrete large-radius K4 fiber bound. Its energy center remains
arbitrary and the lower-radius condition supplies the annulus separation. -/
theorem k4_large_sphere_fiber_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L M τ : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hW : 1 ≤ L^2*(2*τ)) (hMW : 4*(L^2*(2*τ)) ≤ ((L*M)/(d : ℝ))^2)
    (A : Fin 6 → Mom d) (a b c x y : Fin d → ℤ) (β : Fin 3 → ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β τ)
    (hbase : ∀ p ∈ S, p.1=x ∧ p.2.1=y)
    (hlarge : ∀ p ∈ S, M ≤ ‖latticePoint L (k4SphereLabel b x p.2.2)‖) :
    (S.card : ℝ) ≤ (d : ℝ)*((4*L+1)^(d-2)*
      (640000*(Real.sqrt (L^2*(2*τ))+(4*L)*(L^2*(2*τ))^((3 : ℝ)/2)/(((L*M)/(d : ℝ))/2)+
        (4*L)*Real.sqrt (L^2*(2*τ))*(((L*M)/(d : ℝ))/2)^(-((1 : ℝ)/3))))) := by
  classical
  let T := S.image (fun p => k4SphereLabel b x p.2.2)
  have hbox := k4_sphere_fiber_box S hL A a b c x y β τ hS hbase
  have hbig : ∀ n ∈ T, L*M ≤ ‖latticePoint 1 n‖ := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    rw [CountLemmas.latticePoint_one_eq_smul hL.ne',norm_smul,Real.norm_eq_abs,abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (hlarge p hp) hL.le
  have hshell : ∀ n ∈ T, |‖latticePoint 1 n‖^2-
      L^2*(2*β 1-‖latticePoint L b+latticePoint L x‖^2+2*‖latticePoint L x‖^2)| ≤ L^2*(2*τ) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    have hh := k4_integer_shell hL _ (k4CanonicalSet_sphere (hS p hp))
    rw [(hbase p hp).1] at hh
    exact hh
  have hh := k4_nd_large_shell_norm_card_le hd T
    (fun k => (L • (2 • A 2-(latticePoint L b+latticePoint L x))) k)
    (mul_pos hL hM) hW hMW (mul_nonneg (by norm_num) hL.le) hbox hbig hshell
  rw [k4_sphere_fiber_card S b x y hbase] at hh
  simpa only [show 2*(2*L)+1=4*L+1 by ring,show 2*(2*L)=4*L by ring] using hh

end WaveTurbulence.MoleProp
