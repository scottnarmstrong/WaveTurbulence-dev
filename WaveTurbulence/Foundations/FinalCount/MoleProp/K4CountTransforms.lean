/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSets
import Mathlib.Tactic

/-! # Literal sphere and strip equations of the canonical K4 fiber

The actual doubled free label q=2k3−b−k2 remains on the original integer
lattice. Its parity condition can be discarded only after the injection
proved here. All arbitrary conservation and energy centers are retained.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- The canonical six-label reconstruction commutes with the actual
lattice embedding; no shifted or rotated replacement lattice is introduced. -/
theorem k4Labels_latticePoint {d : ℕ} (L : ℝ) (a b c x y z : Fin d → ℤ) :
    (fun i => latticePoint L (k4Labels a b c x y z i)) =
      k4Labels (latticePoint L a) (latticePoint L b) (latticePoint L c)
        (latticePoint L x) (latticePoint L y) (latticePoint L z) := by
  funext i
  fin_cases i <;> simp [k4Labels,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]

/-- The actual doubled sphere variable in integer labels. -/
def k4SphereLabel {d : ℕ} (b x z : Fin d → ℤ) : Fin d → ℤ := z+z-b-x

/-- Fixing the base label loses no multiplicity when passing to the sphere variable. -/
theorem k4SphereLabel_injective {d : ℕ} (b x : Fin d → ℤ) :
    Function.Injective (k4SphereLabel b x) := by
  intro z t h
  funext i
  have he := congrFun h i
  simp only [k4SphereLabel,Pi.sub_apply,Pi.add_apply] at he
  omega

/-- The physical sphere variable is the literal doubled affine label. -/
theorem latticePoint_k4SphereLabel {d : ℕ} (L : ℝ) (b x z : Fin d → ℤ) :
    latticePoint L (k4SphereLabel b x z) =
      2 • latticePoint L z-(latticePoint L b+latticePoint L x) := by
  simp only [k4SphereLabel,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq,two_smul]
  abel

/-- The second energy is exactly the sphere equation for the actual
integer doubled label. -/
theorem k4_sphere_energy_identity {d : ℕ} (b x z : Mom d) :
    ‖2 • z-(b+x)‖^2 =
      2*(-‖x‖^2+‖z‖^2+‖b+x-z‖^2)-‖b+x‖^2+2*‖x‖^2 := by
  have he := k4_second_energy b x z
  have hv : 2 • z-(b+x) = (2 : ℝ) • (z-(1/2 : ℝ) • (b+x)) := by module
  rw [hv,norm_smul,Real.norm_eq_abs,show |(2 : ℝ)|=2 by norm_num]
  nlinarith only [he]

/-- The third energy is exactly the independent strip on the same actual
sphere variable. -/
theorem k4_strip_energy_identity {d : ℕ} (b c x y z : Mom d) :
    inner ℝ (c+y) (2 • z-(b+x)) =
      (-‖z‖^2-‖y‖^2+‖c+y+z‖^2)-‖c+y‖^2+‖y‖^2-inner ℝ (c+y) (b+x) := by
  rw [k4_third_energy]
  simp only [two_smul,inner_sub_right,inner_add_right]
  ring

/-- Every actual source point satisfies the sphere equation, with exactly
twice its original energy tolerance and no additional parameter premise. -/
theorem k4CanonicalSet_sphere {d : ℕ} {L : ℝ} {A : Fin 6 → Mom d}
    {a b c : Fin d → ℤ} {β : Fin 3 → ℝ} {τ : ℝ}
    {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ k4CanonicalSet L A a b c β τ) :
    |‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖^2-
      (2*β 1-‖latticePoint L b+latticePoint L p.1‖^2+2*‖latticePoint L p.1‖^2)| ≤ 2*τ := by
  have hlabels := congrFun (k4Labels_latticePoint L a b c p.1 p.2.1 p.2.2)
  have he := hp.2.2.1
  change |-‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 1)‖^2+
    ‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 2)‖^2+
    ‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 4)‖^2-β 1| ≤ τ at he
  rw [hlabels 1,hlabels 2,hlabels 4] at he
  change |-‖latticePoint L p.1‖^2+‖latticePoint L p.2.2‖^2+
    ‖latticePoint L b+latticePoint L p.1-latticePoint L p.2.2‖^2-β 1| ≤ τ at he
  rw [latticePoint_k4SphereLabel,k4_sphere_energy_identity]
  have hid : 2*(-‖latticePoint L p.1‖^2+‖latticePoint L p.2.2‖^2+
      ‖latticePoint L b+latticePoint L p.1-latticePoint L p.2.2‖^2)-
      ‖latticePoint L b+latticePoint L p.1‖^2+2*‖latticePoint L p.1‖^2-
      (2*β 1-‖latticePoint L b+latticePoint L p.1‖^2+2*‖latticePoint L p.1‖^2) =
    2*(-‖latticePoint L p.1‖^2+‖latticePoint L p.2.2‖^2+
      ‖latticePoint L b+latticePoint L p.1-latticePoint L p.2.2‖^2-β 1) := by ring
  rw [hid,abs_mul,show |(2 : ℝ)|=2 by norm_num]
  exact mul_le_mul_of_nonneg_left he (by norm_num)

/-- The literal first-vertex base constraints of every canonical point. -/
theorem k4CanonicalSet_first {d : ℕ} {L : ℝ} {A : Fin 6 → Mom d}
    {a b c : Fin d → ℤ} {β : Fin 3 → ℝ} {τ : ℝ}
    {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ k4CanonicalSet L A a b c β τ) :
    NearLattice L (A 1) p.1 ∧ NearLattice L (A 3) p.2.1 ∧
      NearLattice L (A 0) (p.1+p.2.1-a) ∧
      |-‖latticePoint L (p.1+p.2.1-a)‖^2+‖latticePoint L p.1‖^2+
        ‖latticePoint L p.2.1‖^2-β 0| ≤ τ :=
  ⟨hp.1 1,hp.1 3,hp.1 0,hp.2.1⟩

/-- Every actual source point satisfies the independent strip on the
same actual doubled integer label used in the sphere equation. -/
theorem k4CanonicalSet_strip {d : ℕ} {L : ℝ} {A : Fin 6 → Mom d}
    {a b c : Fin d → ℤ} {β : Fin 3 → ℝ} {τ : ℝ}
    {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ k4CanonicalSet L A a b c β τ) :
    |inner ℝ (latticePoint L c+latticePoint L p.2.1)
        (latticePoint L (k4SphereLabel b p.1 p.2.2))-
      (β 2-‖latticePoint L c+latticePoint L p.2.1‖^2+‖latticePoint L p.2.1‖^2-
        inner ℝ (latticePoint L c+latticePoint L p.2.1) (latticePoint L b+latticePoint L p.1))| ≤ τ := by
  have hlabels := congrFun (k4Labels_latticePoint L a b c p.1 p.2.1 p.2.2)
  have he := hp.2.2.2
  change |-‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 2)‖^2-
    ‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 3)‖^2+
    ‖latticePoint L (k4Labels a b c p.1 p.2.1 p.2.2 5)‖^2-β 2| ≤ τ at he
  rw [hlabels 2,hlabels 3,hlabels 5] at he
  change |-‖latticePoint L p.2.2‖^2-‖latticePoint L p.2.1‖^2+
    ‖latticePoint L c+latticePoint L p.2.1+latticePoint L p.2.2‖^2-β 2| ≤ τ at he
  rw [latticePoint_k4SphereLabel,k4_strip_energy_identity]
  convert he using 1 <;> congr 1 <;> ring

/-- The doubled sphere variable lies in an actual radius-two ball with
its exact affine center; no bound on that center is imposed. -/
theorem k4CanonicalSet_sphere_ball {d : ℕ} {L : ℝ} {A : Fin 6 → Mom d}
    {a b c : Fin d → ℤ} {β : Fin 3 → ℝ} {τ : ℝ}
    {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ k4CanonicalSet L A a b c β τ) :
    ‖latticePoint L (k4SphereLabel b p.1 p.2.2)-
      (2 • A 2-(latticePoint L b+latticePoint L p.1))‖ ≤ 2 := by
  have hz : NearLattice L (A 2) p.2.2 := hp.1 2
  rw [latticePoint_k4SphereLabel]
  have he : 2 • latticePoint L p.2.2-(latticePoint L b+latticePoint L p.1)-
      (2 • A 2-(latticePoint L b+latticePoint L p.1)) =
      (2 : ℝ) • (latticePoint L p.2.2-A 2) := by module
  rw [he,norm_smul,Real.norm_eq_abs,show |(2 : ℝ)|=2 by norm_num]
  have hh := mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_one] using hh

/-- Exact rescaling of an actual physical squared shell to integer scale. -/
theorem k4_integer_shell {d : ℕ} {L W K : ℝ} (hL : 0 < L) (n : Fin d → ℤ)
    (hs : |‖latticePoint L n‖^2-K| ≤ W) :
    |‖latticePoint 1 n‖^2-L^2*K| ≤ L^2*W := by
  rw [latticePoint_one_eq_smul hL.ne',norm_smul,Real.norm_eq_abs,abs_of_pos hL]
  have he : (L*‖latticePoint L n‖)^2-L^2*K = L^2*(‖latticePoint L n‖^2-K) := by ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg L)]
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg L)

/-- Exact rescaling of the actual physical strip to integer coordinates. -/
theorem k4_integer_strip {d : ℕ} {L T α : ℝ} (hL : 0 < L) (r : Mom d) (n : Fin d → ℤ)
    (hs : |inner ℝ r (latticePoint L n)-α| ≤ T) :
    |inner ℝ r (latticePoint 1 n)-L*α| ≤ L*T := by
  rw [latticePoint_one_eq_smul hL.ne',real_inner_smul_right,← mul_sub,abs_mul,abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left hs hL.le

/-- Exact rescaling of the actual affine spatial ball. -/
theorem k4_integer_ball {d : ℕ} {L B : ℝ} (hL : 0 < L) (b : Mom d) (n : Fin d → ℤ)
    (hb : ‖latticePoint L n-b‖ ≤ B) :
    ‖latticePoint 1 n-L • b‖ ≤ L*B := by
  rw [latticePoint_one_eq_smul hL.ne',← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left hb hL.le

end WaveTurbulence.MoleProp
