/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtomReduction
public import WaveTurbulence.Foundations.CountLemmas.ShellThresholdLift

/-! # Completing the square for the same-sign atomic count -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- A same-sign atom pair projects injectively into an actual squared-radius
shell at integer scale. No bound on its center or energy is imposed. -/
theorem positive_atom_shell_threshold_bound {d : ℕ} {L τ : ℝ} (hL : 0 < L)
    (hτ : 0 ≤ τ) (hW : 1 ≤ τ*L^2) {U : ℝ}
    (hWU : τ*L^2 ≤ U) (hbudget : L^2*(τ*L^2) ≤ U^3) (a b : Mom (d+2))
    (nk : Fin (d+2) → ℤ) (β : ℝ) :
    ((atomPairSet L a b nk β τ 1).ncard : ℝ) ≤
      (2*L+1)^d*(6*Real.pi+1924002)*U := by
  classical
  let S := (finite_atomPairSet hL a b nk β τ 1).toFinset
  let T := S.image Prod.fst
  let k := latticePoint L nk
  let c := (L/2) • k
  let K := (L^2/2)*(β-‖k‖^2/2)
  have hc : S.card = T.card := (card_image_of_injOn
    (fun q hq r hr he => atomPair_fst_injOn L a b nk β τ 1
      ((finite_atomPairSet hL a b nk β τ 1).mem_toFinset.mp hq)
      ((finite_atomPairSet hL a b nk β τ 1).mem_toFinset.mp hr) he)).symm
  have hb := card_squared_shell_threshold_le T c (fun j => L*a j) (K := K) hW hL.le hWU hbudget
    (by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
      exact (Counting.mem_latticeBox _ _ _).mp (nearLattice_mem_box hL a q.1
        ((finite_atomPairSet hL a b nk β τ 1).mem_toFinset.mp hq).1))
    (by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
      have hq' := (finite_atomPairSet hL a b nk β τ 1).mem_toFinset.mp hq
      have hcon : q.1+q.2 = nk := by simpa using hq'.2.2.1
      have hk : latticePoint L q.1+latticePoint L q.2 = k := by
        rw [← WeylSums.latticePoint_add_eq,hcon]
      have he := two_vector_square_identity (latticePoint L q.1) (latticePoint L q.2)
      rw [hk] at he
      have hid : latticePoint 1 q.1-c = L • (latticePoint L q.1-(1/2 : ℝ) • k) := by
        rw [latticePoint_one_eq_smul hL.ne']
        dsimp only [c]
        module
      have heq : ‖latticePoint 1 q.1-c‖^2-K = (L^2/2)*
          (‖latticePoint L q.1‖^2+‖latticePoint L q.2‖^2-β) := by
        rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos hL,mul_pow]
        dsimp only [K]
        nlinarith only [he]
      rw [heq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ L^2/2)]
      have hh : |‖latticePoint L q.1‖^2+‖latticePoint L q.2‖^2-β| ≤ τ := by
        simpa using hq'.2.2.2
      calc
        _ ≤ (L^2/2)*τ := mul_le_mul_of_nonneg_left hh (by positivity)
        _ ≤ τ*L^2 := by nlinarith only [mul_nonneg (sq_nonneg L) hτ])
  rw [Set.ncard_eq_toFinset_card _ (finite_atomPairSet hL a b nk β τ 1)]
  exact (congrArg (fun n : ℕ => (n : ℝ)) hc).le.trans hb

end WaveTurbulence.CountLemmas
