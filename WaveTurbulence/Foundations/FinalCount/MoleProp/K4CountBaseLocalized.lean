/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountLocalized
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountAlgebra
import Mathlib.Tactic

/-! # The actual canonical K4 localized base projection

The bilinear coefficient is k4−a, while the radius restriction is on
k4+c. Their centers are distinct and arbitrary; the proved translated
coefficient-ball estimate retains this distinction exactly.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- Actual canonical base labels with a radius-restricted strip coefficient
satisfy the localized elementary bound. The exceptional k4=a fiber is
handled separately by the two-free-label box count. -/
theorem k4_base_localized_pair_le {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L R τ : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (a c : Fin d → ℤ) (A1 : Mom d) (β : ℝ)
    (hS : ∀ p ∈ S, NearLattice L A1 p.1 ∧ ‖latticePoint L (p.2+c)‖ ≤ R ∧ p.2 ≠ a ∧
      |-‖latticePoint L (p.1+p.2-a)‖^2+‖latticePoint L p.1‖^2+
        ‖latticePoint L p.2‖^2-β| ≤ τ) :
    (S.card : ℝ) ≤ (d : ℝ)*((2*(L*R)+1)^(d-1)*(2*L+1)^(d-1)*
      (τ*L^2*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))+(2*(L*R)+1))) := by
  classical
  let f := fun p : (Fin d → ℤ) × (Fin d → ℤ) => (p.1-a,p.2-a)
  have hinj : Set.InjOn f (S : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    intro p _hp q _hq he
    apply Prod.ext
    · funext i
      have hh := congrFun (congrArg Prod.fst he) i
      change p.1 i-a i=q.1 i-a i at hh
      omega
    · funext i
      have hh := congrFun (congrArg Prod.snd he) i
      change p.2 i-a i=q.2 i-a i at hh
      omega
  have hmap : ∀ q ∈ S.image f,
      NearLattice L (A1-latticePoint L a) q.1 ∧
      ‖latticePoint L q.2-(-latticePoint L (c+a))‖ ≤ R ∧ q.2 ≠ 0 ∧
      |inner ℝ (latticePoint L q.2) (latticePoint L q.1)-
        ((‖latticePoint L a‖^2-β)/2)| ≤ τ/2 := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hs := hS p hp
    refine ⟨?_,?_,?_,?_⟩
    · change ‖latticePoint L (p.1-a)-(A1-latticePoint L a)‖ ≤ 1
      rw [WeylSums.latticePoint_sub_eq]
      have he : latticePoint L p.1-latticePoint L a-(A1-latticePoint L a) = latticePoint L p.1-A1 := by abel
      rw [he]
      exact hs.1
    · change ‖latticePoint L (p.2-a)-(-latticePoint L (c+a))‖ ≤ R
      have he : latticePoint L (p.2-a)-(-latticePoint L (c+a)) = latticePoint L (p.2+c) := by
        simp only [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_add_eq]
        abel
      rw [he]
      exact hs.2.1
    · change p.2-a ≠ 0
      intro he
      apply hs.2.2.1
      funext i
      have hh := congrFun he i
      change p.2 i-a i=0 at hh
      omega
    · change |inner ℝ (latticePoint L (p.2-a)) (latticePoint L (p.1-a))-
          ((‖latticePoint L a‖^2-β)/2)| ≤ τ/2
      rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq,real_inner_comm]
      have he := k4_first_energy (latticePoint L a) (latticePoint L p.1) (latticePoint L p.2)
      have hsE := hs.2.2.2
      rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_add_eq] at hsE
      have hid : inner ℝ (latticePoint L p.1-latticePoint L a) (latticePoint L p.2-latticePoint L a)-
          ((‖latticePoint L a‖^2-β)/2) =
        -(-‖latticePoint L p.1+latticePoint L p.2-latticePoint L a‖^2+
          ‖latticePoint L p.1‖^2+‖latticePoint L p.2‖^2-β)/2 := by linarith only [he]
      rw [hid,abs_div,abs_neg,show |(2 : ℝ)|=2 by norm_num]
      exact div_le_div_of_nonneg_right hsE (by norm_num)
  have hh := k4_localized_pair_le (S.image f) hL hR (div_nonneg hτ (by norm_num))
    (A1-latticePoint L a) (-latticePoint L (c+a)) ((‖latticePoint L a‖^2-β)/2) hmap
  rw [card_image_of_injOn hinj] at hh
  convert hh using 1 <;> ring

end WaveTurbulence.MoleProp
