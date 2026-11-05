/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafPairUniqueness
public import WaveTurbulence.Foundations.XChain.SysDraft.Kernel
/-! The attached-kernel sum has exactly one two-point component and vanishes at unbalanced signs. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem lowerKernelSum_pair {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin 2 → ℤˣ) (hs : sig 1 = -sig 0) (p N : ℕ) (n : Fin 2 → (Fin d → ℤ)) :
    lowerKernelSum L γ δ F sig p N n =
      if n 0 = n 1 then (F p (latticePoint L (n 0)) : ℂ) else 0 := by
  let D := leafPairLowerData sig hs p N
  have he : (∑ E : LowerGraftData sig p N, KG L γ δ F E.low p n) = KG L γ δ F D.low p n :=
    sum_eq_single D (fun E _ hne => False.elim (hne (Subsingleton.elim _ _))) (by simp)
  exact he.trans (KG_leafPair L γ δ F D.low (fun _ => rfl) (fun _ => rfl) p (fun _ => rfl) p n)

theorem lowerKernelSum_unbalanced {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (p N : ℕ) (h : ∑ j, (sig j : ℤ) ≠ 0) (n : Fin w → (Fin d → ℤ)) :
    lowerKernelSum L γ δ F sig p N n = 0 := by
  haveI : IsEmpty (LowerGraftData sig p N) := ⟨fun D => h (by
    rw [← D.sign]
    exact SysAPI.Garden.sum_sig_eq_zero D.low.garden D.plain)⟩
  simp only [lowerKernelSum, Finset.univ_eq_empty, sum_empty]

theorem neg_sig_one_of_balanced_two (sig : Fin 2 → ℤˣ) (hs : ∑ j, (sig j : ℤ) = 0) :
    sig 1 = -sig 0 := by
  apply Units.ext
  change (sig 1 : ℤ) = -(sig 0 : ℤ)
  have h : (sig 0 : ℤ) + (sig 1 : ℤ) = 0 := by simpa only [Fin.sum_univ_two] using hs
  omega

end WaveTurbulence.Induct
