/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# A finite cover for the exact output momentum set

The common affine lattice and the four unit balls leave at most
`(3L)^(4d)` output quadruples when `L≥1`. No momentum regularity is used.
This is the finite supremum input to the Plancherel step.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Integer choices for one output unit ball. -/
@[expose] noncomputable def outputIntegerBox {d : ℕ} (D : SumintDatum d) (L : ℝ) (c : Fin 4) :
    Finset (Fin d → ℤ) :=
  Counting.latticeBox (fun j => L * (D.centre c j - D.wBar j)) L

/-- A concrete finite family containing every allowed output quadruple. -/
@[expose] noncomputable def outputCover {d : ℕ} (D : SumintDatum d) (L : ℝ) :
    Finset (Fin 4 → Mom d) := by
  classical
  exact (Fintype.piFinset (outputIntegerBox D L)).image
    (fun n c => D.wBar + latticePoint L (n c))

/-- The literal draft coset and ball premises give membership in the cover. -/
theorem mem_outputCover {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (E : Fin 4 → Mom d)
    (hE : ∀ c, (∃ n : Fin d → ℤ, E c = D.wBar + latticePoint L n) ∧ ‖E c - D.centre c‖ ≤ 1) :
    E ∈ outputCover D L := by
  classical
  choose n hn using fun c => (hE c).1
  apply Finset.mem_image.mpr
  refine ⟨n, Fintype.mem_piFinset.mpr ?_, ?_⟩
  · intro c
    apply (Counting.mem_latticeBox _ _ _).mpr
    intro j
    have hb : |E c j - D.centre c j| ≤ 1 :=
      (show |E c j - D.centre c j| ≤ ‖E c - D.centre c‖ from
        PiLp.norm_apply_le (E c - D.centre c) j).trans (hE c).2
    rw [hn c] at hb
    change |D.wBar j + (n c j : ℝ) / L - D.centre c j| ≤ 1 at hb
    have he : (n c j : ℝ) - L * (D.centre c j - D.wBar j) =
        L * (D.wBar j + (n c j : ℝ) / L - D.centre c j) := by
      field_simp
      <;> ring
    rw [he, abs_mul, abs_of_pos hL]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hL.le
  · funext c
    exact (hn c).symm

/-- The finite output family has the dimension-only polynomial cardinality used in Step 3. -/
theorem card_outputCover_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 1 ≤ L) :
    ((outputCover D L).card : ℝ) ≤ (3 * L)^(4 * d) := by
  classical
  have hc (c : Fin 4) : ((outputIntegerBox D L c).card : ℝ) ≤ (3 * L)^d := by
    apply (Counting.card_latticeBox_le _ (by linarith : 0 ≤ L)).trans
    apply pow_le_pow_left₀ (by linarith)
    linarith
  calc
    _ ≤ ((Fintype.piFinset (outputIntegerBox D L)).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ = ∏ c, ((outputIntegerBox D L c).card : ℝ) := by
      rw [Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ _c : Fin 4, (3 * L)^d :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun c _ => hc c)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

end WaveTurbulence.Sumint
