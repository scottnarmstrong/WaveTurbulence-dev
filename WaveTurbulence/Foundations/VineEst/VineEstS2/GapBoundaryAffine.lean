/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices

/-! # Exact frozen affine boundary shifts and their common-coset identity -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open RegRed

/-- The source anchor decoder is an integer combination of exactly the
four frozen boundary arguments, with total coefficient one. -/
theorem gapBoundaryRow_eval {E : Type*} [AddCommGroup E] (q : ℤ) (β : Fin 4 → E) :
    (∑ c, gapBoundaryRow q c • β c) = β 2+q • (β 2-β 3) := by
  simp only [Fin.sum_univ_succ,gapBoundaryRow]
  norm_num
  simp only [add_smul,one_smul,smul_sub]
  abel

/-- The physical source coset shift is exactly the frozen affine shift. -/
theorem gapBoundaryRow_physical {d : ℕ} (L : ℝ) (base : Mom d)
    (q : ℤ) (β : Fin 4 → (Fin d → ℤ)) :
    (∑ c, (gapBoundaryRow q c : ℝ) • (base+latticePoint L (β c))) =
      base+latticePoint L (β 2+q • (β 2-β 3)) := by
  have he := gapBoundaryRow_eval q (fun c => base+latticePoint L (β c))
  simp only [Int.cast_smul_eq_zsmul]
  rw [he]
  let f := latticePointAddHom (d := d) L
  change (base+f (β 2))+q • ((base+f (β 2))-(base+f (β 3))) = base+f (β 2+q • (β 2-β 3))
  rw [map_add,map_zsmul,map_sub]
  rw [add_sub_add_left_eq_sub]
  abel

end WaveTurbulence.VineEstS2
