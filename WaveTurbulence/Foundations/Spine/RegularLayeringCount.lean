/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CodeLayeringCount
public import WaveTurbulence.Foundations.RegStruct.SourceCoupleCount
/-! Actual regular-layered carrier count at each incoherency, using the proved code and C4 counts. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Links WaveTurbulence.Reg
open Set Finset

def regularLayeredCouplesAt (p n g : ℕ) : Set (LayeredGarden 2) :=
  ⋃ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}, codeLayeredCouples p Q.1 g

theorem finite_regularLayeredCouplesAt (p n g : ℕ) : (regularLayeredCouplesAt p n g).Finite := by
  let _ := finite_coupleCodes n
  exact Set.finite_iUnion fun Q => finite_codeLayeredCouples p Q.1 Q.2.1 g

/-- TARGET L2230–2232: count whole regular couples and their canonical layerings together.
The regular-code factor is absolute and the layering factor depends on p only through 2^(9p). -/
theorem ncard_regularLayeredCouplesAt_le (p n g : ℕ) :
    (regularLayeredCouplesAt p n g).ncard ≤ (12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) := by
  classical
  let _ := finite_coupleCodes n
  let _ : Fintype {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} := Fintype.ofFinite _
  have h := Set.ncard_iUnion_le_of_fintype
    (fun Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} => codeLayeredCouples p Q.1 g)
  have hsum : (∑ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n},
      (codeLayeredCouples p Q.1 g).ncard) ≤
      coupleCodeCount n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) := by
    calc
      _ ≤ ∑ _Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n},
          (2 ^ (9 * p)) ^ g * 2 ^ (2 * n) := by
        apply Finset.sum_le_sum
        intro Q _
        simpa only [Q.2.2] using ncard_codeLayeredCouples_le p Q.1 Q.2.1 g
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, coupleCodeCount, Nat.card_eq_fintype_card, Nat.cast_id]
  exact h.trans (hsum.trans (Nat.mul_le_mul_right _ (coupleCodeCount_le_pow n)))

end WaveTurbulence.LGSpine
