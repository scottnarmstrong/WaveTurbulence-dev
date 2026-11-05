/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideLabels
import Mathlib.Tactic

/-! # Explicit labels for the side-ladder/type-V isomorphism

The side has m+2 full rungs. The canonical type-V core supplies its first
and last rungs, and its m inserted rungs run through the middle in reverse
order. The inverse is used only on sideLabels N (m+2); values outside those
finite sets are the total extension specified by the displayed formulas.
-/

public section
namespace WaveTurbulence.Vine

/-- Embed canonical type-V labels into the side with m+2 full rungs. -/
@[expose] def sideEmbedding (N m : ℕ) : ℕ → ℕ
  | 0 => 7
  | 1 => 8
  | 2 => N+(m+1)
  | 3 => N+(m+2)+(m+1)
  | 4 => N
  | 5 => N+(m+2)
  | 6 => 5
  | 7 => 6
  | 8 => 4
  | t+9 => if t<m then N+(m-t) else N+(m+2)+(m-(t-m))

/-- The inverse table on the five old side-core labels; unused small
labels are sent to0 as a total extension. -/
@[expose] def sideCoreInverse : ℕ → ℕ
  | 4 => 8
  | 5 => 6
  | 6 => 7
  | 7 => 0
  | 8 => 1
  | _ => 0

/-- Explicit inverse side labels, with separate first/last rung cases. -/
@[expose] def sideInverse (N m a : ℕ) : ℕ :=
  if a<9 then sideCoreInverse a else
    if a<N+(m+2) then
      let j := a-N
      if j=0 then 4 else if j=m+1 then 2 else 9+(m-j)
    else
      let j := a-(N+(m+2))
      if j=0 then 5 else if j=m+1 then 3 else 9+m+(m-j)

/-- Labels beyond the nine canonical core atoms use the two rail formulas. -/
theorem sideEmbedding_large (N m t : ℕ) : sideEmbedding N m (t+9)=
    if t<m then N+(m-t) else N+(m+2)+(m-(t-m)) := rfl

/-- Canonical inserted upper labels traverse the old middle rungs backwards. -/
theorem sideEmbedding_upper (N m i : ℕ) (hi : i<m) :
    sideEmbedding N m (9+i)=N+(m-i) := by
  rw [Nat.add_comm 9 i,sideEmbedding_large]
  simp only [hi,ite_true]

/-- Canonical lower labels traverse the lower old middle rungs backwards. -/
theorem sideEmbedding_lower (N m i : ℕ) :
    sideEmbedding N m (9+m+i)=N+(m+2)+(m-i) := by
  have he : 9+m+i=(m+i)+9 := by omega
  rw [he,sideEmbedding_large]
  have hn : ¬m+i<m := by omega
  have hs : m+i-m=i := by omega
  simp only [hn,ite_false,hs]

/-- Inverse labels on the upper side rail, including its first/last rungs. -/
theorem sideInverse_upper (N m j : ℕ) (hN : 9 ≤ N) (hj : j<m+2) :
    sideInverse N m (N+j)=if j=0 then 4 else if j=m+1 then 2 else 9+(m-j) := by
  have hsmall : ¬N+j<9 := by omega
  have hupper : N+j<N+(m+2) := by omega
  simp only [sideInverse,hsmall,ite_false,hupper,ite_true,Nat.add_sub_cancel_left]

/-- Inverse labels on the lower side rail. The formula also specifies the
total extension beyond its final rung. -/
theorem sideInverse_lower (N m j : ℕ) (hN : 9 ≤ N) :
    sideInverse N m (N+(m+2)+j)=if j=0 then 5 else if j=m+1 then 3 else 9+m+(m-j) := by
  have hsmall : ¬N+(m+2)+j<9 := by omega
  have hupper : ¬N+(m+2)+j<N+(m+2) := by omega
  simp only [sideInverse,hsmall,ite_false,hupper,Nat.add_sub_cancel_left]

/-- The explicit inverse recovers every label of the canonical expanded
V template, whose atom count is9+2m. -/
theorem sideInverse_sideEmbedding (N m i : ℕ) (hN : 9 ≤ N) (hi : i<9+2*m) :
    sideInverse N m (sideEmbedding N m i)=i := by
  by_cases hcore : i<9
  · interval_cases i
    · rfl
    · rfl
    · simpa [sideEmbedding] using sideInverse_upper N m (m+1) hN (by omega)
    · simpa [sideEmbedding] using sideInverse_lower N m (m+1) hN
    · simpa [sideEmbedding] using sideInverse_upper N m 0 hN (by omega)
    · simpa [sideEmbedding] using sideInverse_lower N m 0 hN
    · rfl
    · rfl
    · rfl
  · obtain ⟨t,rfl⟩ : ∃ t,i=t+9 := ⟨i-9,by omega⟩
    rw [sideEmbedding_large]
    by_cases ht : t<m
    · simp only [ht,ite_true]
      rw [sideInverse_upper N m (m-t) hN (by omega)]
      have hz : m-t ≠ 0 := by omega
      have hl : m-t ≠ m+1 := by omega
      simp only [hz,hl,ite_false]
      omega
    · simp only [ht,ite_false]
      rw [sideInverse_lower N m (m-(t-m)) hN]
      have hz : m-(t-m) ≠ 0 := by omega
      have hl : m-(t-m) ≠ m+1 := by omega
      simp only [hz,hl,ite_false]
      omega

end WaveTurbulence.Vine
