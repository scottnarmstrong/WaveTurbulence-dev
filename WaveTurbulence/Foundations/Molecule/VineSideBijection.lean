/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideRelabel
import Mathlib.Tactic

/-! # Explicit bijection between expanded V labels and a long VII side -/

public section
namespace WaveTurbulence.Vine

/-- Every canonical label lands on the selected side. -/
theorem sideEmbedding_mem (N m i : ℕ) (hi : i<9+2*m) :
    sideEmbedding N m i ∈ sideLabels N (m+2) := by
  rw [mem_sideLabels_iff]
  by_cases hcore : i<9
  · interval_cases i <;> simp [sideEmbedding] <;> omega
  · obtain ⟨t,rfl⟩ : ∃ t,i=t+9 := ⟨i-9,by omega⟩
    rw [sideEmbedding_large]
    split <;> omega

/-- The explicit inverse lies in the canonical atom range and recovers the
selected side label. No choice of graph isomorphism enters this construction. -/
theorem sideInverse_spec (N m a : ℕ) (hN : 9 ≤ N)
    (ha : a ∈ sideLabels N (m+2)) :
    sideInverse N m a<9+2*m ∧ sideEmbedding N m (sideInverse N m a)=a := by
  rw [mem_sideLabels_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | ⟨hlo,hhi⟩
  · constructor <;> simp [sideInverse,sideCoreInverse,sideEmbedding]; omega
  · constructor <;> simp [sideInverse,sideCoreInverse,sideEmbedding]; omega
  · constructor <;> simp [sideInverse,sideCoreInverse,sideEmbedding]; omega
  · constructor <;> simp [sideInverse,sideCoreInverse,sideEmbedding]
  · constructor <;> simp [sideInverse,sideCoreInverse,sideEmbedding]; omega
  · obtain ⟨j,rfl⟩ : ∃ j,a=N+j := ⟨a-N,by omega⟩
    by_cases hu : j<m+2
    · rw [sideInverse_upper N m j hN hu]
      by_cases hz : j=0
      · subst j
        simp [sideEmbedding]; omega
      · by_cases hl : j=m+1
        · subst j
          simp [sideEmbedding]; omega
        · simp only [hz,hl,ite_false]
          constructor
          · omega
          · rw [sideEmbedding_upper N m (m-j) (by omega)]
            omega
    · obtain ⟨l,rfl⟩ : ∃ l,j=(m+2)+l := ⟨j-(m+2),by omega⟩
      have he : N+(m+2+l)=N+(m+2)+l := by omega
      rw [he,sideInverse_lower N m l hN]
      by_cases hz : l=0
      · subst l
        simp [sideEmbedding]; omega
      · by_cases hl : l=m+1
        · subst l
          simp [sideEmbedding]; omega
        · simp only [hz,hl,ite_false]
          constructor
          · omega
          · rw [sideEmbedding_lower]
            omega

/-- Injectivity on the finite canonical label range follows from the literal
left inverse, without a cardinality argument. -/
theorem sideEmbedding_injOn (N m : ℕ) (hN : 9 ≤ N) :
    Set.InjOn (sideEmbedding N m) {i | i<9+2*m} := by
  intro i hi j hj he
  have := congrArg (sideInverse N m) he
  rwa [sideInverse_sideEmbedding N m i hN hi,
    sideInverse_sideEmbedding N m j hN hj] at this

end WaveTurbulence.Vine
