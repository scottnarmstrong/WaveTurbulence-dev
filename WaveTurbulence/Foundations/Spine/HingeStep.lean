/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SubLadder
public import WaveTurbulence.Foundations.WaveB.Ladders
/-! # Removing one atom from a list of disjoint ladders (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

theorem Lad.sub_atoms_mem (ℓ : Lad G) (s m' : ℕ) (hs : s + m' ≤ ℓ.1) (x : GBranch G.tree)
    (hx : x ∈ (ℓ.sub s m').atoms) :
    ∃ k : Fin (ℓ.1 + 1), s ≤ (k : ℕ) ∧ (k : ℕ) ≤ s + m' ∧ (x = ℓ.2.1 k ∨ x = ℓ.2.2 k) := by
  rw [Lad.mem_atoms_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hk2 : (k : ℕ) < m' + 1 := k.2
  have hmin : (⟨min (s + (k : ℕ)) ℓ.1, by omega⟩ : Fin (ℓ.1 + 1)) = ⟨s + k, by omega⟩ :=
    Fin.ext (by simp only; omega)
  refine ⟨⟨s + k, by omega⟩, by simp, by simp; omega, ?_⟩
  rcases hk with rfl | rfl
  · exact Or.inl (by simp only [Lad.sub, hmin])
  · exact Or.inr (by simp only [Lad.sub, hmin])

/-- Atoms of rungs with different indices are different. -/
theorem Lad.atom_rung_ne (ℓ : Lad G) (h : ℓ.IsL) (k k' : Fin (ℓ.1 + 1)) (hk : k ≠ k')
    (x : GBranch G.tree) (hx : x = ℓ.2.1 k ∨ x = ℓ.2.2 k) (hx' : x = ℓ.2.1 k' ∨ x = ℓ.2.2 k') : False := by
  obtain ⟨hu, hv, hcross⟩ := Sum.elim_injective.mp h.2.1
  rcases hx with rfl | rfl <;> rcases hx' with h' | h'
  · exact hk (hu h')
  · exact hcross _ _ h'
  · exact hcross _ _ h'.symm
  · exact hk (hv h')

lemma Lad.rungInc_le_one (layer : GBranch G.tree → ℕ) (ℓ : Lad G) (k : ℕ) : ℓ.rungInc layer k ≤ 1 := by
  unfold Lad.rungInc
  split_ifs <;> omega

end WaveTurbulence.CoarseSpliced
