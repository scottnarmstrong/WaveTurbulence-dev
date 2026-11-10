/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoarseSplicedDraft.LadderCounts
/-! # Sub-ladders of consecutive rungs (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

/-- A ladder presentation `(m, u, v)`. -/
abbrev Lad (G : Garden w) :=
  Σ m : ℕ, (Fin (m + 1) → GBranch G.tree) × (Fin (m + 1) → GBranch G.tree)

def Lad.atoms (ℓ : Lad G) : Finset (GBranch G.tree) := Molecule.ladderAtoms ℓ.2.1 ℓ.2.2

def Lad.IsL (ℓ : Lad G) : Prop := G.molecule.IsLadder ℓ.2.1 ℓ.2.2

noncomputable def Lad.inc (layer : GBranch G.tree → ℕ) (ℓ : Lad G) : ℕ :=
  sourceLadderIncoherency G layer ℓ.2.1 ℓ.2.2

/-- The sub-ladder of the `m' + 1` consecutive rungs starting at rung `s`. -/
def Lad.sub (ℓ : Lad G) (s m' : ℕ) : Lad G :=
  ⟨m', fun t => ℓ.2.1 ⟨min (s + t) ℓ.1, by omega⟩, fun t => ℓ.2.2 ⟨min (s + t) ℓ.1, by omega⟩⟩

theorem Lad.IsL.sub {ℓ : Lad G} (h : ℓ.IsL) (s m' : ℕ) (hs : s + m' ≤ ℓ.1) (hm' : 1 ≤ m') :
    (ℓ.sub s m').IsL := by
  obtain ⟨-, hinj, hmem, hbb, hrail⟩ := h
  obtain ⟨hu, hv, hcross⟩ := Sum.elim_injective.mp hinj
  unfold Lad.IsL Lad.sub
  dsimp only
  refine ⟨hm', ?_, ?_, ?_, ?_⟩
  · refine Sum.elim_injective.mpr ⟨?_, ?_, ?_⟩
    · intro a b hab
      have h1 := congrArg Fin.val (hu hab)
      simp only at h1
      apply Fin.ext
      have := a.2; have := b.2
      omega
    · intro a b hab
      have h1 := congrArg Fin.val (hv hab)
      simp only at h1
      apply Fin.ext
      have := a.2; have := b.2
      omega
    · intro a b hab
      exact hcross _ _ hab
  · intro j
    exact hmem _
  · intro j
    exact hbb _
  · intro j
    have e1 : (⟨min (s + ((j.castSucc : Fin (m' + 1)) : ℕ)) ℓ.1, by omega⟩ : Fin (ℓ.1 + 1)) =
        (⟨s + j, by omega⟩ : Fin ℓ.1).castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    have e2 : (⟨min (s + ((j.succ : Fin (m' + 1)) : ℕ)) ℓ.1, by omega⟩ : Fin (ℓ.1 + 1)) =
        (⟨s + j, by omega⟩ : Fin ℓ.1).succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    have := hrail ⟨s + j, by omega⟩
    rw [← e1, ← e2] at this
    exact this

theorem Lad.mem_atoms_iff (ℓ : Lad G) (x : GBranch G.tree) :
    x ∈ ℓ.atoms ↔ ∃ k : Fin (ℓ.1 + 1), x = ℓ.2.1 k ∨ x = ℓ.2.2 k := by
  unfold Lad.atoms Molecule.ladderAtoms
  simp only [mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨k, Or.inr rfl⟩
  · rintro ⟨k, rfl | rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩

theorem Lad.sub_atoms_subset (ℓ : Lad G) (s m' : ℕ) (hs : s + m' ≤ ℓ.1) :
    (ℓ.sub s m').atoms ⊆ ℓ.atoms := by
  intro x hx
  rw [Lad.mem_atoms_iff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have hk2 : (k : ℕ) < m' + 1 := k.2
  have hmin : (⟨min (s + (k : ℕ)) ℓ.1, by omega⟩ : Fin (ℓ.1 + 1)) = ⟨s + k, by omega⟩ :=
    Fin.ext (by simp only; omega)
  rcases hk with rfl | rfl
  · exact ⟨⟨s + k, by omega⟩, Or.inl (by simp only [Lad.sub, hmin])⟩
  · exact ⟨⟨s + k, by omega⟩, Or.inr (by simp only [Lad.sub, hmin])⟩

/-- The per-rung incoherency indicator, extended by zero. -/
noncomputable def Lad.rungInc (layer : GBranch G.tree → ℕ) (ℓ : Lad G) (k : ℕ) : ℕ :=
  if h : k < ℓ.1 + 1 then (if layer (ℓ.2.1 ⟨k, h⟩) = layer (ℓ.2.2 ⟨k, h⟩) then 0 else 1) else 0

theorem Lad.inc_eq_sum (layer : GBranch G.tree → ℕ) (ℓ : Lad G) :
    ℓ.inc layer = ∑ k ∈ Finset.range (ℓ.1 + 1), ℓ.rungInc layer k := by
  unfold Lad.inc sourceLadderIncoherency
  rw [← Fin.sum_univ_eq_sum_range (fun k => ℓ.rungInc layer k) (ℓ.1 + 1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Lad.rungInc, j.2]

theorem Lad.sub_inc (layer : GBranch G.tree → ℕ) (ℓ : Lad G) (s m' : ℕ) (hs : s + m' ≤ ℓ.1) :
    (ℓ.sub s m').inc layer = ∑ k ∈ Finset.Ico s (s + m' + 1), ℓ.rungInc layer k := by
  rw [Finset.sum_Ico_eq_sum_range, show s + m' + 1 - s = m' + 1 by omega, Finset.sum_range]
  unfold Lad.inc sourceLadderIncoherency Lad.sub
  dsimp only
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have ht := t.2
  have hmin : (⟨min (s + (t : ℕ)) ℓ.1, by omega⟩ : Fin (ℓ.1 + 1)) = ⟨s + t, by omega⟩ :=
    Fin.ext (by simp only; omega)
  simp only [Lad.rungInc, dif_pos (show s + (t : ℕ) < ℓ.1 + 1 by omega), hmin]

end WaveTurbulence.CoarseSpliced
