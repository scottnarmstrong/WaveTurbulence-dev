/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.HingeStep
/-! # Pieces of a ladder avoiding one rung (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

def Lad.TS (l : List (Lad G)) : ℕ := (l.map (fun ℓ => 2 * ℓ.1 + 2)).sum

noncomputable def Lad.IS (layer : GBranch G.tree → ℕ) (l : List (Lad G)) : ℕ :=
  (l.map (Lad.inc layer)).sum

def Lad.Pw (l : List (Lad G)) : Prop := l.Pairwise (fun ℓ ℓ' => Disjoint ℓ.atoms ℓ'.atoms)

def Lad.AllL (l : List (Lad G)) : Prop := ∀ ℓ ∈ l, ℓ.IsL

/-- The sub-ladders of a list of rung ranges. -/
def Lad.pieces (ℓ : Lad G) (ps : List (ℕ × ℕ)) : List (Lad G) := ps.map (fun p => ℓ.sub p.1 p.2)

theorem Lad.pieces_props (ℓ : Lad G) (hL : ℓ.IsL) (j : Fin (ℓ.1 + 1)) (ps : List (ℕ × ℕ))
    (hps1 : ∀ p ∈ ps, p.1 + p.2 ≤ ℓ.1 ∧ 1 ≤ p.2 ∧ ((p.1 + p.2 < (j : ℕ)) ∨ (j : ℕ) < p.1))
    (hps2 : ps.Pairwise (fun p q => p.1 + p.2 < q.1)) :
    Lad.AllL (ℓ.pieces ps) ∧ (∀ q ∈ ℓ.pieces ps, q.atoms ⊆ ℓ.atoms) ∧
    (∀ q ∈ ℓ.pieces ps, ℓ.2.1 j ∉ q.atoms ∧ ℓ.2.2 j ∉ q.atoms) ∧ Lad.Pw (ℓ.pieces ps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hL.sub p.1 p.2 (hps1 p hp).1 (hps1 p hp).2.1
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact Lad.sub_atoms_subset ℓ p.1 p.2 (hps1 p hp).1
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have hp1 := hps1 p hp
    constructor <;> intro hx <;>
    · obtain ⟨k, hk1, hk2, hk3⟩ := Lad.sub_atoms_mem ℓ p.1 p.2 hp1.1 _ hx
      refine Lad.atom_rung_ne ℓ hL k j (fun hkj => ?_) _ hk3 (by first | exact Or.inl rfl | exact Or.inr rfl)
      rw [hkj] at hk1 hk2
      omega
  · unfold Lad.pieces Lad.Pw
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hps2
    intro p q hp hq hpq
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk1, hk2, hk3⟩ := Lad.sub_atoms_mem ℓ p.1 p.2 (hps1 p hp).1 x hx
    obtain ⟨k', hk1', hk2', hk3'⟩ := Lad.sub_atoms_mem ℓ q.1 q.2 (hps1 q hq).1 x hx'
    refine Lad.atom_rung_ne ℓ hL k k' (fun hkk => ?_) x hk3 hk3'
    rw [hkk] at hk2
    omega

end WaveTurbulence.CoarseSpliced
