/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ClassCount
public import WaveTurbulence.Foundations.Spine.FinalArith
/-! # The ladder decay gate (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Sumint Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma card_ladderAtoms : (Molecule.ladderAtoms u v).card = 2 * n + 4 := by
  classical
  unfold Molecule.ladderAtoms
  have hd : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
    exact C.hne _ _ hj.symm
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ C.huinj,
    Finset.card_image_of_injective _ C.hvinj]
  simp; ring

include C in
/-- The incoherency counts the end rungs and the interior rungs on different layers. -/
lemma incoh_le (layer : GBranch G.tree → ℕ) :
    sourceLadderIncoherency G layer u v ≤
      (Finset.univ.filter (fun k : Fin n => layer (u (LadderDarts.ir k)) ≠ layer (v (LadderDarts.ir k)))).card + 2 := by
  classical
  unfold sourceLadderIncoherency
  set f : Fin (n + 1 + 1) → ℕ := fun j => if layer (u j) = layer (v j) then 0 else 1 with hf
  have hsub : (Finset.univ : Finset (Fin (n + 1 + 1))) ⊆
      ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))) ∪
        (Finset.univ.image (LadderDarts.ir (n := n))) := by
    intro j _
    by_cases h0 : j = 0
    · simp [h0]
    · by_cases h1 : j = Fin.last (n + 1)
      · simp [h1]
      · apply Finset.mem_union_right
        have hj0 : j.1 ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have hj1 : j.1 ≠ n + 1 := fun h => h1 (Fin.ext (by simp [h]))
        have hjn := j.2
        refine Finset.mem_image.mpr ⟨⟨j.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [LadderDarts.ir]
        omega
  calc ∑ j : Fin (n + 1 + 1), f j ≤ ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))) ∪
        (Finset.univ.image (LadderDarts.ir (n := n))), f j :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), f j +
        ∑ j ∈ (Finset.univ.image (LadderDarts.ir (n := n))), f j := (by have := Finset.sum_union_inter (s₁ := ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1)))) (s₂ := (Finset.univ.image (LadderDarts.ir (n := n)))) (f := f); omega)
    _ ≤ 2 + (Finset.univ.filter (fun k : Fin n => layer (u (LadderDarts.ir k)) ≠ layer (v (LadderDarts.ir k)))).card := by
        refine add_le_add ?_ ?_
        · calc ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), f j ≤
              ∑ _j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), 1 := Finset.sum_le_sum (fun j _ => by
                simp only [hf]; split_ifs <;> simp)
            _ ≤ 2 := by simpa using Finset.card_le_two (a := (0 : Fin (n + 1 + 1))) (b := Fin.last (n + 1))
        · rw [Finset.sum_image (fun a _ b _ h => C.ir_injective h)]
          rw [Finset.card_filter]
          exact le_of_eq (Finset.sum_congr rfl (fun k _ => by simp only [hf]; split_ifs <;> simp_all))
    _ = _ := by ring

end LadderDarts.Ctx

end WaveTurbulence.LadderDecay
