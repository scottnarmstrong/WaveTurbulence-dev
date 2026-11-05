/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! The input-leaf parametrization underlying the uniform kernel majorant.
Proof extracted from the literal snapshot-7 summability proof; original unchanged. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set

/-- Input leaf labels determine a decoration when each tree has at most one lone leaf. -/
theorem genDecoration_input_injective {w d : ℕ} (LG : LayeredGarden w)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) :
    Function.Injective (fun (κ : GenDecoration LG.garden d nroot nfl)
      (ℓ : {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}) => κ.1 ℓ.1.toNode) := by
  classical
  have hlone' : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsLone ℓ → LG.garden.IsLone ℓ' →
      ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ' := fun ℓ ℓ' h h' hj =>
    Finset.card_le_one.1 (hlone ℓ.1.1) ℓ (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, h⟩) ℓ'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.symm, h'⟩)
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let Φ : GenDecoration LG.garden d nroot nfl → (ι → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.1.toNode
  -- the decoration is determined by its input-leaf values

  intro κ κ' hκ
  let δ : GNode LG.garden.tree → (Fin d → ℤ) := fun a => κ.1 a - κ'.1 a
  have hδb : ∀ b : GBranch LG.garden.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2) := by
    intro b
    simp only [δ, κ.2.1.1 b, κ'.2.1.1 b]
    abel
  have hin : ∀ ℓ ∈ inputLeaves LG.garden, δ ℓ.toNode = 0 := fun ℓ hℓ => by
    have := congrFun hκ ⟨ℓ, hℓ⟩
    simp only [Φ] at this
    simp [δ, this]
  have hleaf : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsLone ℓ → δ ℓ.toNode = 0 := by
    intro ℓ hnl
    by_cases hm : LG.garden.mark ℓ = none
    · by_cases hs : LG.garden.sign ℓ.toNode = 1
      · exact hin ℓ (by simp [inputLeaves, hs, hm])
      · -- a minus leaf: use its (plus) partner
        have hne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
        have hs' : LG.garden.sign ℓ.toNode = -1 := by
          rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with h | h
          · exact absurd h hs
          · exact h
        have hpm : LG.garden.mark (LG.garden.pair ℓ) = none := by
          by_contra h
          have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 h
          rw [LG.garden.pair_pair] at this
          exact hne this.symm
        have hps : LG.garden.sign (LG.garden.pair ℓ).toNode = 1 := by
          have := LG.garden.pair_sign ℓ hne
          change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = -nodeSign LG.garden.sig ℓ.1 at this
          change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
          rw [this]
          change -LG.garden.sign ℓ.toNode = 1
          rw [hs']
          rfl
        have h0 := hin (LG.garden.pair ℓ) (by simp [inputLeaves, hps, hpm])
        simp only [δ] at h0 ⊢
        rw [κ.2.1.2 ℓ, κ'.2.1.2 ℓ]
        exact h0
    · -- a marked leaf that is not lone is a flower
      have hfl : LG.garden.IsFlower ℓ := by
        rcases hmk : LG.garden.mark ℓ with _ | tag
        · exact absurd hmk hm
        · cases tag
          · exact absurd hmk hnl
          · exact hmk
      simp [δ, κ.2.2.2 ℓ hfl, κ'.2.2.2 ℓ hfl]
  have hroot : ∀ j, δ (GNode.root LG.garden.tree j) = 0 := fun j => by
    simp [δ, κ.2.2.1 j, κ'.2.2.1 j]
  apply Subtype.ext
  funext a
  exact sub_eq_zero.1
    (eq_zero_of_roots_leaves_zero δ hδb LG.garden.IsLone hlone' hroot hleaf a)

end WaveTurbulence.LGSpine
