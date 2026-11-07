/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PosSingle
import Mathlib.Tactic

/-! # Decidable base checks for the rail-position cuts (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

theorem posσ_zero (n j c₀ c₁ : ℕ) (τ : ℕ → ℕ) : posσ n 0 j c₀ c₁ τ = τ := by
  funext v; unfold posσ
  by_cases h : v < n ∨ n + 2 * 0 ≤ v
  · rw [if_pos h]
  · exfalso; apply h; omega

/-- The slot members of distinct slots are distinct. -/
@[expose] def SlotsDistinct (T : VineTemplate) : Prop :=
  T.slots.Pairwise (fun s s' => s.1 ≠ s'.1 ∧ s.1 ≠ s'.2 ∧ s.2 ≠ s'.1 ∧ s.2 ≠ s'.2)

instance (T : VineTemplate) : Decidable (SlotsDistinct T) := by unfold SlotsDistinct; infer_instance

theorem slotsDistinct (X : VineType) : SlotsDistinct X.template := by
  cases X <;> decide +kernel

theorem slotsDistinct_getElem {T : VineTemplate} (h : SlotsDistinct T) {j j' : ℕ} (hj : j < T.slots.length)
    (hj' : j' < T.slots.length) (hne : j ≠ j') :
    (T.slots[j]).1 ≠ (T.slots[j']).1 ∧ (T.slots[j]).1 ≠ (T.slots[j']).2 ∧
      (T.slots[j]).2 ≠ (T.slots[j']).1 ∧ (T.slots[j]).2 ≠ (T.slots[j']).2 := by
  have hp := List.pairwise_iff_getElem.mp h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hp j j' hj hj' hlt
  · have := hp j' j hj' hj hgt
    exact ⟨fun e => this.1 e.symm, fun e => this.2.2.1 e.symm, fun e => this.2.1 e.symm,
      fun e => this.2.2.2 e.symm⟩

/-- Local part of the base check for the position cut of slot `c` with the label set `K0`. -/
@[expose] def PosA (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (K0 : List ℕ) : Prop :=
  (∀ v ∈ K0, 2 ≤ v ∧ v < T.n) ∧ (∀ e ∈ T.bonds, e ≠ s.1 → e ≠ s.2 → ¬ Crosses (kap K0) e) ∧
    (kap K0 s.1.1 = kap K0 s.2.1) ∧ (kap K0 s.1.2 = kap K0 s.2.2) ∧ (kap K0 s.1.1 ≠ kap K0 s.1.2)

/-- Compatibility part of the base check. -/
@[expose] def PosB (T : VineTemplate) (c : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) (K0 : List ℕ) : Prop :=
  (∀ j' < T.slots.length, j' ≠ c → Sides2 (kap K0) (slotEnds (T.slots.getD j' ((0, 0), (0, 0))))) ∧
    s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2 ∧ s(s.1.1, s.1.2) ≠ s(s.2.1, s.2.2) ∧ SymSingle T s.1 ∧ SymSingle T s.2 ∧
      s.1 ∈ T.bonds ∧ s.2 ∈ T.bonds

instance (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (K0 : List ℕ) : Decidable (PosA T s K0) := by
  unfold PosA; infer_instance
instance (T : VineTemplate) (c : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) (K0 : List ℕ) : Decidable (PosB T c s K0) := by
  unfold PosB; infer_instance


theorem posσ_le {n k j c₀ c₁ : ℕ} {τ : ℕ → ℕ} (h0 : c₀ ≤ 2) (h1 : c₁ ≤ 2) (hτ : ∀ v, τ v ≤ 2) (v : ℕ) :
    posσ n k j c₀ c₁ τ v ≤ 2 := by
  unfold posσ
  by_cases h : v < n ∨ n + 2 * k ≤ v
  · rw [if_pos h]; exact hτ v
  · rw [if_neg h]; dsimp only; split_ifs <;> omega

/-- Orient a crossing edge so that the end labelled `2` (inside `K`) comes first. -/
@[expose] def orientE (c₁ : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := if c₁ = 2 then (e.2, e.1) else e

theorem orientE_class (c₁ : ℕ) (e : ℕ × ℕ) : s((orientE c₁ e).1, (orientE c₁ e).2) = s(e.1, e.2) := by
  unfold orientE; split_ifs
  · exact Sym2.eq_swap
  · rfl

end WaveTurbulence.LayerCnt
