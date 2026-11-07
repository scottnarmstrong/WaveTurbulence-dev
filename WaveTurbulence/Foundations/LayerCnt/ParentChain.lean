/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Peak

/-! # The parent-chain argument (TARGET layerlad, L1507)

Abstract form: atoms `u i, v i` (`1 ≤ i ≤ n`) each have a "parent" among their rung partner and the
two rail neighbours, with strictly smaller depth and a layer at least as large. Then no coherent stretch
of rungs has an increase followed by a decrease (`NoPeak`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt

variable {V : Type*}

/-- Every interior atom of a rung sequence has a parent among its four neighbours. -/
@[expose] def HasParents (f : V → ℕ) (depth : V → ℕ) (u v : ℕ → V) (n : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∃ y, (y = v i ∨ y = u (i - 1) ∨ y = u (i + 1)) ∧ depth y < depth (u i) ∧ f (u i) ≤ f y) ∧
    (∃ y, (y = u i ∨ y = v (i - 1) ∨ y = v (i + 1)) ∧ depth y < depth (v i) ∧ f (v i) ≤ f y)

theorem noPeak_of_parents {f : V → ℕ} {depth : V → ℕ} {u v : ℕ → V} {n : ℕ}
    (h : HasParents f depth u v n) : NoPeak (fun i => f (u i)) (fun i => f (v i)) n := by
  intro p r hp hpr hr hcoh ⟨hup, hdown⟩
  simp only at hup hdown hcoh
  -- the starting index and threshold
  obtain ⟨j, T, hjlo, hjhi, hjT, hlo, hhi⟩ : ∃ j T : ℕ, p + 1 ≤ j ∧ j ≤ r ∧ T = f (u j) ∧
      f (u p) < T ∧ f (u (r + 1)) < T := by
    by_cases hc : f (u r) ≤ f (u (p + 1))
    · exact ⟨p + 1, f (u (p + 1)), le_rfl, by omega, rfl, hup, by omega⟩
    · exact ⟨r, f (u r), by omega, le_rfl, rfl, by omega, hdown⟩
  have hvf : ∀ i, p ≤ i → i ≤ r + 1 → f (v i) = f (u i) := fun i h1 h2 => (hcoh i h1 h2).symm
  -- the core set is closed under parents
  have key : ∀ d : ℕ, ∀ x : V, depth x = d → ∀ i, p + 1 ≤ i → i ≤ r → (x = u i ∨ x = v i) → T ≤ f x → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx i hi1 hi2 hxi hTx
      obtain ⟨hpu, hpv⟩ := h i (by omega) (by omega)
      have step : ∀ y, depth y < depth x → f x ≤ f y →
          (y = u i ∨ y = v i ∨ y = u (i - 1) ∨ y = v (i - 1) ∨ y = u (i + 1) ∨ y = v (i + 1)) → False := by
        intro y hyd hxy hyc
        have hTy : T ≤ f y := le_trans hTx hxy
        rcases hyc with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ih _ (hx ▸ hyd) _ rfl i hi1 hi2 (Or.inl rfl) hTy
        · exact ih _ (hx ▸ hyd) _ rfl i hi1 hi2 (Or.inr rfl) hTy
        · by_cases hi' : i - 1 ≥ p + 1
          · exact ih _ (hx ▸ hyd) _ rfl (i - 1) hi' (by omega) (Or.inl rfl) hTy
          · have : i - 1 = p := by omega
            rw [this] at hTy; omega
        · by_cases hi' : i - 1 ≥ p + 1
          · exact ih _ (hx ▸ hyd) _ rfl (i - 1) hi' (by omega) (Or.inr rfl) hTy
          · have : i - 1 = p := by omega
            rw [this, hvf p le_rfl (by omega)] at hTy; omega
        · by_cases hi' : i + 1 ≤ r
          · exact ih _ (hx ▸ hyd) _ rfl (i + 1) (by omega) hi' (Or.inl rfl) hTy
          · have : i + 1 = r + 1 := by omega
            rw [this] at hTy
            omega
        · by_cases hi' : i + 1 ≤ r
          · exact ih _ (hx ▸ hyd) _ rfl (i + 1) (by omega) hi' (Or.inr rfl) hTy
          · have : i + 1 = r + 1 := by omega
            rw [this] at hTy
            have := hvf (r + 1) (by omega) le_rfl
            omega
      rcases hxi with rfl | rfl
      · obtain ⟨y, hy, hyd, hyf⟩ := hpu
        exact step y hyd hyf (by tauto)
      · obtain ⟨y, hy, hyd, hyf⟩ := hpv
        exact step y hyd hyf (by tauto)
  exact key _ (u j) rfl j hjlo hjhi (Or.inl rfl) (le_of_eq hjT)

end WaveTurbulence.LayerCnt
