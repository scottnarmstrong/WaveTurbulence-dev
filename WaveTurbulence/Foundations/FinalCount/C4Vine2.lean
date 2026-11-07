/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Vine1
import Mathlib.Tactic

/-! # Prop 9.6, case (4): the ladder `Z_m(Q)` minus the bond of one chain is a half-closed vine (II)

`N₁` is the ladder `Z_m(Q)` (the closure `𝕄₁` of `𝕄₀`), `K = N₁` with the bond `(c,d)` of one chain removed. Since `𝕄₀` has
no triple bond, the pair `(c,d)` of the removed chain is an end rung of the ladder; after reversing the ladder it is the
last rung, and `K` is the half-ladder: a half-closure of vine (II).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem zbb_half (m : ℕ) (x y : Bool × ℕ) (hx : x.2 ≤ m) (hy : y.2 ≤ m) :
    lBB x y + (if x.2 = m ∧ y.2 = m ∧ x.1 ≠ y.1 then 1 else 0) = zBB m x y := by
  unfold lBB zBB
  cases hxa : x.1 <;> cases hya : y.1 <;> simp [hxa, hya] <;> split_ifs <;> omega

section
variable {V : Type u} {D₁ : Type v} {D₂ : Type v} [DecidableEq V] [Fintype D₁] [DecidableEq D₁] [Fintype D₂]
  [DecidableEq D₂]

/-- **A `Z_m(Q)` ladder minus the bond of the chain `(c,d)` is a half-closed vine (II)**, when the other chain `(c',d')`
cannot carry more than the second end rung. -/
theorem halfClosure_of_zq {N₁ : Molecule V D₁} {K : Molecule V D₂} {m : ℕ} {φ : Bool × ℕ → V} {c d c' d' : V}
    (hZ : IsZQ N₁ m φ) (hat : K.atoms = N₁.atoms) (hcd : c ∈ N₁.atoms ∧ d ∈ N₁.atoms ∧ c ≠ d)
    (hbbK : ∀ p q, N₁.bondsBetween p q = K.bondsBetween p q + (if s(c, d) = s(p, q) then 1 else 0))
    (hle : ∀ p q, N₁.bondsBetween p q ≤ 2 + (if s(c, d) = s(p, q) then 1 else 0) +
      (if s(c', d') = s(p, q) then 1 else 0)) :
    IsVineIIHalfClosure K := by
  classical
  -- the pair `(c, d)` is an end rung
  have hend : ∃ ψ : Bool × ℕ → V, IsZQ N₁ m ψ ∧ s(c, d) = s(ψ (false, m), ψ (true, m)) := by
    by_cases hm : m = 0
    · subst hm
      obtain ⟨xc, hxc, hxc'⟩ := (hZ.atoms c).mp hcd.1
      obtain ⟨xd, hxd, hxd'⟩ := (hZ.atoms d).mp hcd.2.1
      have e1 : xc = (xc.1, 0) := Prod.ext rfl (by omega)
      have e2 : xd = (xd.1, 0) := Prod.ext rfl (by omega)
      have hne : xc.1 ≠ xd.1 := by
        intro h; apply hcd.2.2; rw [← hxc', ← hxd', e1, e2, h]
      refine ⟨φ, hZ, ?_⟩
      have hb : ∀ a b : Bool, a ≠ b → (a = false ∧ b = true) ∨ (a = true ∧ b = false) := by
        intro a b; cases a <;> cases b <;> simp
      rcases hb _ _ hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← hxc', ← hxd', e1, e2, h1, h2]
      · rw [← hxc', ← hxd', e1, e2, h1, h2, Sym2.eq_swap]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hne0 : s(φ (false, 0), φ (true, 0)) ≠ s(φ (false, m), φ (true, m)) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this; omega
        · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this
      have h3 : ∀ j, j ≤ m → (j = 0 ∨ j = m) → N₁.bondsBetween (φ (false, j)) (φ (true, j)) = 3 := by
        intro j hj hj'
        rw [hZ.bb _ _ (by simpa using hj) (by simpa using hj)]
        simp [zBB, hm, hj']
      have hR : ∀ j, j ≤ m → (j = 0 ∨ j = m) → s(c, d) ≠ s(φ (false, j), φ (true, j)) →
          s(c', d') = s(φ (false, j), φ (true, j)) := by
        intro j hj hj' hne
        have := hle (φ (false, j)) (φ (true, j))
        rw [h3 j hj hj', if_neg hne] at this
        by_contra hne'
        rw [if_neg hne'] at this
        omega
      by_cases h0 : s(c, d) = s(φ (false, 0), φ (true, 0))
      · refine ⟨zrev m φ, hZ.rev, ?_⟩
        simpa [zrev] using h0
      · by_cases h1 : s(c, d) = s(φ (false, m), φ (true, m))
        · exact ⟨φ, hZ, h1⟩
        · exact absurd ((hR 0 (Nat.zero_le _) (Or.inl rfl) h0).symm.trans (hR m le_rfl (Or.inr rfl) h1)) hne0
  obtain ⟨ψ, hψ, hψcd⟩ := hend
  refine isVineHalf_of_ladder hψ.inj (fun w => by rw [hat]; exact hψ.atoms w) ?_
  intro x y hx hy
  have h1 := hbbK (ψ x) (ψ y)
  rw [hψ.bb x y hx hy] at h1
  have h2 := zbb_half m x y hx hy
  have hind : (s(c, d) = s(ψ x, ψ y)) ↔ (x.2 = m ∧ y.2 = m ∧ x.1 ≠ y.1) := by
    rw [hψcd]
    constructor
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have a1 := hψ.inj _ _ (by simp) hx e1
        have a2 := hψ.inj _ _ (by simp) hy e2
        rw [← a1, ← a2]; simp
      · have a1 := hψ.inj _ _ (by simp) hy e1
        have a2 := hψ.inj _ _ (by simp) hx e2
        rw [← a1, ← a2]; simp
    · rintro ⟨e1, e2, e3⟩
      obtain ⟨a, i⟩ := x; obtain ⟨b, j⟩ := y
      simp only at e1 e2 e3
      subst e1 e2
      cases a <;> cases b <;> simp_all [Sym2.eq_swap]
  rw [if_congr hind rfl rfl] at h1
  omega

end
end WaveTurbulence.FinalCountG8
