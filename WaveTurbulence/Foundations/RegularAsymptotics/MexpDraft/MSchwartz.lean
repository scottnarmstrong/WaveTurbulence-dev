/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.Prop78
public import WaveTurbulence.Foundations.Cancel.CollisionLin

/-!
# The momentum factors of classes with `Z = ∅` are Schwartz functions, built from collision terms

For a class with `|Z| = 0` every chain factor is a resonant integral (`𝙸 = 0`), and

* type 1: `ℳ*_X = 𝒦₀(ℳ*_{X₁}, ℳ*_{X₂}, ℳ*_{X₃})` (DH21 (inductm1)/(inductm5));
* a chain tuple `(0, 𝚌, X₁, X₂)` in front of `S`: `ℳ*_{(j)} ℳ*_S = 𝒦_𝚌` with `ℳ*_S` in the slot `𝚌` evaluated at
  `k` (DH21 (inductm2)–(inductm4), (inductm7)–(inductm9)).

`MS hd F X` is this recursion with the landed Schwartz-valued collision terms (`collisionTermSchwartz`), and
`MS_eq`: `⇑(MS hd F X) = Mshape F X` for `|Z| = 0`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped SchwartzMap

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel WaveTurbulence.WKE

variable {d : ℕ}

/-- The chain factor of `𝚌 - 1 = c` times `g`, as the collision term `𝒦_𝚌` (`g` in the slot `𝚌`). -/
noncomputable def CT (hd : 2 ≤ d) (c : Fin 3) (a b g : 𝓢(Mom d, ℝ)) : 𝓢(Mom d, ℝ) :=
  if c = 0 then collisionTermSchwartz hd 1 g a b
  else if c = 1 then collisionTermSchwartz hd 2 a g b
  else collisionTermSchwartz hd 3 a b g

mutual
/-- **`ℳ*_X` as a Schwartz function** (classes with `|Z| = 0`; the bits are ignored). -/
noncomputable def MS (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) : Shape → 𝓢(Mom d, ℝ)
  | .triv => F
  | .type1 X₁ X₂ X₃ => collisionTermSchwartz hd 0 (MS hd F X₁) (MS hd F X₂) (MS hd F X₃)
  | .type2 L Y => MT hd F L (MS hd F Y)

/-- The chain factors of a tuple list applied to `g`. -/
noncomputable def MT (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) : Tuples → 𝓢(Mom d, ℝ) → 𝓢(Mom d, ℝ)
  | .nil, g => g
  | .cons _ c X₁ X₂ rest, g => CT hd c (MS hd F X₁) (MS hd F X₂) (MT hd F rest g)
end

theorem MS_consShape (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) (I : Bool) (c : Fin 3) (X₁ X₂ S : Shape) :
    MS hd F (consShape I c X₁ X₂ S) = CT hd c (MS hd F X₁) (MS hd F X₂) (MS hd F S) := by
  cases S <;> rfl

theorem resIntegral_eq_deltaInt (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    resIntegral Ψ k = deltaInt (fun ℓ x => Ψ (k + ℓ) (k + ℓ + x) (k + x)) := rfl

/-- **A chain factor times `g` is a collision term.** -/
theorem npair_mul (hd : 2 ≤ d) (c : Fin 3) (a b g : 𝓢(Mom d, ℝ)) (k : Mom d) :
    Npair false c a b k * g k = CT hd c a b g k := by
  simp only [Npair, Bool.false_eq_true, ↓reduceIte, resIntegral_eq_deltaInt, CT]
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, coe_collisionTermSchwartz, collisionTerm, redSlot,
      greenSlot]
    rw [mul_comm, ← deltaInt_smul]
    congr 1; funext ℓ x
    simp [collisionKernel]; ring
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, coe_collisionTermSchwartz, collisionTerm,
      redSlot, greenSlot]
    rw [mul_comm, ← deltaInt_smul]
    congr 1; funext ℓ x
    simp [collisionKernel]; ring
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, coe_collisionTermSchwartz,
      collisionTerm, redSlot, greenSlot]
    rw [mul_comm, ← deltaInt_smul]
    congr 1; funext ℓ x
    simp [collisionKernel]; ring

theorem Tuples.zcount_cons_eq_zero {I : Bool} {c : Fin 3} {X₁ X₂ : Shape} {rest : Tuples}
    (h : (Tuples.cons I c X₁ X₂ rest).zcount = 0) :
    I = false ∧ X₁.zcount = 0 ∧ X₂.zcount = 0 ∧ rest.zcount = 0 := by
  simp only [Tuples.zcount] at h
  cases I <;> simp_all

mutual
/-- **`ℳ*_X = MS X` for classes with `|Z| = 0`.** -/
theorem MS_eq (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) : (X : Shape) → X.zcount = 0 →
    ⇑(MS hd F X) = Mshape F X
  | .triv, _ => rfl
  | .type1 X₁ X₂ X₃, h => by
    simp only [Shape.zcount, Nat.add_eq_zero_iff] at h
    funext k
    simp only [MS, coe_collisionTermSchwartz, collisionTerm, Mshape, resIntegral_eq_deltaInt,
      MS_eq hd F X₁ h.1.1, MS_eq hd F X₂ h.1.2, MS_eq hd F X₃ h.2]
    rfl
  | .type2 L Y, h => by
    simp only [Shape.zcount, Nat.add_eq_zero_iff] at h
    funext k
    rw [MS, MT_eq hd F L h.1, MS_eq hd F Y h.2]
    rfl

theorem MT_eq (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) : (L : Tuples) → L.zcount = 0 → (g : 𝓢(Mom d, ℝ)) →
    (k : Mom d) → MT hd F L g k = g k * Mtuples F L k
  | .nil, _, g, k => by simp [MT, Mtuples]
  | .cons I c X₁ X₂ rest, h, g, k => by
    obtain ⟨rfl, h₁, h₂, hr⟩ := Tuples.zcount_cons_eq_zero h
    rw [MT, ← npair_mul hd, MT_eq hd F rest hr, MS_eq hd F X₁ h₁, MS_eq hd F X₂ h₂]
    simp only [Mtuples]
    ring
end

/-- `ℳ*` of a class with a chain tuple in front. -/
theorem mshape_consShape (F : Mom d → ℝ) (I : Bool) (c : Fin 3) (X₁ X₂ S : Shape) (k : Mom d) :
    Mshape F (consShape I c X₁ X₂ S) k = Npair I c (Mshape F X₁) (Mshape F X₂) k * Mshape F S k := by
  cases S <;> simp [consShape, Mshape, Mtuples] <;> ring

end WaveTurbulence.Mexp
