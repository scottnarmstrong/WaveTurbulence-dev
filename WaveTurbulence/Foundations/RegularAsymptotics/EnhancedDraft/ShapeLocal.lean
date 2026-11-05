/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Enhanced

/-!
# Shapes only see `Z` on the special candidates (packet C5, reading R1)

DH21 Def 4.18 compares the sub-objects `(𝒬_j, Z_j)` with `Z_j = Z ∩ 𝒩_j^ch`. `cplShape` evaluates
the global `Z` at the sub-objects' own nodes; `cplShape_congr` shows that the shape of a dominant
code only depends on `Z` through its special candidates, so `(𝒬_j, Z)` and `(𝒬_j, Z_j)` have the same
shape (`cplShape_inter`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

mutual
theorem cplShape_congr {Z Z' : Finset (Fin w × Path)} : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → (∀ z ∈ cplSpecial Q a b, z ∈ Z ↔ z ∈ Z') →
    cplShape Z Q a b = cplShape Z' Q a b
  | .triv, _, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b, hz => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplSpecial, List.mem_append] at hz
    simp only [cplShape]
    rw [cplShape_congr Q₁ h.1.1 _ _ fun z hz' => hz z (Or.inl (Or.inl hz')),
      cplShape_congr Q₂ h.1.2 _ _ fun z hz' => hz z (Or.inl (Or.inr hz')),
      cplShape_congr Q₃ h.2 _ _ fun z hz' => hz z (Or.inr hz')]
  | .type2 Xp Xm Qlp, h, a, b, hz => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplSpecial, List.mem_append] at hz
    simp only [cplShape]
    rw [chainTuples_congr Xp h.1.1 _ _ fun z hz' => hz z (Or.inl (Or.inl hz')),
      chainTuples_congr Xm h.1.2 _ _ fun z hz' => hz z (Or.inl (Or.inr hz')),
      cplShape_congr Qlp h.2 _ _ fun z hz' => hz z (Or.inr hz')]

theorem chainTuples_congr {Z Z' : Finset (Fin w × Path)} : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) → (∀ z ∈ chainSpecial X ζ a, z ∈ Z ↔ z ∈ Z') →
    chainTuples Z X ζ a = chainTuples Z' X ζ a
  | .nil, _, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a, hz => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    simp only [chainSpecial, RegChain.isNil, ↓reduceIte, List.mem_append, List.mem_singleton,
      chainSpecial, List.not_mem_nil, or_false] at hz
    have ha : decide (a ∈ Z) = decide (a ∈ Z') := by
      exact decide_eq_decide.mpr (hz a (Or.inl rfl))
    have eR : (if slotSign ζ m.red.1 = 1 then
        cplShape Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplShape Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])) = (if slotSign ζ m.red.1 = 1 then
        cplShape Z' Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplShape Z' Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])) := by
      have hz' : ∀ z ∈ (if slotSign ζ m.red.1 = 1 then
          cplSpecial Qr (addrExt a [m.red.1])
            (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        else cplSpecial Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
          (addrExt a [m.red.1])), z ∈ Z ↔ z ∈ Z' :=
        fun z h => hz z (Or.inr (Or.inl (Or.inl h)))
      split_ifs at hz' ⊢ <;> exact cplShape_congr Qr hr _ _ hz'
    have eG : (if slotSign ζ m.green.1 = 1 then
        cplShape Z Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplShape Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])) = (if slotSign ζ m.green.1 = 1 then
        cplShape Z' Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplShape Z' Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])) := by
      have hz' : ∀ z ∈ (if slotSign ζ m.green.1 = 1 then
          cplSpecial Qg (addrExt a [m.green.1])
            (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        else cplSpecial Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
          (addrExt a [m.green.1])), z ∈ Z ↔ z ∈ Z' :=
        fun z h => hz z (Or.inr (Or.inl (Or.inr h)))
      split_ifs at hz' ⊢ <;> exact cplShape_congr Qg hg _ _ hz'
    simp only [chainTuples]
    rw [ha, eR, eG, chainTuples_congr rest hs _ _ fun z h => hz z (Or.inr (Or.inr h))]
end

/-- **`(𝒬, Z)` and `(𝒬, Z ∩ 𝒩^ch_special)` have the same shape** (reading R1). -/
theorem cplShape_inter (Z : Finset (Fin w × Path)) (Q : RegCpl) (h : Q.dominant = true)
    (a b : Fin w × Path) :
    cplShape Z Q a b = cplShape (Z ∩ (cplSpecial Q a b).toFinset) Q a b :=
  cplShape_congr Q h a b fun z hz => by simp [hz]

end WaveTurbulence.Links
