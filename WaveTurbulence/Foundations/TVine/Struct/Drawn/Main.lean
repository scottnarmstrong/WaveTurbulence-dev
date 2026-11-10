/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Templates
public import WaveTurbulence.Foundations.TVine.Core.Bridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.NamedInputs
public import WaveTurbulence.Foundations.TVine.Struct.Statement

/-!
# N2 Lemma 5.2: every drawn vine (III)–(VIII) is a T-vine (packet L3D)

`research-gamma-half-2/NOTES.md` L828–L837 (REFEREED, REF2: "Lemma 5.2 holds for every orientation up to 21 atoms";
"Lemma 1.9(2) must be applied undirected"): "Every expansion T_X(k⃗) of the B2 templates X = III–VIII is a T-vine."

* `isTVineU_of_isVineXU` (U layer): a B2 vine of type `X ∉ {I, II}`, read undirected (L1's `IsVineXU`), is a T-vine.
  Its bond multiset is carried by an injective map onto the expanded template `T_X(k⃗)` on `range n`; that multigraph
  is a T-vine with joints `0, 1` (`expand_X_tvine`), hence with joints `1, 0` (`isTVineU_swap`); and T-vines are closed
  under isomorphism (`isTVineU_of_iso`).
* **`drawnTVine : GammaLow.FinalCount.DrawnTVineInput`** (molecule level, through L1's bridge `isVine_iff`,
  `isTVine_iff`), and the same statement as L3's `Struct.DrawnTVineStatement` (`drawnTVineStatement`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

universe u v

section swap

variable {V : Type*} [DecidableEq V]

/-- The closure does not depend on the order of the joints. -/
theorem isClosureU_swap {G C : UMultigraph V} {j₁ j₂ : V} (h : IsClosureU G j₁ j₂ C) : IsClosureU G j₂ j₁ C := by
  obtain ⟨hσ, hV, hl, added, hdata, hm⟩ := h
  have hs : G.mult s(j₂, j₁) = G.mult s(j₁, j₂) := by rw [Sym2.eq_swap]
  refine ⟨by rw [hs]; exact hσ, by rw [hV]; exact Finset.erase_right_comm, hl, added, ?_, fun e => ?_⟩
  · rcases hdata with ⟨h0, a, b, c, d, h1, h2, rfl⟩ | ⟨h1', x, y, h1, h2, rfl⟩
    · exact Or.inl ⟨by rw [hs]; exact h0, c, d, a, b, h2, h1, Multiset.pair_comm _ _⟩
    · exact Or.inr ⟨by rw [hs]; exact h1', y, x, h2, h1, by rw [Sym2.eq_swap]⟩
  · rw [hm e]; congr 1; exact if_congr or_comm rfl rfl

/-- T-vines do not depend on the order of the joints. -/
theorem isTVineU_swap {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) : IsTVineU G j₂ j₁ := by
  obtain ⟨hB, hm, C, hC, hRT⟩ := h
  exact ⟨hB.swap, hm, C, isClosureU_swap hC, hRT⟩

end swap

/-- Every expansion of a template (III)–(VIII) is a T-vine with joints `0, 1`. -/
theorem expand_tvine_drawn (X : VineType) (hX1 : X ≠ .I) (hX2 : X ≠ .II) (Ks : List ℕ)
    (hK : Ks.length = X.template.slots.length) :
    IsTVineU (ofMS (Finset.range (X.expand Ks).n) (tmplMS (X.expand Ks))) 0 1 := by
  cases X with
  | I => exact absurd rfl hX1
  | II => exact absurd rfl hX2
  | III => exact expand_III_tvine Ks hK
  | IV => exact expand_IV_tvine Ks hK
  | V => exact expand_V_tvine Ks hK
  | VI => exact expand_VI_tvine Ks hK
  | VII => exact expand_VII_tvine Ks hK
  | VIII => exact expand_VIII_tvine Ks hK

/-- **N2 Lemma 5.2, undirected.** A B2 vine of type `X ∉ {I, II}` (L1's `IsVineXU`) is a T-vine. -/
theorem isTVineU_of_isVineXU {V : Type*} [DecidableEq V] {X : VineType} {G : UMultigraph V} {j₁ j₂ : V}
    (hX1 : X ≠ .I) (hX2 : X ≠ .II) (h : IsVineXU X G j₁ j₂) : IsTVineU G j₁ j₂ := by
  obtain ⟨hB, k, hk, f, hinj, himg, hj, hbm⟩ := h
  have hH := expand_tvine_drawn X hX1 hX2 k hk
  have hbm' : (bondMultiset G).map (Sym2.map f) = tmplMS (X.expand k) := hbm
  have hGs : ∀ e ∈ bondMultiset G, e ∈ G.verts.sym2 := fun e he =>
    mem_sym2_of_mult (by rw [← count_bondMultiset]; exact Multiset.count_ne_zero.mpr he)
  have hwf : WF (Finset.range (X.expand k).n) (tmplMS (X.expand k)) := by
    intro e he
    rw [← hbm'] at he
    obtain ⟨e', he', rfl⟩ := Multiset.mem_map.mp he
    rw [Finset.mem_sym2_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
    rw [← himg]
    exact Finset.mem_image_of_mem f (Finset.mem_sym2_iff.mp (hGs e' he') y hy)
  have : Nonempty V := ⟨j₁⟩
  have hlinv : LInv G.verts f (Function.invFunOn f (G.verts : Set V)) := fun w hw =>
    hinj.leftInvOn_invFunOn hw
  have hmult : ∀ a ∈ G.verts, ∀ b ∈ G.verts,
      (ofMS (Finset.range (X.expand k).n) (tmplMS (X.expand k))).mult s(f a, f b) = G.mult s(a, b) := by
    intro a ha b hb
    rw [ofMS_mult_of_wf hwf, ← hbm', count_map_of_injOn hlinv hGs ha hb, count_bondMultiset]
  have hj' : (f j₁ = 0 ∧ f j₂ = 1) ∨ (f j₁ = 1 ∧ f j₂ = 0) := by
    have h0 : (0 : ℕ) ∈ ({f j₁, f j₂} : Finset ℕ) := by rw [hj]; simp
    have h1 : (1 : ℕ) ∈ ({f j₁, f j₂} : Finset ℕ) := by rw [hj]; simp
    have ha : f j₁ ∈ ({0, 1} : Finset ℕ) := by rw [← hj]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 ha
    omega
  apply isTVineU_of_iso hinj himg hmult hB
  rcases hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hH
  · rw [h1, h2]; exact isTVineU_swap hH

/-- **N2 Lemma 5.2 (`𝒱_{>1/2} ⊂ 𝒱_{≤1/2}`)**, exactly L6's named input `DrawnTVineInput`: every expansion of a drawn
template (III)–(VIII) is a T-vine. -/
theorem drawnTVine : GammaLow.FinalCount.DrawnTVineInput.{u, v} := by
  intro V D _ _ _ M X S a b hX1 hX2 h
  rw [isVine_iff M X] at h
  rw [isTVine_iff M]
  exact ⟨h.1, isTVineU_of_isVineXU hX1 hX2 h.2⟩

end WaveTurbulence.TVine.Struct.Drawn
