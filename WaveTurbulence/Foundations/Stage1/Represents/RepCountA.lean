/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.ClassCountStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-F: the direct piece count (AMEND10, ruling R56) from CLASSCOUNT's garden count

TARGET L2251: the terms `K^eqc` are counted by gardens.  If every piece `π` has a representative layered garden
`rep π` (a Stage 1 carrier that carries a piece with the data `(ḡ, ρ̄)` of `π`, CLASSCOUNT's `HasPieceData`) and at most
`M` pieces share a representative, then the number of pieces with data `(g, r)` is at most `M` times CLASSCOUNT's garden
bound.  With `M = 3^N` (the prescriptions on the at most `N` groups of the representative's skeleton) this is the
clause of `Stage1CountsA`.
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.ClassCount

open Classical in
/-- Counting pieces through representatives with bounded fibres. -/
theorem pieceCount_of_rep (hcc : ClassCountStmt) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
      ∀ (S : Stage1Data P R) (rep : S.Pc → LayeredGarden (2 * R)) (M : ℕ),
        (∀ π, Stage1Carries P p N (rep π) ∧ HasPieceData P.d (rep π) (S.piece π).gbar (S.piece π).rbar) →
        (∀ LG, ((@univ S.Pc S.fin).filter fun π => rep π = LG).card ≤ M) →
        ∀ g r : ℕ,
          ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
            (M : ℝ) * ((C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
              P.C₂ ^ (g + r)) := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK p hp R hR N hN S rep M hrep hfib g r
  letI := S.fin
  set PS := (univ : Finset S.Pc).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r with hPS
  set A := PS.image rep with hA
  have hAc : (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
      P.C₂ ^ (g + r) := by
    refine hmain P hK p hp R hR N hN g r A fun LG hLG => ?_
    obtain ⟨π, hπ, hLGe⟩ := Finset.mem_image.1 hLG
    have hgr := (Finset.mem_filter.1 hπ).2
    obtain ⟨h1, h2⟩ := hrep π
    rw [← hLGe]
    refine ⟨h1, ?_⟩
    rw [← hgr.1, ← hgr.2]
    exact h2
  have hcard : PS.card ≤ M * A.card := by
    have := Finset.card_le_mul_card_image PS M fun LG _ => by
      refine le_trans (Finset.card_le_card ?_) (hfib LG)
      intro π hπ
      simp only [Finset.mem_filter] at hπ ⊢
      exact ⟨Finset.mem_univ _, hπ.2⟩
    simpa [hA, mul_comm] using this
  have hcardR : (PS.card : ℝ) ≤ (M : ℝ) * (A.card : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _))

end WaveTurbulence.Represents
