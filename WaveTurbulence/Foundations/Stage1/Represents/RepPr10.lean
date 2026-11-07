/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr6
public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts3
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `Sound` of the successor piece of a prescribed point of a `Stage1Carries` garden

`normalizedPiece_sound`: the hypotheses of `stage1Piece_sound_succ_uncond` (prime, irreducible, balanced, `1 ≤ n_sk`) are discharged by
SKEL-FACTS (`skelFacts_of_carries`), the order bound by `decoded_order`, the layer bound by canonicity.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton

theorem normalizedPiece_sound (P : WTParams) {R : ℕ} (hR : 1 ≤ R) {p N : ℕ}
    (b : PrescribedPrimeGarden (2 * R)) (hc : Stage1Carries P p N b.layered)
    (hNb : N ≤ P.N (p + 1) ^ 4) (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1Piece.Sound (P := P) (b.normalizedPiece P.d) p base roots := by
  obtain ⟨hI, hbal, hn⟩ := skelFacts_of_carries P p N hR hc b.prime
  have hsz := b.prime.data.decoded_order b.prime.prime.1 b.prime.decodes
  have hord : b.layered.garden.order = N := hc.2.2.1
  refine stage1Piece_sound_succ_uncond P b.prime.prime.1 b.layered b.prime.decodes b.totalSigma b.prime.prime hI hbal hn p
    (by omega) (fun v => ?_) hL base roots
  exact Canon.layer_le_of_isCanonGC hc.1 _
end WaveTurbulence.Represents
