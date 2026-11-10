/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-!
# DH21 Lemma 6.6 (`auxlem`) and its weighted form (packet C2)

For a ternary tree `𝒯` of order `n`, let `μ_𝔫` be the number of leaves below `𝔫` and `μ°_𝔫` the
second largest of the values `μ_𝔪` over the children `𝔪` of `𝔫`. Then (DH21 Lemma 6.6, L1659–L1664)
`∏_{𝔫 ∈ 𝒩} μ°_𝔫 ≤ 3^n / (2n+1)`.

The weighted form (used in DH23 Lemma A.4 (2), L2116–L2127): with leaf weights `w_ℓ ≥ 1` and
`μ_𝔫 = ∑_{ℓ below 𝔫} w_ℓ`, `∏_{𝔫} μ°_𝔫 ≤ 3^n ∏_ℓ w_ℓ / ∑_ℓ w_ℓ` (`auxProd_mul_wsum_le`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-- The second largest of three reals. -/
def secondMax (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

end WaveTurbulence.Links
