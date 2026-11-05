/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftGenDecorationEquiv
/-! Reindex decoration sums without choosing or quotienting any ordered top trees. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem tsum_graftGenDecoration {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (f : GenDecoration (markedGardenGraft sig top P low hsig) d n nfl → ℂ) :
    (∑' κ, f κ) = ∑' x : BoundaryDecorationData top P low d n nfl,
      f (assembleGenDecoration sig top P low hsig n nfl x) :=
  ((graftGenDecorationEquiv sig top P low hsig n nfl).symm.tsum_eq f).symm

theorem summable_assembleGenDecoration_iff {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (f : GenDecoration (markedGardenGraft sig top P low hsig) d n nfl → ℂ) :
    Summable (fun x : BoundaryDecorationData top P low d n nfl =>
      f (assembleGenDecoration sig top P low hsig n nfl x)) ↔ Summable f :=
  (graftGenDecorationEquiv sig top P low hsig n nfl).symm.summable_iff

end WaveTurbulence.Induct
