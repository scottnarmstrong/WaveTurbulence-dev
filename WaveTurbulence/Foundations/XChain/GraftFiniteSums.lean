/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
/-! Exact finite-support reindexing of source canonical-garden sums by construction data. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem finsum_canonicalGraft_trunc {w p : ℕ} (sig : Fin w → ℤˣ) (hw : 4 ≤ w)
    (Ntop Natt : ℕ) (f : LayeredGarden w → ℂ) :
    (∑ᶠ C : {C : CanonicalGraftData sig p // C.IsTrunc Ntop Natt}, f C.1.graft) =
      ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
        LG.IsTrunc p Ntop Natt}, f LG.1 :=
  finsum_eq_of_bijective (canonicalGraftTruncEquiv sig hw Ntop Natt)
    (canonicalGraftTruncEquiv sig hw Ntop Natt).bijective (fun _ => rfl)

end WaveTurbulence.Induct
