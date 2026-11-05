/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.RootInputCoordinates
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.FiniteCellDecomposition
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement

/-! # Inserting the root mask before Fourier inversion of the actual leaf inputs -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The actual finite root row inserts the mask in the literal leafwise
localized input product, before any cancellation in Fourier space. -/
theorem sourceRootMask_mul_coupleLeafwiseProduct {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    sourceRootMask c k *
      (∏ a, leafCell (F a) (c a) ((coupleMomentumData hQ hG).inputMomentum k x a)) =
      ∏ a, leafCell (F a) (c a) ((coupleMomentumData hQ hG).inputMomentum k x a) :=
  (coupleRootInputCoordinates hQ hG).sourceRootMask_mul_localizedLeafWeight F c k x

/-- In particular, the common-profile source product is unchanged. -/
theorem sourceRootMask_mul_coupleLeafCellProduct {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    sourceRootMask c k * coupleLeafCellProduct hQ hG F c k x =
      coupleLeafCellProduct hQ hG F c k x :=
  sourceRootMask_mul_coupleLeafwiseProduct hQ hG (fun _ => F) c k x

end WaveTurbulence.RegAsymp
