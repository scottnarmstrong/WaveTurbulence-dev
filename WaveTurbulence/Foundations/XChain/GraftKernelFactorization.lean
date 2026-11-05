/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelSummand
/-! The literal kernelK decoration factor splits into top and attached-garden factors. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kernelDecorationFactor_graft {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (κ : GenDecoration (markedGardenGraft sig top P (fun B => (low B).garden) hsig) d n nfl) :
    kernelDecorationFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound)
      (fun _ => t) s k₀ κ =
    topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig
      (splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).1.1 k₀ p t s *
    ∏ B : P.parts, kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀
      ((splitGenDecoration sig top P (fun B => (low B).garden) hsig n nfl κ).2 B) := by
  let big := markedLayeredGardenGraft sig top P low p hsig hbound
  let kt := fun a => κ.1 (topNodeEmbedding top P (fun B => (low B).garden) a)
  let kl := fun B a => κ.1 (lowerNodeEmbedding top P (fun B => (low B).garden) B a)
  let Et : ℂ := ((∏ b : GBranch top, epsCoef (kt (b.child 0)) (kt (b.child 1)) (kt (b.child 2))) : ℝ)
  let Ei : P.parts → ℂ := fun B => (epsDec (low B).garden (kl B) : ℂ)
  let Pt := graftTopPhaseIntegral L γ δ sig top P (fun B => (low B).garden) hsig
    (fun a => k₀ + latticePoint L (kt a)) p t s
  let Pi := fun B => phaseIntegral L γ δ (low B).garden (kDomain (low B) (fun _ => p) s) s
    (cosetDecoration (low B).garden L k₀ (kl B))
  let Ii := fun B => ∏ ℓ ∈ inputLeaves (low B).garden,
    (F ((low B).layer ℓ.toNode) (cosetDecoration (low B).garden L k₀ (kl B) ℓ.toNode) : ℂ)
  have he : (epsDec big.garden κ.1 : ℂ) = Et * ∏ B, Ei B := by
    have hh := congrArg (fun r : ℝ => (r : ℂ))
      (markedGardenGraft_epsDec sig top P (fun B => (low B).garden) hsig κ.1)
    simp only [Complex.ofReal_mul] at hh
    have hprod := map_prod Complex.ofRealHom (fun B : P.parts => epsDec (low B).garden (kl B)) univ
    simp only [Complex.ofRealHom_eq_coe] at hprod
    exact hh.trans (congrArg (fun z : ℂ => Et * z) hprod)

  have hp : phaseIntegral L γ δ big.garden (kDomain big (fun _ => t) s) s
      (cosetDecoration big.garden L k₀ κ.1) = Pt * ∏ B, Pi B :=
    phaseIntegral_graft L γ δ sig top P low p hsig hbound hbranch hn hf t s hpt htp
      (cosetDecoration big.garden L k₀ κ.1)
  have hi : (∏ ℓ ∈ inputLeaves big.garden,
      (F (big.layer ℓ.toNode) (cosetDecoration big.garden L k₀ κ.1 ℓ.toNode) : ℂ)) = ∏ B, Ii B :=
    markedLayeredGardenGraft_inputs sig top P low p hsig hbound F
      (cosetDecoration big.garden L k₀ κ.1)
  have hh := congrArg₂ (· * ·) (congrArg₂ (· * ·) he hp) hi
  exact hh.trans (mul_three_prod Et Pt Ei Pi Ii)

end WaveTurbulence.Induct
