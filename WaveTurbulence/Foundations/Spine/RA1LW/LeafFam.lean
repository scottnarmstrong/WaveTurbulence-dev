/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CosetCoordinateBridge
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularApp
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp

/-! # Leaf-indexed profile families of a couple (RA1-LEAFWISE)

The individually modified inputs `H : LeafProfiles 2 d` of a regular couple, read as a family indexed by the
enumeration `plusLeafEquiv` of the actual positive leaves used by the coordinate-level RA1 modules. -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp Links Incoh

/-- The complex leaf family `a ↦ H_{leaf a}`. -/
@[expose] def leafFam {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (H : LGSpine.LeafProfiles 2 d) : Fin (2*Q.links.length+1) → Mom d → ℂ :=
  fun a k => (H (plusLeafEquiv hQ hG a).val.1 k : ℂ)

/-- `γ₁ = min (2γ) (min 1 (2(d-1)(1-γ)))`. -/
@[expose] def gam1L (d : ℕ) (γ : ℝ) : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

/-- The complexified address-indexed profile family. -/
@[expose] def addrFam {w d : ℕ} (H : Fin w × TTree.Path → Mom d → ℝ) : Fin w × TTree.Path → Mom d → ℂ :=
  fun z k => (H z k : ℂ)

theorem leafFam_eq_addrFam {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (H : LGSpine.LeafProfiles 2 d) (a : Fin (2*Q.links.length+1)) :
    leafFam hQ hG H a = addrFam H (plusLeafEquiv hQ hG a).val.1 := rfl

/-- The literal leafwise input product in its actual integer-coordinate summand. -/
theorem actual_coset_leafProduct_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (L : ℝ) (k : Mom d)
    (H : LGSpine.LeafProfiles 2 d) :
    (∏ ℓ ∈ inputLeaves G,
      (H ℓ.1 (cosetDecoration G L k ((integerLinkEquiv hQ hG d).symm θ).val ℓ.toNode) : ℂ)) =
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then latticePoint L (θ j).1 else latticePoint L (θ j).2) a) := by
  rw [prod_inputLeaves_eq_enumerated hQ hG (fun ℓ => (H ℓ.1 (cosetDecoration G L k
    ((integerLinkEquiv hQ hG d).symm θ).val ℓ.toNode) : ℂ))]
  apply Finset.prod_congr rfl
  intro a _
  rw [cosetDecoration_integerLinkEquiv_eq_decOfParams hQ hG d θ L k]
  simp only [leafFam,coupleMomentumData_inputMomentum,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]

end WaveTurbulence.RA1Leafwise
