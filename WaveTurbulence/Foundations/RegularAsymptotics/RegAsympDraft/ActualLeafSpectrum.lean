/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CosetCoordinateBridge
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.FiniteCellDecomposition
public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoff
public import WaveTurbulence.Foundations.Incoh.LeafArrayLocalization

/-! # Spectral decomposition of the literal input product in the kernel -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The literal B1 input product in its actual integer-coordinate summand. -/
theorem actual_coset_leafProduct_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (L : ℝ) (k : Mom d) (F : Mom d → ℂ) :
    (∏ ℓ ∈ inputLeaves G, F (cosetDecoration G L k ((integerLinkEquiv hQ hG d).symm θ).val ℓ.toNode)) =
      ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then latticePoint L (θ j).1 else latticePoint L (θ j).2) a) := by
  rw [prod_inputLeaves_eq_enumerated hQ hG,
    cosetDecoration_integerLinkEquiv_eq_decOfParams hQ hG d θ L k]
  simp only [coupleMomentumData_inputMomentum,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]

end WaveTurbulence.RegAsymp
