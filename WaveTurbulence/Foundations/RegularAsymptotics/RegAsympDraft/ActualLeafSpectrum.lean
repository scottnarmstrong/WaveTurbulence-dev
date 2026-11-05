/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CosetCoordinateBridge
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleSpectralDecomposition
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

/-- For the literal source input product, the full leaf-center series of
finite exact spectral integrals converges to that product. The finite link
sets are chosen before every input and every root momentum. -/
theorem actual_leafProduct_hasSum_spectrum (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∃ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (∀ c, ((S c).card : ℝ) ≤ C ^ Q.links.length) ∧
        ∀ K M : ℕ, ∀ B : ℝ, d+1 ≤ K → 0 ≤ B →
        ∀ F : Mom d → ℂ, Fourier.spatialNorm K M F ≤ ENNReal.ofReal B →
        ∀ L : ℝ, ∀ k : Mom d,
        ∀ θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ),
          HasSum (fun c => ∑ z ∈ S c,
            ∫ ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ,
              (coupleMomentumData hQ hG).localizedSourceSpectralDensity 1 (fun _ => F) c z k
                (fun j i => if i=0 then latticePoint L (θ j).1 else latticePoint L (θ j).2) ξ)
            (∏ ℓ ∈ inputLeaves G,
              F (cosetDecoration G L k ((integerLinkEquiv hQ hG d).symm θ).val ℓ.toNode)) := by
  classical
  obtain ⟨C,hC,h⟩ := actual_couple_uniform_spectral_decomposition d hd
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG
  choose S hcard hspec using h G Q hQ hG
  refine ⟨S,hcard,?_⟩
  intro K M B hK hB F hF L k θ
  let x : Fin Q.links.length → Fin 2 → Mom d := fun j i =>
    if i=0 then latticePoint L (θ j).1 else latticePoint L (θ j).2
  rw [actual_coset_leafProduct_eq hQ hG θ L k F]
  have hh := hasSum_leafCell_product (fun _ : Fin (2*Q.links.length+1) => F)
    (fun a => (coupleMomentumData hQ hG).inputMomentum k x a)
  apply hh.congr_fun
  intro c
  have hc := hspec c K M B hK hB F hF 1 k x
  simpa only [Circle.coe_one,one_mul,coupleLeafCellProduct] using hc.symm

end WaveTurbulence.RegAsymp
