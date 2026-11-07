/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapTerm
/-! FLOWER-P7: the decapitation identity for the couple with both roots pinned at time `t`.

`kernelKgen` of the cap of a width-six layered garden `LG` (roots in layer `p`, all roots designated with the
time `t`, caps `up = t`, base vector `k`, root labels `0`) equals `c^2 ∑_n outer(n) · kernelKgen LG (n)`, where
`n` runs over the six root labels of `LG` subject to the two outer constraints
`n (idx j 0) - n (idx j 1) + n (idx j 2) = 0`, and
`outer(n) = ε(n_0,n_1,n_2) ε(n_3,n_4,n_5) e^{πi ζ_0 δ L^{2γ} Ω_0 t} e^{πi ζ_1 δ L^{2γ} Ω_1 t}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- The summand of `kernelKgen` as a function of the labelling. -/
noncomputable def kgTerm {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (κ : GNode LG.garden.tree → (Fin d → ℤ)) : ℂ :=
  (epsDec LG.garden κ : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ) : ℂ) *
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG up fix).indicator
        (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ))
        (LG.garden.extendFix fix τ)) *
    ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ ℓ.toNode) : ℂ)

theorem kernelKgen_eq_tsum {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelKgen L γ δ F LG fix off wt up k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, kgTerm L γ δ F LG fix off wt up k₀ κ.1 := rfl

theorem inputProd_cap (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    (∏ ℓ ∈ inputLeaves (capGarden LG.garden hsig),
      (F ((capLayered LG hsig p hp).layer ℓ.toNode)
        (cosetDecoration (capGarden LG.garden hsig) L k (upperDec (T := LG.garden.tree) κ') ℓ.toNode) : ℂ)) =
    ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ' ℓ.toNode) : ℂ) := by
  rw [inputLeaves_cap, Finset.prod_image (fun x _ y _ h => liftLeaf_injective h)]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [liftLeaf_toNode, capLayered_layer_lift, coset_cap_lift]

/-- The outer weight: the two root `ε`'s and the pinned root phase. -/
noncomputable def outerWeight (L γ δ : ℝ) (k : Mom d) (t : ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) : ℂ :=
  ((∏ j : Fin 2, epsCoef (n (idx j 0)) (n (idx j 1)) (n (idx j 2)) : ℝ) : ℂ) * rootPhase L γ δ k t n

theorem kgTerm_cap (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    kgTerm L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
        (fun _ => t) k (upperDec (T := LG.garden.tree) κ') =
      outerWeight L γ δ k t (fun c => κ' (GNode.root LG.garden.tree c)) *
        kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ' := by
  unfold kgTerm outerWeight
  rw [integral_cap L γ δ LG hsig p hp t k κ', inputProd_cap L F LG hsig p hp k κ']
  simp only [Complex.ofReal_one, mul_one]
  have he := epsDec_cap LG.garden hsig κ'
  rw [he]
  push_cast
  ring

end WaveTurbulence.FlowerP7
