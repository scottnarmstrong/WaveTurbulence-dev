/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Final
/-! FLOWER-P7: truncating the remainder at stage `p`. The kernels of the canonical couples of `coupleSum` only
read the inputs `F_q` with `q ≤ p`; truncating `R` there makes all inputs summable on every coset. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem kernelKgen_congr {w d : ℕ} (L γ δ : ℝ) (F F' : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) = F' (LG.layer ℓ.toNode)) :
    kernelKgen L γ δ F LG fix off wt up k₀ nroot nfl = kernelKgen L γ δ F' LG fix off wt up k₀ nroot nfl := by
  unfold kernelKgen
  congr 1
  refine tsum_congr fun κ => ?_
  congr 1
  exact Finset.prod_congr rfl fun ℓ hℓ => by rw [h ℓ hℓ]

theorem coupleSum_congr (P : WTParams) (F F' : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) (dt : Bool)
    (t : ℝ) (k : Mom P.d) (h : ∀ q ≤ p, F q = F' q) :
    coupleSum P F p N kind dt t k = coupleSum P F' p N kind dt t k := by
  unfold coupleSum
  refine finsum_congr fun Q => finsum_congr_Prop rfl fun hQ => ?_
  exact kernelKgen_congr _ _ _ F F' Q _ _ _ _ _ _ _ fun ℓ _ => h _ (hQ.1.2.1 _)

/-- The remainder truncated at stage `p`. -/
def truncR {d : ℕ} (R : ℕ → Mom d → ℝ) (p : ℕ) : ℕ → Mom d → ℝ := fun q => if q ≤ p then R q else 0

theorem inputsF_truncR (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) {q : ℕ} (hq : q ≤ p) :
    inputsF P (truncR R p) q = inputsF P R q := by
  funext k; simp [inputsF, truncR, hq]

theorem remainderBound_truncR (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hL : 1 ≤ P.L)
    (hR : RemainderBound P R p) : RemainderBound P (truncR R p) p := by
  intro q hq
  simpa [truncR, hq] using hR q hq

theorem summable_inputsF_truncR (P : WTParams) (R : ℕ → Mom P.d → ℝ) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {p : ℕ}
    (hp : p ≤ P.D) (hR : RemainderBound P R p) (k : Mom P.d) (q : ℕ) :
    Summable fun n : Fin P.d → ℤ => |inputsF P (truncR R p) q (k + latticePoint P.L n)| := by
  by_cases hq : q ≤ p
  · exact summable_inputsF_of_RemainderBound P (truncR R p) hd hL hp (remainderBound_truncR P R p hL hR) hq k
  · have h := summable_abs_schwartz_coset hL (P.φ (P.δ * q)) k
    refine h.congr fun n => ?_
    simp [inputsF, truncR, hq]

end WaveTurbulence.FlowerP7
