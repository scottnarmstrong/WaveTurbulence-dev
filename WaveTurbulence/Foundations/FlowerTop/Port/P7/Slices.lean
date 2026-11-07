/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.LGBridge
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.LGTT
public import WaveTurbulence.Foundations.Spine.TwistClosedNR
/-! FLOWER-P7: slices at a fixed vector of top orders of a twist-closed family are twist-closed (LF twists
preserve the top order of every tree: `LFTwist.FamilyBatch.topOrder`), and the resulting slice estimates for
the irreducible blocks. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
theorem twistClosed_topFilter {w : ℕ} (p : ℕ) (A : Finset (LayeredGarden w)) (hA : TwistClosed p A)
    (v : Fin w → ℕ) :
    TwistClosed p (A.filter fun LG => ∀ j, LG.topOrder p j = v j) := by
  intro kind ι B L hprime hcan hmem LH hLH
  obtain ⟨hmemA, hv⟩ := Finset.mem_filter.1 hmem
  refine Finset.mem_filter.2 ⟨hA kind ι B L hprime hcan hmemA LH hLH, fun j => ?_⟩
  obtain ⟨M', B', _, hbatch, rfl⟩ := hLH
  rw [hbatch.topOrder j]
  exact hv j

/-- The shared hypotheses of LG-SPINE's estimates (as in `garden_estimate_slice_of_gate`). -/
structure LGContext (C₀ : ℕ) (P : WTParams) where
  hs : PieceSmall P
  hcoarse : CoarseSplicedAt P
  hfourier : LadderFourierAt P
  hcount : FinalCountAt P
  habs : FinalAbsorptionAt (6 * C₀) P
  hlog : 1 ≤ Real.log P.L
  hgate : Stage1ReductionAt C₀ P
  hd : 1 ≤ P.d
  hlowP : LowProfileAt P
  htime : P.τstar = (P.D : ℝ) * P.δ
  Cφ : ℝ
  hCφ : 0 ≤ Cφ
  hφ : ∀ τ ∈ Set.Icc (0 : ℝ) P.τstar, SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ

open scoped Classical in
/-- **Irreducible block, one slice** (`m = 2, 3`): the sum of the six-tree kernels over the canonical truncated
gardens of fixed order and fixed top-order vector. -/
theorem garden_slice_kernelKgen (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) {m : ℕ} (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1))
    (ζ : Fin (2 * m) → ℤˣ) (hζ : IsBalancedSig ζ) (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) (tt : Fin (2 * m) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin (2 * m) → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P G.Cφ p m N ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + m) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LG ∈ (gardenSet P p N m ζ).filter (fun LG => ∀ j, LG.topOrder p j = v j),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LG (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * N) := by
  have hmem : ∀ LG ∈ (gardenSet P p N m ζ).filter (fun LG => ∀ j, LG.topOrder p j = v j),
      IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
        LG.garden.sig = ζ ∧ LG.garden.order = N := fun LG h =>
    (Canon.finite_truncSum_support P (p + 1) N (2 * m) ζ).mem_toFinset.mp (Finset.mem_filter.1 h).1
  have h := garden_estimate_slice_of_gate_tt C₀ P G.hs G.hcoarse G.hfourier G.hcount G.habs G.hlog G.hgate G.hd
    G.hlowP G.htime G.hCφ G.hφ hp Rr hRr hm2 hmmax ζ hζ n k hN tt htt _ hmem
    (twistClosed_topFilter p _ (twistClosed_gardenSet P G.hd hp hm2 ζ hN) v) hnum
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.sum_congr rfl fun LG hLG => ?_
  exact kernelKgen_eq_kernelLeaves P.L P.γ P.δ (inputsF P Rr) LG (hmem LG hLG).1.1 tt k n

end WaveTurbulence.FlowerP7
