/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Adapter
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.FinalFalse
/-! FLOWER-P7: the `kind = L0`, `dt = false` adapter. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ}

/-- `PieceHyp` from LG-SPINE's numerics, with arbitrary per-tree caps. -/
def PieceHyp.mkOfTT (G : LGContext C₀ P) (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (tt : Fin (2 * 3) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) : PieceHyp C₀ P p N Rr k tt Creg where
  G := G
  hp := hp
  hN := hN
  hRr := hRr
  hR1 := hR1
  hmmax := by omega
  htt := htt
  hF := hF
  hnum6 := fun N' hN' => hGN 3 N' (by norm_num) (by omega) hN'
  hnumA := fun N' hN' => hGN 2 N' (by norm_num) (by omega) hN'
  hnumC := hCN
  hreg := hreg

/-- **The `kind = L0`, `dt = false` total couple bound over LG-SPINE's gates** (the content of `CoupleStage1At` for
`dt = false`; the regular part is the two-time family bound `regular_family_pointwise2`):
`‖coupleSum … L0 false‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{2νN}`. -/
theorem coupleSum_false_total (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) (t : ℝ) (k : Mom P.d)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  have hL1 : 1 ≤ P.L := by linarith [G.hs.L_ge]
  set H'' : RegPremises P (inputsF P (truncR Rr p)) p := H.of_trunc Rr rfl with hH''
  have hCreg : H''.Creg = H.Creg := rfl
  have hF := summable_inputsF_truncR P Rr G.hd hL1 hp.le hRr k
  have hreg := H''.bound
  have Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
      PieceHyp C₀ P p N (truncR Rr p) k tt (fun _ => H''.Creg) := fun tt htt =>
    PieceHyp.mkOfTT (N := N) (k := k) G hp hN (remainderBound_truncR P Rr p hL1 hRr) hR1 tt htt hF hGN hCN hreg
  have hCr0 : 0 ≤ H.Creg := by linarith [H.creg_pos]
  have hb : BoundNum P (fun _ => H''.Creg) H.Creg :=
    boundNum_of G hγ hCr0 (fun _ => hCreg.le) (fun _ => by rw [hCreg]; exact hCr0)
  have hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1) := by
    have := forty_dim_le_Lambda P G.hd (show p + 1 ≤ P.D by omega)
    have h1 : (P.d : ℝ) + 1 ≤ 40 * P.d := by
      have : (1 : ℝ) ≤ P.d := by exact_mod_cast G.hd
      linarith
    have h2 : ((40 * P.d : ℕ) : ℝ) ≤ P.Lambda (p + 1) := by exact_mod_cast this
    push_cast at h2
    linarith
  have hLoss := hLoss_of_numerics P G.hd G.hlog hL1 p N hN hCr0 hE
  rw [coupleSum_congr P (inputsF P Rr) (inputsF P (truncR Rr p)) p N .L0 false t k
    (fun q hq => (inputsF_truncR P Rr p hq).symm)]
  exact coupleSum_false_bound Hs hb hF t hΛ hLoss

end

end WaveTurbulence.FlowerP7
