/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.RegFam
/-! FLOWER-P7: the `dt = true` adapter. Builds `PieceHyp` and `BoundNum` from LG-SPINE's context, the numerics
`GardenNum`/`CoupleNum`, and FLOWER-REG's regular premises, and proves the total couple bound. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {t : ℝ} {Creg : ℕ → ℝ}

/-- `PieceHyp` from LG-SPINE's numerics. -/
def PieceHyp.mkOf (G : LGContext C₀ P) (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) : PieceHyp C₀ P p N Rr k (fun _ => t) Creg where
  G := G
  hp := hp
  hN := hN
  hRr := hRr
  hR1 := hR1
  hmmax := by omega
  htt := fun _ => ht
  hF := hF
  hnum6 := fun N' hN' => hGN 3 N' (by norm_num) (by omega) hN'
  hnumA := fun N' hN' => hGN 2 N' (by norm_num) (by omega) hN'
  hnumC := hCN
  hreg := hreg

theorem boundNum_of (G : LGContext C₀ P) (hγ : P.γ ≤ P.d) {Cr : ℝ} (hCr : 0 ≤ Cr)
    (hCreg : ∀ e, Creg e ≤ Cr) (hCreg0 : ∀ e, 0 ≤ Creg e) : BoundNum P Creg Cr where
  hδ0 := G.hs.delta_pos
  hδ1 := G.hs.delta_le
  hL := by linarith [G.hs.L_ge]
  hν := G.hs.nu_pos.le
  hν8 := by linarith [G.hs.nu_small, G.hs.nu_pos]
  hCr0 := hCr
  hCreg := hCreg
  hCreg0 := hCreg0
  hγ := hγ

def RegPremises.of_trunc {F : ℕ → Mom P.d → ℝ} (H : RegPremises P F p) (R : ℕ → Mom P.d → ℝ) (hF : F = inputsF P R) :
    RegPremises P (inputsF P (truncR R p)) p := by
  subst hF
  have e : ∀ r ≤ p, inputsF P (truncR R p) r = inputsF P R r := fun r hr => inputsF_truncR P R p hr
  exact
  { H with
    hcF := fun r hr => by rw [e r hr]; exact H.hcF r hr
    hlowF := fun r hr => by rw [e r hr]; exact H.hlowF r hr
    hhighF := fun r hr => by rw [e r hr]; exact H.hhighF r hr
    hhighP := by rw [e p le_rfl]; exact H.hhighP
    h0 := fun k => by rw [e p le_rfl]; exact H.h0 k }

/-- **The `dt = true` total couple bound over LG-SPINE's gates** (the content of `RegularCouplesDtAt` and of
`CoupleStage1At` for `dt = true`): `‖coupleSum … true‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{2νN}`, with `kind` arbitrary. -/
theorem coupleSum_true_total (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1)) (k : Mom P.d) (kind : TreeKind)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N kind true t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  have hL1 : 1 ≤ P.L := by linarith [G.hs.L_ge]
  set H'' : RegPremises P (inputsF P (truncR Rr p)) p := H.of_trunc Rr rfl with hH''
  have hCreg : H''.Creg = H.Creg := rfl
  have hF := summable_inputsF_truncR P Rr G.hd hL1 hp.le hRr k
  have hreg := H''.bound
  have PH := PieceHyp.mkOf (N := N) (k := k) (t := t) G hp hN (remainderBound_truncR P Rr p hL1 hRr) hR1 ht hF hGN hCN hreg
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
  rw [coupleSum_congr P (inputsF P Rr) (inputsF P (truncR Rr p)) p N kind true t k
    (fun q hq => (inputsF_truncR P Rr p hq).symm)]
  exact coupleSum_true_bound PH hb kind hΛ hLoss

end

end WaveTurbulence.FlowerP7
