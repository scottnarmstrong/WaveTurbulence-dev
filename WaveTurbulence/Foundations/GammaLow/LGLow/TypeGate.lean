/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.EvalAssemble

/-! # LG-low (packet L07): the family-free waist `TypeGateAt`

`TypeGateAt P` is the conclusion of main's `LGSpine.stage1_type_bound`. `evalV_typeGate_bound` and
`evalOps_typeGate_bound` are main's `evalV_gate_bound` (`Spine/EvalGate.lean`) and `evalOps_gate_bound`
(`Spine/EvalAssemble.lean`), copied by source (sha256 in `COPIED-SHA256SUMS`) with the gate bundle
`(C₀, hcoarse, hfourier, hcount, habs, hlog, hgate)` replaced by `hTG : TypeGateAt P` and the call of
`stage1_type_bound` by `hTG`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open MeasureTheory Set Finset CentralDiff
open scoped Classical ENNReal

/-- **The family-free waist of main's nonregular chain.** The conclusion of `LGSpine.stage1_type_bound`
(AMEND6′, TARGET L2236–L2255 before the weights): the Stage 1 bound of a twist-closed sum of carried gardens against a
pair-type family. Main's chain from `stage1_type_bound` up to `NonregularEstimateAt` (and up to the flower couple
clause) uses the source gates (Stage 1, finalsbest1, ladderl1old, finalcount1), the absorption constants and
`1 ≤ log L` only through this conclusion; it is free of the vine family and of `γ`. -/
def TypeGateAt (P : WTParams) : Prop :=
  ∀ {p R N : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) → 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (A : Finset (LayeredGarden (2 * R))), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s →
    U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
    ‖∑ LG ∈ A, U.toLF.value tt base roots LG‖ ≤ s *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))))

/-- Main's `evalV_gate_bound` through the waist. -/
theorem evalV_typeGate_bound (P : WTParams) (hTG : TypeGateAt P)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain)
    (g : TProf P.d (2 * R)) (B₀ : NNReal) (hB₀ : 0 < (B₀ : ℝ))
    (hg : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (g q j j') ≤ ENNReal.ofReal (B₀ : ℝ)) :
    ‖evalV P A tt roots g base‖ ≤ (B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have hcard : ∀ LG ∈ A, (inputLeaves LG.garden).card = N + R := by
    intro LG hLG
    have h1 := twice_card_inputLeaves LG.garden (hplain LG hLG)
    have h2 : LG.garden.order = N := (hA LG hLG).2.2.1
    omega
  have := hTG hp hR hRmax hN1 hN A hA hcl tt htt
    base roots (oneFamily P g B₀) ((B₀ : ℝ) ^ (N + R)) (pow_pos hB₀ _) (fun i q j j' hq => hg q hq j j')
    (fun LG hLG => by
      have : Unique (oneFamily P g B₀).ι := inferInstanceAs (Unique Unit)
      rw [TypeFamilyD.size_eq]
      change (∑ _i : (oneFamily P g B₀).ι, (B₀ : ℝ) ^ (inputLeaves LG.garden).card) ≤ _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul, hcard LG hLG])
  convert this using 2
  unfold evalV
  refine Finset.sum_congr rfl fun LG _ => ?_
  have : ∀ LG : LayeredGarden (2 * R), Unique ((oneFamily P g B₀).toLF.ι LG) := fun _ => inferInstanceAs (Unique Unit)
  rw [LeafFamily.value, Finset.univ_unique, Finset.sum_singleton]
  change _ = ((1 : ℝ) : ℂ) * kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g) (fun b => tt b.1.1) 0 base roots 0
  simp

/-- Main's `evalOps_gate_bound` through the waist. -/
theorem evalOps_typeGate_bound (P : WTParams) (hs : PieceSmall P) (hTG : TypeGateAt P) (hd : 1 ≤ P.d)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (base : Mom P.d)
    (M : ℕ) (lam : ℝ) (T : ℝ) (hT1 : 1 ≤ T) (hT : (2 * M + 1) / |lam| ≤ T)
    (xs : ℝ) (hxs : 0 ≤ xs) (hxM : ∀ m ∈ Finset.range (2 * M + 1), |lam * ((m : ℝ) - M)| ≤ xs)
    (Dmax : ℕ) (B₀ : NNReal) (hB₀ : 0 < (B₀ : ℝ)) (Lops : ℕ)
    (os : List (TOp P.d (2 * R))) (hlen : os.length ≤ Lops) (hdc : dcnt os ≤ Dmax)
    (h0 : TProf P.d (2 * R)) (u c : ℝ) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hI : Inv p (40 * P.d) (40 * P.d) os u c h0)
    (hB : c + u * ((1 + xs * (2 * (P.d : ℝ)) ^ (40 * P.d + Dmax)) ^ Lops - 1) ≤ (B₀ : ℝ)) :
    ‖evalOps (evalV P A tt roots) M lam os h0 base‖ ≤ T ^ Lops * ((B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
  rw [evalOps_apply (Y := ℂ)]
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d + Dmax) with hκ
  have hnorm := evalOps_norm_le hd (fun g => evalV P A tt roots g base) M lam (p := p) (A := 40 * P.d)
    (B := 40 * P.d) xs κ (B₀ : ℝ) ((B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))))
    hxs hxM (40 * P.d + Dmax) (fun a ha => by
      have h2 : (1 : ℝ) ≤ 2 * P.d := by linarith
      constructor
      · calc (P.d : ℝ) ^ a ≤ (2 * (P.d : ℝ)) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) a
          _ ≤ _ := pow_le_pow_right₀ h2 ha
      · calc (2 : ℝ) ^ a * (P.d : ℝ) ^ a = (2 * (P.d : ℝ)) ^ a := by rw [mul_pow]
          _ ≤ _ := pow_le_pow_right₀ h2 ha)
    (fun g hg => evalV_typeGate_bound P hTG hp hR hRmax hN1 hN A hA hcl
      tt htt base roots hplain g B₀ hB₀ hg)
    os h0 u c hu hc (by omega) hI (by
      have h2 : (1 : ℝ) ≤ 1 + xs * κ := by
        have : 0 ≤ xs * κ := mul_nonneg hxs (by positivity)
        linarith
      have := pow_le_pow_right₀ h2 hlen
      nlinarith)
  refine hnorm.trans ?_
  have hS : ∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam| ≤ T := (sum_abs_cw_le M lam).trans hT
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hG0 : 0 ≤ (B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    have := hs.delta_pos
    positivity
  refine mul_le_mul_of_nonneg_right ?_ hG0
  calc _ ≤ T ^ os.length := pow_le_pow_left₀ hS0 hS _
    _ ≤ T ^ Lops := pow_le_pow_right₀ hT1 hlen

end WaveTurbulence.GammaLow.LGLow
