/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr10

/-! # B4 STAGE1MK-GATE: soundness of pieces at a prescribed point, and the zero pieces

* `pointPiece_soundFull`: `SoundMKFull` for B2c's piece `stage1PieceMKOf` at a prescribed point whose garden satisfies
  the truncation-free carrier, at any marked set `Mk ⊆ 𝒱₀(σ)` (ruling R173), given `MkPieceRest`.
* `zeroPiece a`: the piece at the empty marked set, no survivors, `nProt = 0`, no pins, no filters, indicator `1`;
  it is `SoundMKFull` (`zeroPiece_soundFull`) and represents the value `0` (`representsIntMKSel_zero`,
  `representsIntMK_zero`: an empty superposition). It is the piece of a zero class (stem-unclean, value `0` by FL-SEP). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.Stage1MKGate

/-- **`SoundMKFull` for a piece at a prescribed point** (any marked set inside `𝒱₀(σ)`). -/
theorem pointPiece_soundFull (P : WTParams) {R : ℕ} (hR : 1 ≤ R) {p N : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (hc : Stage1Mk.Stage1CarriesW P p N a.layered) (hNb : N ≤ P.N (p + 1) ^ 4) (hL : P.L ≠ 0)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) {Mk : Set (Stage1.CLVine a.prime.skeleton)}
    (hMk : Mk ⊆ vinesV0 a.prime.skeleton a.totalSigma)
    (prot : Finset (GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree)) (nProt : ℕ)
    (fix : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Option ℝ)
    (filt : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Mom P.d) → ℝ)
    (lb : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Option ℝ)
    (hrest : MkSubpro.MkPieceRest
      (MkSubpro.stage1PieceMKOf P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma Mk prot nProt fix filt ind
        lb) cθ) :
    SoundMKFull
      (MkSubpro.stage1PieceMKOf P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma Mk prot nProt fix filt ind lb)
      p 0 roots cθ := by
  obtain ⟨hI, hbal, hn⟩ := skelFacts_of_carriesW P p N hR hc a.prime
  have hsz := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hord : a.layered.garden.order = N := hc.2.1
  exact MkSubpro.soundMKFull_marked P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma hMk a.prime.prime hI hbal
    hn p (by omega) (fun v => Canon.layer_le_of_isCanonGC hc.1 _) hL 0 roots cθ prot nProt fix filt ind hrest

/-- **The zero piece of a prescribed point**: empty marked set (no survivors), `nProt = 0`, no pins or filters,
indicator `1`. -/
def zeroPiece (P : WTParams) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) : Stage1PieceMK P.d R :=
  MkSubpro.stage1PieceMKOf P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma ∅ ∅ 0 (fun _ => none)
    (fun _ => none) (fun _ => 1)

theorem zeroPiece_m (P : WTParams) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) : (zeroPiece P a).surv.m = 0 := by
  show (VineA.NormalizedSplice.survObjs a.prime.skeleton a.totalSigma ∅).length = 0
  rw [VineA.NormalizedSplice.survObjs_length, RedSplice.survivorsMk_empty]
  rfl

theorem zeroPiece_rest (P : WTParams) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (cθ : ℝ) :
    MkSubpro.MkPieceRest (zeroPiece P a) cθ where
  survivors_card := by rw [zeroPiece_m]; exact Nat.zero_le _
  prot_card := (Finset.card_eq_zero.mpr rfl).trans_le (Nat.zero_le _)
  fix_prot := fun b hb => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hb
  fix_layer := fun b t hb => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hb
  filt_ok := fun a q hq => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hq
  ind_ok := fun k => by simp [zeroPiece, MkSubpro.stage1PieceMKOf]
  ind_local := fun k k' _ => rfl
  lb_free := fun b hb => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hb
  lb_prot := fun b hb => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hb
  lb_layer := fun b x hb => by simp [zeroPiece, MkSubpro.stage1PieceMKOf] at hb

theorem zeroPiece_soundFull (P : WTParams) {R : ℕ} (hR : 1 ≤ R) {p N : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (hc : Stage1Mk.Stage1CarriesW P p N a.layered) (hNb : N ≤ P.N (p + 1) ^ 4) (hL : P.L ≠ 0)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) : SoundMKFull (zeroPiece P a) p 0 roots cθ :=
  pointPiece_soundFull P hR a hc hNb hL roots cθ (Set.empty_subset _) ∅ 0 (fun _ => none) (fun _ => none) (fun _ => 1)
    (fun _ => none)
    (zeroPiece_rest P a cθ)

/-- The mass bound's prefactor is nonnegative. -/
theorem massBound_nonneg {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP x s : ℝ)
    (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) :
    0 ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ x * s := by
  have h1 := pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg P.δ)) (n - π.Gsb.order)
  have h2 := pow_nonneg hC (π.Gsb.order + 2 * R)
  have h3 := Real.rpow_nonneg hL (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
    P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have h4 := Real.rpow_nonneg hL (cP * P.d * (π.nProt : ℝ))
  have h5 := Real.rpow_nonneg hL x
  positivity

/-- **The value `0` is represented** (an empty superposition), for every piece, selection and mass. -/
theorem representsIntMKSel_zero {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R)
    (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) :
    RepresentsIntMKSel π sel n cP tt base roots s 0 := by
  refine ⟨Empty, ⊤, 0, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    integrable_zero_measure, by simp, integrable_zero_measure, ?_, fun e => e.elim⟩
  rw [integral_zero_measure]
  exact massBound_nonneg π n cP _ s hC hL hs

theorem representsIntMK_zero {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ)
    (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hs : 0 ≤ s) : π.RepresentsIntMK n cP tt base roots s 0 :=
  (representsIntMKSel_empty π n cP tt base roots s 0).mp (representsIntMKSel_zero π ∅ n cP tt base roots s hC hL hs)

/-- `selMassMK` is nonnegative. -/
theorem selMassMK_nonneg {R : ℕ} (N : ℕ) {b : ℝ} (hb : 0 ≤ b) {Rs : Fin (2 * R) → ℝ} (hRs : ∀ j, 0 ≤ Rs j)
    (kSel : Fin (2 * R) → Option ℕ) (U : Finset (Fin (2 * R))) : 0 ≤ selMassMK N b Rs kSel U := by
  unfold selMassMK
  refine mul_nonneg (pow_nonneg hb N) (Finset.prod_nonneg fun j _ => ?_)
  split_ifs
  · simp [inv_nonneg.mpr (hRs j)]
  · exact mul_nonneg (inv_nonneg.mpr (hRs j)) (Real.rpow_nonneg (hRs j) _)
  · exact zero_le_one

end WaveTurbulence.Flower.Stage1MKGate
