/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermPerk
public import WaveTurbulence.Foundations.Flower.ProtOps.LocalExt
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar
public import WaveTurbulence.Foundations.Flower.ProtCut.CapCut
public import WaveTurbulence.Foundations.Flower.ProtCut.MultLocal

/-! # D3 PROT-PIN: configuration `term` in the local output norm (paired trees and cap couples)

`term_tree_final`: from `term_perk` at every lattice output, `LocalOutputExtension` (cost `L^{31d}`) and the constant
bookkeeping `term_final_alg`: one exceptional pair pays `δ² L^{2γ}` against `coupling²·L^{2d}`, the pieces' half-orders add
to `n - 1` and their incoherency indices to `g` (the cut link is coherent on a protected object). The cap couple is the
paired tree times one input (D2c `kernelProt_cap`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A multiplier whose every terminal cut has unit pieces and a cut factor of modulus `≤ 1`. -/
def GoodMult {d : ℕ} (LG : LayeredGarden 1) (X : RegChain) (M : (GNode LG.garden.tree → Mom d) → ℂ) : Prop :=
  ∀ {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {LGp LGi : LayeredGarden 1}
    {LGr LGg : LayeredGarden 2} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg),
    appendChain Xp (cpair m Qr Qg inner) = X →
    ∃ (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mp : (GNode LGp.garden.tree → Mom d) → ℂ)
      (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
      (Mg : (GNode LGg.garden.tree → Mom d) → ℂ), D.MultFactors M Mc Mp Mi Mr Mg ∧ (∀ K, Mp K = 1) ∧
      (∀ K, Mi K = 1) ∧ (∀ K, Mr K = 1) ∧ (∀ K, Mg K = 1) ∧ ∀ A B, ‖Mc A B‖ ≤ 1

theorem fD3_empty {w d : ℕ} {G : Garden w} (ω : GNode G.tree → Flower.IncTop.Star d → ℂ) (M Mu : GBranch G.tree → ℝ)
    (b : GBranch G.tree) (ξ : Fin 4 → Mom d) : fD3 ∅ ω ∅ (fun _ => false) M ∅ Mu b ξ = 1 := by
  simp [fD3]

theorem norm_indB_le {w d : ℕ} {T : Fin w → TTree} {ind : (GNode T → Mom d) → ℝ} (h : ∀ κ, 0 ≤ ind κ ∧ ind κ ≤ 1)
    (B : Fin 4 → Mom d) : ‖((indB ind B : ℝ) : ℂ)‖ ≤ 1 := by
  unfold indB
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h _).1]
  exact (h _).2

/-- The α multiplier of a protected paired tree is good. -/
theorem goodMult_alpha {d : ℕ} {LG : LayeredGarden 1} {X : RegChain} (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (M Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    GoodMult LG X (fun κ => Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ *
      filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ)) := by
  intro Xp m Qr Qg inner LGp LGi LGr LGg D hX
  subst hX
  refine ⟨_, _, _, _, _, D.multFactors_D3 ∅ (by simp) ω ∅ (fun _ => false) M ∅ Mu ind hind,
    fun K => ?_, fun K => ?_, fun K => ?_, fun K => ?_, fun A B => ?_⟩
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp only [fD3_empty, one_mul]
    exact norm_indB_le hind.1 B

/-- The α multiplier of a cap couple, on its paired tree, is good. -/
theorem goodMult_alpha_cap {d : ℕ} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {X : RegChain}
    (Dc : CapData X LG LG1) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (M Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    GoodMult LG1 X (Dc.capM fun κ => Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ *
      filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ)) := by
  intro Xp m Qr Qg inner LGp LGi LGr LGg D hX
  subst hX
  refine ⟨_, _, _, _, _, CapData.multFactors_D3_cap Dc D ∅ (by simp) ω ∅ (fun _ => false) M ∅ Mu ind hind,
    fun K => ?_, fun K => ?_, fun K => ?_, fun K => ?_, fun A B => ?_⟩
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp [fD3_empty]
  · simp only [fD3_empty, one_mul]
    refine norm_indB_le (fun κ => hind.1 _) B

/-! ### The constants -/

theorem coupling_sq_mul {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) :
    coupling d L γ δ ^ 2 * (L ^ d) ^ 2 = δ ^ 2 / 4 * L ^ (2 * γ) := by
  unfold coupling
  have h1 : (L ^ ((d : ℝ) - γ)) ^ 2 * L ^ (2 * γ) = (L ^ d) ^ 2 := by
    rw [← Real.rpow_natCast (L ^ ((d : ℝ) - γ)), ← Real.rpow_mul hL.le, ← Real.rpow_add hL, ← pow_mul,
      ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have h2 : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL _
  field_simp
  rw [← h1]
  ring

/-- **The final arithmetic of `term`.** -/
theorem term_final_alg {P : WTParams} {Cr CL K β leaf r c c' : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (hC1 : 0 ≤ P.C₁) (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hβ : 0 ≤ β) (hleaf : 0 ≤ leaf) (hr : 0 ≤ r)
    (hK : K = CL * Cr * latC P.d ^ 2 / 4) (hbig : K * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) :
    CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * r) * leaf))) ≤ P.L ^ c * (P.C₁ * P.δ * r) * (β * leaf) := by
  have hL0 : 0 < P.L := by linarith
  have e1 : coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 =
      latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ)) := by
    rw [← coupling_sq_mul hL0]; ring
  have e2 : P.L ^ (31 * P.d) * P.L ^ (4 * c') * P.L ^ (2 : ℝ) = P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, ← Real.rpow_natCast]
    push_cast; ring_nf
  have hc' : P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) ≤ P.L ^ c := Real.rpow_le_rpow_of_exponent_le hL hc
  have hA : 0 ≤ P.L ^ (31 * P.d) * P.L ^ (4 * c') := mul_nonneg (pow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hB : 0 ≤ P.C₁ * P.δ * r * β * leaf := by positivity
  calc CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
        P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf)))
      = (K * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) * (P.L ^ (31 * P.d) * P.L ^ (4 * c')) *
          (P.C₁ * P.δ * r * β * leaf) := by
        rw [show coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf =
          (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) * P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf by ring,
          e1, hK]
        ring
    _ ≤ P.L ^ (2 : ℝ) * (P.L ^ (31 * P.d) * P.L ^ (4 * c')) * (P.C₁ * P.δ * r * β * leaf) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbig hA) hB
    _ = P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) * (P.C₁ * P.δ * r * β * leaf) := by rw [← e2]; ring
    _ ≤ P.L ^ c * (P.C₁ * P.δ * r * β * leaf) := mul_le_mul_of_nonneg_right hc' hB
    _ = _ := by ring

theorem rb_succ (P : WTParams) {n : ℕ} (hn : 1 ≤ n) (g : ℕ) : rb P n g = P.C₁ * P.δ * rb P (n - 1) g := by
  unfold rb
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

end WaveTurbulence.Flower.ProtPin
