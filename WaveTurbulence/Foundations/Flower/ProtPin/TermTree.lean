/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermCore
public import WaveTurbulence.Foundations.Flower.ProtPin.PieceGate
public import WaveTurbulence.Foundations.Flower.ProtPin.Pieces
public import WaveTurbulence.Foundations.Flower.ProtPin.Lattice
public import WaveTurbulence.Foundations.Flower.ProtCut.Check
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckAlpha
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability

/-! # D3 PROT-PIN: configuration `term` of a protected paired tree, one output at a time

`term_perk`: D2c's (cut-term) identity, then `term_core` (zero-extended terminal operator, product, trace), then the
gates on the four pieces (`tree_piece_rn`, `couple_piece_rn`) and the exceptional-pair sum (`tsum_jbr_coset_sharp`):
the per-output norm of `kernelProt (term at s)` on `timeBoxGt p q'` is at most
`C_θ · coupling² (latC L^d)² · L^{4c'} · C₁⁴ (C₁δ)^{n-1} L^{-(γ₁-√η)g} · ∏ B_ℓ`, for any multiplier whose pieces are `1`
and whose cut factor `Mc` has modulus `≤ 1` (the dagger). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- The real factor of `regBound`. -/
def rb (P : WTParams) (n g : ℕ) : ℝ := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)

theorem rb_nonneg {P : WTParams} (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) : 0 ≤ rb P n g := by
  unfold rb; have := Real.rpow_nonneg hL (-(P.gamma1 - Real.sqrt P.η) * g); positivity

theorem regBound_eq_rb (P : WTParams) (n g : ℕ) : regBound P n g = ENNReal.ofReal (rb P n g) := rfl

/-- Four pieces: `C₁⁴ (C₁δ)^{n-1} L^{-(γ₁-√η) g}`. -/
theorem rb_four {P : WTParams} (hL : 0 < P.L) {n₁ n₂ n₃ n₄ g₁ g₂ g₃ g₄ : ℕ} :
    rb P n₁ g₁ * rb P n₂ g₂ * rb P n₃ g₃ * rb P n₄ g₄ =
      P.C₁ ^ 3 * (P.C₁ * (P.C₁ * P.δ) ^ (n₁ + n₂ + n₃ + n₄) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((g₁ + g₂ + g₃ + g₄ : ℕ) : ℝ))) := by
  unfold rb
  push_cast
  rw [show -(P.gamma1 - Real.sqrt P.η) * ((g₁ : ℝ) + g₂ + g₃ + g₄) =
    -(P.gamma1 - Real.sqrt P.η) * g₁ + -(P.gamma1 - Real.sqrt P.η) * g₂ + -(P.gamma1 - Real.sqrt P.η) * g₃ +
      -(P.gamma1 - Real.sqrt P.η) * g₄ by ring, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL]
  ring

/-- The `cutU` range on the box is `(s, T)`. -/
theorem cutU_eq (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (hch : ChainIn p (appendChain Xp (cpair m Qr Qg inner)) LG) {s T : ℝ} (hps : (p : ℝ) < s)
    (hT : T ≤ p + 1) : cutU LG Xp T s = Ioo s T := by
  have hna : layerAt LG ((0 : Fin 1), Xp.lonePath) = p := by
    refine (layerAt_node LG D.aBr.toNode).trans (hch D.aBr rfl ?_ ?_)
    · show Xp.lonePath <+: (appendChain Xp (cpair m Qr Qg inner)).lonePath
      rw [appendChain_lonePath]; exact List.prefix_append _ _
    · show Xp.lonePath ≠ (appendChain Xp (cpair m Qr Qg inner)).lonePath
      rw [appendChain_lonePath, cpair_lonePath]
      simp [lonePos]
  ext u
  simp only [cutU, hna, Set.mem_setOf_eq, Set.mem_Ioo]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  constructor
  · rintro ⟨-, -, -, h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, by linarith, h2, h1⟩

/-- From an output-weighted bound to a bound with the inverse weight. -/
theorem le_mul_inv_of_weighted {J : ℝ} (hJ : 0 < J) {x y : ℝ≥0∞} (h : ENNReal.ofReal J * x ≤ y) :
    x ≤ y * ENNReal.ofReal J⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos hJ, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (by simp [hJ]) (by simp)]
  rwa [mul_comm]

/-- A couple piece in its own orientation. -/
theorem rn_couple_oriented {θ p : ℝ} (f : ℝ → ℝ → ℂ) (c : ℝ → ℝ → Fin 2 → ℝ)
    (hc : (∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) :
    rn θ (timeBoxGt p p) (fun x => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) ≤
      rn θ (timeBox p p) (fun x => f (x 0) (x 1)) := by
  refine (rn_mono_set θ (fun x hx => hx.1) _).trans ?_
  rcases hc with hc | hc
  · exact le_of_eq (rn_congr θ fun x _ => by rw [(hc _ _).1, (hc _ _).2])
  · have hsw := rn_swap θ (timeBox p p) (fun x => f (x 0) (x 1))
    have hpre : ConjCoh.permT swap2 ⁻¹' timeBox p p = timeBox p p := by
      ext x
      simp only [Set.mem_preimage, permT_swap2_apply, timeBox, Set.mem_setOf_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      tauto
    rw [hpre] at hsw
    rw [← hsw]
    exact le_of_eq (rn_congr θ fun x _ => by
      rw [(hc _ _).1, (hc _ _).2, permT_swap2_apply]; rfl)

theorem timeBoxGt_cl (p : ℝ) : ∀ x ∈ timeBoxGt p p, x ∈ closure (interior (timeBoxGt p p)) :=
  fun _ hx => VineEstS3.timeBoxGt_subset_closure_interior le_rfl hx

/-- `Σ_{e} f(yr_e) f(yg_e) ≤ (Σ_y f(y))²`: the exceptional data are determined by `(yr, yg)`. -/
theorem tsum_pairE_le {d : ℕ} (m : MiniTreeCode) (f : (Fin d → ℤ) → ℝ≥0∞) :
    ∑' e : PairE m d, f e.1.2.1 * f e.1.2.2 ≤ (∑' y, f y) * ∑' y, f y := by
  have hinj : Function.Injective (fun e : PairE m d => (e.1.2.1, e.1.2.2)) := by
    intro e e' h
    simp only [Prod.mk.injEq] at h
    have hx : e.1.1 = e'.1.1 := by rw [e.2.2, e'.2.2, h.1, h.2]
    exact Subtype.ext (Prod.ext hx (Prod.ext h.1 h.2))
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun y : (Fin d → ℤ) × (Fin d → ℤ) => f y.1 * f y.2))
    (le_of_eq ?_)
  rw [show (∑' y : (Fin d → ℤ) × (Fin d → ℤ), f y.1 * f y.2) = ∑' a, ∑' b, f a * f b from
    ENNReal.tsum_prod (f := fun a b => f a * f b), ← ENNReal.tsum_mul_right]
  congr 1
  funext a
  rw [ENNReal.tsum_mul_left]

/-- The decay factor of a side couple, summed. -/
theorem tsum_decay_le {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ∑' y : Fin d → ℤ, ENNReal.ofReal (jbr (k + latticePoint L y) ^ (30 * d))⁻¹ ≤ ENNReal.ofReal (latC d * L ^ d) := by
  refine le_trans (ENNReal.tsum_le_tsum fun y => ENNReal.ofReal_le_ofReal ?_) (tsum_jbr_coset_sharp hL k)
  have hj := Induct.one_le_jbr (k + latticePoint L y)
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hj
  push_cast
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

end WaveTurbulence.Flower.ProtPin
