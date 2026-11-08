/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Arith
public import WaveTurbulence.Foundations.Flower.SelRes.Gate
public import WaveTurbulence.Foundations.Flower.SelRes.Triv
public import WaveTurbulence.Foundations.Flower.SelRes.Pattern
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt3
public import WaveTurbulence.Foundations.Spine.Final3f

/-! # D7 SEL-RES / Point: the selected pointwise bound (o73 Prop 20.1 at fixed `ξ`)

`point_bound_atom`: `‖K(π.dataMK … ξ)‖ ≤ bsf · ∏_{v ∈ sel} L^{71d−14} M_v^{−1/18} (1+|ξ_v|)^{1/18}`, each selected atom
at its own scale `M_v` (finding F-C5b-1); `bsf` is C5a's `kernel_bound` right side. `point_bound` is the case `M ≡ M₂`.
With `c = 49d − 35` and `μ = δL^{2γ}`, the regimes are split per atom:
- normal (`μ ≥ 4L^{−18c}`): the atoms with `M_v ≤ L^{18c}` need no gain (`φ_v ≥ 1`); the others go through the
  patterns, the expansion of the low atoms, and the gates on the modifications (`L^{(22d+16)}` per expanded atom);
- tiny (`μ < 4L^{−18c}`): the atoms with `μM_v < 2` have `κφ_v ≥ 1`; the others go through the patterns; then the
  trivial bound against `bsf ≥ (δ^{10ν}/L)^{ord}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- C5a's pointwise kernel bound of a piece (the right side of `kernel_bound`). -/
def bsf (P : WTParams) (cθ : ℝ) {R : ℕ} (π : Stage1PieceMK P.d R) : ℝ :=
  (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
    (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
      ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L)) *
    (cθ ^ (40 * P.ν)) ^ π.Gsb.order *
    P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ))

theorem bsf_nonneg {P : WTParams} (hs : PieceSmall P) {cθ : ℝ} (hcθ : 1 ≤ cθ) {R : ℕ} (π : Stage1PieceMK P.d R) :
    0 ≤ bsf P cθ π := by
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  unfold bsf
  have : 0 ≤ cθ ^ (40 * P.ν) := Real.rpow_nonneg (by linarith) _
  positivity

/-- **A lower bound for `bsf`** (used only for tiny `δ`): `(δ^{10ν}/L)^{ord}`. -/
theorem bsf_lower {P : WTParams} (hs : PieceSmall P) {cθ : ℝ} (hcθ : 1 ≤ cθ) {R : ℕ} (π : Stage1PieceMK P.d R)
    (hgsb : (π.gsb : ℝ) ≤ π.Gsb.order) (hρ : (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) ≤ 2 * π.Gsb.order)
    (hR : (R : ℝ) ≤ 2 * π.Gsb.order) :
    (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order ≤ bsf P cθ π := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith
  have hδ0 := hs.delta_pos
  have hC1 : 1 ≤ P.C₁ := hs.c1_ge
  have hC2 : 1 ≤ P.C₂ := hC1.trans hs.c1_le_c2
  have hν0 := hs.nu_pos.le
  have hη0 := hs.eta_pos.le
  have hη1 := hs.eta_le
  set o : ℝ := (π.Gsb.order : ℝ) with ho
  have hlogL : 0 ≤ Real.log P.L := Real.log_nonneg hL1
  have hlogC : 0 ≤ Real.log P.C₁ := Real.log_nonneg hC1
  have hEL : -o ≤ -40 * P.ν * P.η * (π.gsb : ℝ) -
      P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60) := by
    have h6 : P.η ^ 6 ≤ 1 / 4 := by
      calc P.η ^ 6 ≤ (1 / 4) ^ 6 := pow_le_pow_left₀ hη0 hη1 6
        _ ≤ 1 / 4 := by norm_num
    have hg0 : (0 : ℝ) ≤ π.gsb := Nat.cast_nonneg _
    have hρ0 : (0 : ℝ) ≤ (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) := by positivity
    have h1 : 40 * P.ν * P.η * (π.gsb : ℝ) ≤ o / 400 := by
      have : 40 * P.ν * P.η ≤ 1 / 400 := by nlinarith [hs.nu_small]
      nlinarith
    have h2 : P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 ≤ o / 4 := by nlinarith
    nlinarith
  have hexp : Real.exp (o * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
      (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
        ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) ≥ (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order := by
    have e : (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order = Real.exp (o * (10 * P.ν * Real.log P.δ) + (-o) * Real.log P.L) := by
      rw [div_eq_mul_inv, mul_pow, Real.rpow_def_of_pos hδ0, ← Real.exp_nat_mul, ← Real.exp_log hL0,
        ← Real.exp_neg, ← Real.exp_nat_mul, Real.log_exp, ← Real.exp_add]
      congr 1; ring
    rw [e, ge_iff_le, Real.exp_le_exp]
    have : o * (Real.log P.C₁) ≥ 0 := mul_nonneg (Nat.cast_nonneg _) hlogC
    nlinarith
  have hc1 : 1 ≤ (cθ ^ (40 * P.ν)) ^ π.Gsb.order := one_le_pow₀ (Real.one_le_rpow hcθ (by linarith))
  have hL1' : 1 ≤ P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)) :=
    Real.one_le_rpow hL1 (by positivity)
  unfold bsf
  calc (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order ≤ 1 * Real.exp _ := by rw [one_mul]; exact hexp
    _ ≤ P.C₂ * Real.exp _ := mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
    _ ≤ P.C₂ * Real.exp _ * (cθ ^ (40 * P.ν)) ^ π.Gsb.order := le_mul_of_one_le_right (by positivity) hc1
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1'

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- Per-atom pattern arithmetic: `(∏_{v∈Q} x_v) y^a ≤ (1/2)^a ∏_{v∈s} φ_v` from `2 x_v y ≤ φ_v` (low atoms) and
`2y ≤ φ_v` (high atoms). -/
theorem pattern_prod_le_atom {ι : Type*} [DecidableEq ι] (s Q : Finset ι) (hQ : Q ⊆ s) (x : ι → ℝ) (y : ℝ)
    (hx : ∀ v ∈ Q, 0 ≤ x v) (hy : 0 ≤ y) (φ : ι → ℝ) (hlow : ∀ v ∈ Q, 2 * x v * y ≤ φ v)
    (hhigh : ∀ v ∈ s \ Q, 2 * y ≤ φ v) :
    (∏ v ∈ Q, x v) * y ^ s.card ≤ (1 / 2) ^ s.card * ∏ v ∈ s, φ v := by
  have e0 : ∏ v ∈ Q, x v = ∏ v ∈ s, (if v ∈ Q then x v else 1) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 hQ]
  have e1 : (1 / 2 : ℝ) ^ s.card = ∏ _v ∈ s, (1 / 2 : ℝ) := (Finset.prod_const _).symm
  have e2 : y ^ s.card = ∏ _v ∈ s, y := (Finset.prod_const _).symm
  rw [e0, e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v hv => ?_
  · by_cases hvQ : v ∈ Q
    · rw [ite_eq_left hvQ]; have := hx v hvQ; positivity
    · rw [ite_eq_right hvQ]; positivity
  by_cases hvQ : v ∈ Q
  · rw [ite_eq_left hvQ]; have := hlow v hvQ; linarith
  · rw [ite_eq_right hvQ]; have := hhigh v (Finset.mem_sdiff.2 ⟨hv, hvQ⟩); linarith

/-- Dropping factors `≥ 1`: `∏_S φ ≤ ∏_T φ` for `S ⊆ T`, `φ ≥ 0` on `S`, `φ ≥ 1` on `T \ S`. -/
theorem prod_le_prod_of_subset_one_le {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T) (φ : ι → ℝ)
    (h0 : ∀ v ∈ S, 0 ≤ φ v) (h1 : ∀ v ∈ T \ S, 1 ≤ φ v) : ∏ v ∈ S, φ v ≤ ∏ v ∈ T, φ v := by
  rw [← Finset.prod_sdiff hST]
  have hA : 1 ≤ ∏ v ∈ T \ S, φ v := by
    calc (1 : ℝ) = ∏ _v ∈ T \ S, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1
  exact le_mul_of_one_le_left (Finset.prod_nonneg h0) hA

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- `γ ≤ 1 + η` and `η ≤ γ` from `PieceSmall`. -/
theorem gamma_bounds {P : WTParams} (hs : PieceSmall P) : P.η ≤ P.γ ∧ P.γ ≤ 1 + P.η := by
  have hL : 1 < P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith
  constructor
  · by_contra h; push Not at h
    have := Real.one_lt_rpow hL (by linarith : 0 < -P.γ + P.η)
    linarith [hs.cap_le]
  · by_contra h; push Not at h
    have h1 : P.L ^ (-P.γ + P.η) < P.L ^ (-1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hL (by linarith)
    have h2 : P.L ^ (-1 : ℝ) = P.L⁻¹ := Real.rpow_neg_one _
    have h3 := hs.cap
    have : 0 < P.L⁻¹ := inv_pos.2 hL0
    linarith

/-- **The selected pointwise bound with per-atom scales** (o73 Prop 20.1 at fixed `ξ`; finding F-C5b-1): the selected
atom `v` carries the filter `chiDN(Ω_v/M_v)` at its own scale `M_v ≥ L`. The regimes are split per atom: in the
normal regime only the atoms with `M_v > L^{18c}` are expanded (the others have `φ_v ≥ 1`); in the tiny regime only
the atoms with `μ M_v ≥ 2` are (the others have `κ φ_v ≥ 1`). -/
theorem point_bound_atom {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMK P.d R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFull π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt c e h f))
    (sel : Finset (GBranch π.Gsb.tree)) (M : GBranch π.Gsb.tree → ℝ) (hM : ∀ v ∈ sel, P.L ≤ M v)
    (hsel : ∀ v ∈ sel, π.fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M v, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    (hone : ∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') :
    ‖splicedKernelMK π.Gsb (π.dataMK tt c e h f) P.L P.γ P.η P.δ base roots‖ ≤
      bsf P cθ π * ∏ v ∈ sel, (P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)) := by
  set D := π.dataMK tt c e h f with hDdef
  have hD : SplicedAmplitudeBounds π.Gsb D.toSplicedKernelData := hamp
  have hL2 : 2 ≤ P.L := hs.L_ge
  have hL0 : 0 < P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have hM0 : ∀ v ∈ sel, 0 < M v := fun v hv => by linarith [hM v hv]
  have hδ0 := hs.delta_pos
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set φ : GBranch π.Gsb.tree → ℝ := fun v =>
    P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) with hφ
  have hΛ : 1 ≤ P.L ^ (71 * (P.d : ℝ) - 14) := Real.one_le_rpow hL1 (by linarith)
  have hw : ∀ v, 1 ≤ (1 + |f v|) ^ (1 / 18 : ℝ) := fun v =>
    Real.one_le_rpow (by linarith [abs_nonneg (f v)]) (by norm_num)
  have hMp : ∀ v ∈ sel, 0 ≤ M v ^ (-(1 / 18 : ℝ)) := fun v hv => Real.rpow_nonneg (hM0 v hv).le _
  have hφ0 : ∀ v ∈ sel, 0 ≤ φ v := fun v hv => by
    simp only [hφ]; have := hw v; have := hMp v hv; positivity
  have hφM : ∀ v ∈ sel, M v ^ (-(1 / 18 : ℝ)) ≤ φ v := fun v hv => by
    simp only [hφ]
    have := hMp v hv
    calc M v ^ (-(1 / 18 : ℝ)) = 1 * M v ^ (-(1 / 18 : ℝ)) * 1 := by ring
      _ ≤ _ := by gcongr; exact hw v
  have hb0 := bsf_nonneg hs hcθ π
  set cc : ℝ := 49 * (P.d : ℝ) - 35 with hcc
  -- an atom at a scale `M_v ≤ L^{18c}` needs no gain
  have hφ1 : ∀ v ∈ sel, M v ≤ P.L ^ (18 * cc) → 1 ≤ φ v := fun v hv hA => by
    have h1 : P.L ^ (-cc) ≤ M v ^ (-(1 / 18 : ℝ)) := by
      calc P.L ^ (-cc) = (P.L ^ (18 * cc)) ^ (-(1 / 18 : ℝ)) := by
            rw [← Real.rpow_mul hL0.le]; congr 1; ring
        _ ≤ M v ^ (-(1 / 18 : ℝ)) := Real.rpow_le_rpow_of_nonpos (hM0 v hv) hA (by norm_num)
    have h2 : 1 ≤ P.L ^ (71 * (P.d : ℝ) - 14) * P.L ^ (-cc) := by
      rw [← Real.rpow_add hL0]; exact Real.one_le_rpow hL1 (by rw [hcc]; linarith)
    have h3 : 0 ≤ P.L ^ (-cc) := Real.rpow_nonneg hL0.le _
    have := hM0 v hv
    simp only [hφ]
    calc (1 : ℝ) ≤ P.L ^ (71 * (P.d : ℝ) - 14) * P.L ^ (-cc) * 1 := by rw [mul_one]; exact h2
      _ ≤ _ := by gcongr; exact hw v
  -- common facts
  have hP := hπ.plain
  set μ : ℝ := P.δ * P.L ^ (2 * P.γ) with hμ
  have hsel' : ∀ v ∈ sel, D.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧
      ∀ u, ψ u = (chiDN u : ℂ) := hsel
  have hord : sel.card ≤ π.Gsb.order := by
    rw [← WaveTurbulence.Ladder.card_branch_eq π.Gsb]; exact Finset.card_le_univ _
  -- the patterns at a subset `S ⊆ sel` of the selected atoms
  have hpatS : ∀ S ⊆ sel, ∀ Bnd : ℝ, 0 ≤ Bnd →
      (∀ D', ModOK S D D' → ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤ Bnd) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ Q ⊆ S, (∀ v ∈ S \ Q, μ * M v / 4 ≤ |f v|) →
        (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * Bnd ≤ (1 / 2) ^ S.card * B) →
      ‖splicedKernelMK π.Gsb D P.L P.γ P.η P.δ base roots‖ ≤ B := by
    intro S hS Bnd hB0 hBnd B hB0' hQB
    have hSone : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b := fun a ha b hb => hone a (hS ha) b (hS hb)
    have hSsel : ∀ v ∈ S, D.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧
        ∀ u, ψ u = (chiDN u : ℂ) := fun v hv => hsel' v (hS hv)
    have hSM : ∀ v ∈ S, 0 < M v := fun v hv => hM0 v (hS hv)
    have hone_pat : ∀ Q ∈ S.powerset, ‖splicedKernelMK π.Gsb
        (modData D D.fix (patInd P.L P.γ P.δ D.frequency S Q)) P.L P.γ P.η P.δ base roots‖ ≤
        (1 / 2) ^ S.card * B := by
      intro Q hQ
      have hQs : Q ⊆ S := Finset.mem_powerset.1 hQ
      by_cases hz : ∃ v ∈ S \ Q, |D.frequency v| < P.δ * P.L ^ (2 * P.γ) * M v / 4
      · obtain ⟨v, hv, hsm⟩ := hz
        rw [pattern_zero hP D hD hL0 P.γ P.η P.δ hδ0.le base roots S Q M (fun v hv => (hSsel v hv).2) hv
          (hSM v (Finset.mem_sdiff.1 hv).1) hsm, norm_zero]
        exact mul_nonneg (by positivity) hB0'
      · push Not at hz
        exact (pattern_bound hP D hD hL0 P.γ P.η P.δ hδ0 base roots S Q hQs hSone M hSM hSsel Bnd hB0
          hBnd).trans (hQB Q hQs hz)
    rw [kernel_eq_sum_patterns hP D hD hL0 P.γ P.η P.δ base roots D.frequency S]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hone_pat).trans ?_)
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, ← mul_assoc]
    push_cast
    rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, one_mul]
  have hγb := gamma_bounds hs
  have hγ0 : 0 ≤ P.γ := le_trans hs.eta_pos.le hγb.1
  have hL2γ : 1 ≤ P.L ^ (2 * P.γ) := Real.one_le_rpow hL1 (by linarith)
  have hδμ : P.δ ≤ μ := by rw [hμ]; nlinarith
  have hp0 : 0 ≤ ∏ v ∈ sel, φ v := Finset.prod_nonneg hφ0
  have hx0 : ∀ v ∈ sel, 0 ≤ 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4) := fun v hv => by
    have := Real.rpow_pos_of_pos hL0 (2 * P.γ); have := hM0 v hv; positivity
  by_cases hB : 4 * P.L ^ (-(18 * cc)) ≤ μ
  · -- normal regime: the gates; only the atoms with `M_v > L^{18c}` are expanded
    set S := sel.filter (fun v => P.L ^ (18 * cc) < M v) with hSdef
    have hS : S ⊆ sel := Finset.filter_subset _ _
    set y : ℝ := P.L ^ (22 * (P.d : ℝ) + 16) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hL0.le _
    have hBnd : ∀ D', ModOK S D D' → ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤
        bsf P cθ π * y ^ S.card := by
      intro D' hD'
      have := kernel_bound_mod hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt c e h f hamp S D'
        hD'
      refine this.trans (le_of_eq ?_)
      have e : P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) +
          (22 * P.d + 16) * (S.card : ℝ)) = P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) +
          2 * (π.surv.m : ℝ)) * y ^ S.card := by
        rw [Real.rpow_add hL0, hy, ← Real.rpow_mul_natCast hL0.le]
      unfold bsf
      rw [e]
      ring
    have hSφ : ∏ v ∈ S, φ v ≤ ∏ v ∈ sel, φ v :=
      prod_le_prod_of_subset_one_le hS φ (fun v hv => hφ0 v (hS hv)) fun v hv => by
        obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
        exact hφ1 v hv1 (not_lt.1 fun hlt => hv2 (Finset.mem_filter.2 ⟨hv1, hlt⟩))
    refine hpatS S hS _ (mul_nonneg hb0 (pow_nonneg hy0 _)) hBnd _ (mul_nonneg hb0 hp0) fun Q hQs hhigh => ?_
    have hprod := pattern_prod_le_atom S Q hQs (fun v => 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) y
      (fun v hv => hx0 v (hS (hQs hv))) hy0 φ (fun v hv => ?_) (fun v hv => ?_)
    · have hSp : 0 ≤ ∏ v ∈ S, φ v := Finset.prod_nonneg fun v hv => hφ0 v (hS hv)
      calc (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * (bsf P cθ π * y ^ S.card)
          = bsf P cθ π * ((∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * y ^ S.card) := by ring
        _ ≤ bsf P cθ π * ((1 / 2) ^ S.card * ∏ v ∈ S, φ v) := mul_le_mul_of_nonneg_left hprod hb0
        _ ≤ bsf P cθ π * ((1 / 2) ^ S.card * ∏ v ∈ sel, φ v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSφ (by positivity)) hb0
        _ = (1 / 2) ^ S.card * (bsf P cθ π * ∏ v ∈ sel, φ v) := by ring
    · have hvS := hQs hv
      have hvsel := hS hvS
      have hMv : P.L ^ (18 * cc) < M v := (Finset.mem_filter.1 hvS).2
      have := atom_low_normal hL2 hd' hB hMv
      have := hMp v hvsel
      calc 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * y
          ≤ P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) := by assumption
        _ ≤ φ v := by
          simp only [hφ]
          calc P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ))
              = P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr; exact hw v
    · exact atom_high_normal hL2 hd' hB (hM0 v (hS (Finset.mem_sdiff.1 hv).1)) (hhigh v hv)
  · -- tiny regime: the trivial bound; only the atoms with `μ M_v ≥ 2` are expanded
    push Not at hB
    have hδL : P.δ ≤ P.L ^ (-(12 * (P.d : ℝ) + 14)) := by
      have h1 : 4 * P.L ^ (-(18 * cc)) ≤ P.L ^ (-(12 * (P.d : ℝ) + 14)) := by
        have h2 : (4 : ℝ) ≤ P.L ^ (18 * cc - (12 * (P.d : ℝ) + 14)) := by
          calc (4 : ℝ) ≤ P.L ^ (2 : ℝ) := by
                rw [show (P.L ^ (2 : ℝ)) = P.L ^ (2 : ℕ) by norm_cast]; nlinarith
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hcc]; linarith)
        calc 4 * P.L ^ (-(18 * cc)) ≤ P.L ^ (18 * cc - (12 * (P.d : ℝ) + 14)) * P.L ^ (-(18 * cc)) := by
              gcongr
          _ = P.L ^ (-(12 * (P.d : ℝ) + 14)) := by rw [← Real.rpow_add hL0]; congr 1; ring
      linarith
    set κ : ℝ := 32 * P.δ ^ (-(1 / 18 : ℝ)) with hκ
    have hκ1 : 1 ≤ κ := by
      have : 1 ≤ P.δ ^ (-(1 / 18 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hs.delta_le (by norm_num)
      linarith
    set T : ℝ := ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) with hT
    have hT0 : 0 ≤ T := by positivity
    have hcore : T * κ ^ π.Gsb.order ≤ bsf P cθ π := by
      have hcoup : ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ = P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ)) := by
        unfold coupling
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hb : π.Gsb.molecule.bonds.card ≤ 2 * π.Gsb.order := by have := hπ.bond_count; omega
      have hRo : (R : ℝ) ≤ 2 * π.Gsb.order := by have := hπ.bond_count; exact_mod_cast (by omega : R ≤ 2 * π.Gsb.order)
      have hgsb : (π.gsb : ℝ) ≤ π.Gsb.order := by
        have := WaveTurbulence.Represents.totalIncoherency_le_atoms hπ.molecule π.ladders π.layer
        rw [hπ.atom_count] at this; exact_mod_cast this
      have hρ : (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) ≤ 2 * π.Gsb.order := by
        have h1 := WaveTurbulence.Represents.rho_le_atoms hπ.molecule
        rw [hπ.atom_count] at h1
        have h2 : π.Cs.hinges.card ≤ π.Gsb.order := by
          rw [← WaveTurbulence.Ladder.card_branch_eq π.Gsb]; exact Finset.card_le_univ _
        have : π.Gsb.molecule.rho + π.Cs.hinges.card ≤ 2 * π.Gsb.order := by omega
        exact_mod_cast this
      have h1 := tiny_core (γ := P.γ) (n := π.Gsb.order) (b := π.Gsb.molecule.bonds.card) hL2 hd' hδ0 hδL
        hs.nu_pos.le
        hs.nu_small (by linarith [hγb.2, hs.eta_le]) hb P.d rfl
      have h2 := bsf_lower hs hcθ π hgsb hρ hRo
      rw [hT, hcoup]
      calc (P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ))) ^ π.Gsb.order *
            (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) * κ ^ π.Gsb.order ≤
          (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order := h1
        _ ≤ _ := h2
    have hκord : κ ^ sel.card ≤ κ ^ π.Gsb.order := pow_le_pow_right₀ hκ1 hord
    have hTD : ∀ S : Finset (GBranch π.Gsb.tree), ∀ D', ModOK S D D' →
        ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤ T := by
      intro S D' hD'
      have hdat : D'.toSplicedKernelData = D.toSplicedKernelData := hD'.data
      obtain ⟨g, hg, -, hi⟩ := hD'.ind
      refine norm_kernel_le_trivial hP D' (by rw [hdat]; exact hD) (fun a q hq u => ?_) (fun k => ?_) hL0
        P.γ P.η P.δ base roots
      · have hq' : π.filt a = some q := by
          have h2 := hD'.filt; rw [h2] at hq; exact hq
        exact (hπ.filt_ok a q hq').2.2.1 u
      · rw [hi k]; have h1 := hπ.ind_ok k
        exact ⟨mul_nonneg h1.1 (hg k).1, (mul_le_mul h1.2 (hg k).2 (hg k).1 zero_le_one).trans_eq (one_mul 1)⟩
    set S := sel.filter (fun v => 2 ≤ μ * M v) with hSdef
    have hS : S ⊆ sel := Finset.filter_subset _ _
    have hκφ0 : ∀ v ∈ sel, 0 ≤ κ * φ v := fun v hv => mul_nonneg (by linarith) (hφ0 v hv)
    have hκS : ∏ v ∈ S, κ * φ v ≤ κ ^ π.Gsb.order * ∏ v ∈ sel, φ v := by
      calc ∏ v ∈ S, κ * φ v ≤ ∏ v ∈ sel, κ * φ v :=
            prod_le_prod_of_subset_one_le hS (fun v => κ * φ v) (fun v hv => hκφ0 v (hS hv)) fun v hv => by
              obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
              have hC : μ * M v < 2 := not_le.1 fun hle => hv2 (Finset.mem_filter.2 ⟨hv1, hle⟩)
              have := atom_tiny_small hδ0 hδμ (hM0 v hv1) hC
              calc (1 : ℝ) ≤ M v ^ (-(1 / 18 : ℝ)) * κ := this
                _ ≤ κ * φ v := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hφM v hv1) (by linarith)
        _ = κ ^ sel.card * ∏ v ∈ sel, φ v := by rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ κ ^ π.Gsb.order * ∏ v ∈ sel, φ v := mul_le_mul_of_nonneg_right hκord hp0
    refine hpatS S hS T hT0 (hTD S) _ (mul_nonneg hb0 hp0) fun Q hQs hhigh => ?_
    have hprod := pattern_prod_le_atom S Q hQs (fun v => 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) 1
      (fun v hv => hx0 v (hS (hQs hv))) zero_le_one (fun v => κ * φ v) (fun v hv => ?_) (fun v hv => ?_)
    · rw [one_pow, mul_one] at hprod
      have hκ0 : 0 ≤ κ ^ π.Gsb.order := pow_nonneg (by linarith) _
      calc (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * T
          ≤ ((1 / 2) ^ S.card * ∏ v ∈ S, κ * φ v) * T := mul_le_mul_of_nonneg_right hprod hT0
        _ ≤ ((1 / 2) ^ S.card * (κ ^ π.Gsb.order * ∏ v ∈ sel, φ v)) * T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκS (by positivity)) hT0
        _ = (1 / 2) ^ S.card * (T * κ ^ π.Gsb.order) * ∏ v ∈ sel, φ v := by ring
        _ ≤ (1 / 2) ^ S.card * bsf P cθ π * ∏ v ∈ sel, φ v :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore (by positivity)) hp0
        _ = (1 / 2) ^ S.card * (bsf P cθ π * ∏ v ∈ sel, φ v) := by ring
    · have hvS := hQs hv
      have hvsel := hS hvS
      have hC : 2 ≤ μ * M v := (Finset.mem_filter.1 hvS).2
      have := atom_low_tiny hδ0 hδμ hC
      calc 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * 1
          = 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) := mul_one _
        _ ≤ M v ^ (-(1 / 18 : ℝ)) * κ := this
        _ ≤ κ * φ v := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hφM v hvsel) (by linarith)
    · have hvsel := hS (Finset.mem_sdiff.1 hv).1
      have := atom_high_tiny hδ0 hδμ (hM0 v hvsel) (hhigh v hv)
      have := hMp v hvsel
      calc 2 * (1 : ℝ) = 2 := mul_one _
        _ ≤ M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) * κ := by assumption
        _ ≤ κ * φ v := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            simp only [hφ]
            calc M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)
                = 1 * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) := by ring
              _ ≤ _ := by gcongr

/-- **The selected pointwise bound** (o73 Prop 20.1 at fixed `ξ`), all selected atoms at one scale `M₂`
(`point_bound_atom` at `M ≡ M₂`). -/
theorem point_bound {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMK P.d R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFull π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt c e h f))
    (sel : Finset (GBranch π.Gsb.tree)) (M₂ : ℝ) (hM : P.L ≤ M₂)
    (hsel : ∀ v ∈ sel, π.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M₂, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    (hone : ∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') :
    ‖splicedKernelMK π.Gsb (π.dataMK tt c e h f) P.L P.γ P.η P.δ base roots‖ ≤
      bsf P cθ π * ∏ v ∈ sel, (P.L ^ (71 * (P.d : ℝ) - 14) * M₂ ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)) :=
  point_bound_atom hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt c e h f hamp sel (fun _ => M₂)
    (fun _ _ => hM) hsel hone

end WaveTurbulence.Flower.SelRes
