/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplFinal
public import WaveTurbulence.Foundations.Flower.ProtRT.TreeBall
public import WaveTurbulence.Foundations.Flower.ProtRT.RT1T
public import WaveTurbulence.Foundations.Flower.ProtRT.RT1ATrace
public import WaveTurbulence.Foundations.Flower.ProtPin.GateAllF

/-! # RT-GATE: `MkSlotsO.RootTraceGate` from the both-pinned couple bound

`rootTraceGate_of`: `RootTraceGate = WTPrefix RootTraceBoundAt` given `RtBoth` (both roots pinned; `rt2_both`'s
statement). The prefix is D3's (`protBoundGate_ofF`: FILT-GATE, `CohFlat`, FILT-COH; `C₁` the maximum of their
constants; `δ₀ ≤ C₁^{-2}`, so `δ C₁ ≤ 1`), with `L₀` large for the one-cut size conditions of the three per-output
constants (trees at `η`, couples at `η` and at `1/4`). Clause (i): `rt_tree_ball` at `θ = η`. Clause (ii):
`rt_cpl_ball` at `(θ, c') = (η, 0)` and `(1/4, 4d)`, `RtOne` from `rt1t_one_of_a` and `rt1a_trace`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **`RtOne`** for every weight and loss (the (a+) slice by `rt1a_trace`, the rest by `rt1t_one_of_a`). -/
theorem rt_one {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') : ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOne θ c' Ct :=
  rt1t_one_of_a (fun _ _ h0 h1 hc => rt1a_trace h0 h1 hc) hθ0 hθ1 hc'

/-- A local output extension with a constant at least `1`. -/
theorem rt_loe_one (d : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) : ∃ CL : ℝ, 1 ≤ CL ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom d) (F : (Fin r → ℝ) → Mom d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * d)) * X := by
  obtain ⟨CL, hCL, hLOE⟩ := ProtOps.localOutputExtension d θ hθ
  refine ⟨max CL 1, le_max_right _ _, fun L hL r B b₀ c₀ F X hX => (hLOE L hL B b₀ c₀ F X hX).trans ?_⟩
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)

/-- **`RootTraceGate`** from the both-pinned couple bound. -/
theorem rootTraceGate_of
    (hBoth : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → (∃ Ct₁ : ℝ, 0 ≤ Ct₁ ∧ RtOne θ 0 Ct₁) → ∃ Ct : ℝ, 0 ≤ Ct ∧ RtBoth θ Ct) :
    MkSlotsO.RootTraceGate := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  obtain ⟨η₃, hη₃, HF⟩ := FiltCoh.filtCoherentBoundGate d hd γ hγ
  -- the weight `1/4`
  obtain ⟨Cq1, hCq1, hq1⟩ := rt_one (θ := 1 / 4) (c' := 4 * d) (by norm_num) le_rfl (by positivity)
  obtain ⟨Cq2, hCq2, hq2⟩ := hBoth (1 / 4) (by norm_num) le_rfl (rt_one (by norm_num) le_rfl le_rfl)
  obtain ⟨CL4, hCL4, hLOE4⟩ := rt_loe_one d (θ := 1 / 4) (by norm_num)
  refine ⟨min (min (min η₁ η₂) η₃) (1 / 4), lt_min (lt_min (lt_min hη₁ hη₂) hη₃) (by norm_num),
    fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ :=
    ⟨hη.1, hη.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))⟩
  have hη2 : η ∈ Ioc 0 η₂ :=
    ⟨hη.1, hη.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))⟩
  have hη3 : η ∈ Ioc 0 η₃ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  have hη0 : 0 ≤ η := hη.1.le
  -- the weight `η`
  obtain ⟨CrT, hCrT, hT⟩ := rt_tree_ball hη0 hη4
  obtain ⟨Cη1, hCη1, hη1'⟩ := rt_one hη0 hη4 le_rfl
  obtain ⟨Cη2, hCη2, hη2'⟩ := hBoth η hη0 hη4 ⟨Cη1, hCη1, hη1'⟩
  obtain ⟨CLη, hCLη, hLOEη⟩ := rt_loe_one d hη0
  obtain ⟨C₁a, hC₁a, ν₁, hν₁, HI1⟩ := HI η hη1 φin hφ τs hτs φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, HC1⟩ := HC η hη2 φin hφ τs hτs φ hW
  obtain ⟨C₁c, hC₁c, ν₃, hν₃, HF1⟩ := HF η hη3 φin hφ τs hτs φ hW
  set C₁ := max (max C₁a C₁b) C₁c with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_of_le_left (le_max_of_le_left hC₁a)
  refine ⟨C₁, hC₁1, min (min ν₁ ν₂) ν₃, lt_min (lt_min hν₁ hν₂) hν₃, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, HI2⟩ := HI1 ν ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  obtain ⟨δ₂, hδ₂, HC2⟩ := HC1 ν ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨δ₃, hδ₃, HF2⟩ := HF1 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  have hC₁p : 0 < C₁ ^ 2 := by positivity
  refine ⟨min (min (min δ₁ δ₂) δ₃) (1 / C₁ ^ 2), lt_min (lt_min (lt_min hδ₁ hδ₂) hδ₃) (by positivity),
    fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, -, HI3⟩ := HI2 δ ⟨hδ.1, hδ.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))⟩ D hD hτD
  obtain ⟨C₂b, -, L₂, -, HC3⟩ := HC2 δ ⟨hδ.1, hδ.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))⟩ D hD hτD
  obtain ⟨C₂c, -, L₃, -, HF3⟩ := HF2 δ ⟨hδ.1, hδ.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩ D hD hτD
  have hδC2 : δ * C₁ ^ 2 ≤ 1 := by
    have h := hδ.2.trans (min_le_right _ _)
    rw [le_div_iff₀ hC₁p] at h
    exact h
  have hδC : δ * C₁ ≤ 1 := by
    have : δ * C₁ ≤ δ * C₁ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hδ.1.le
    linarith
  set Crη := rtCr η Cη1 Cη2 d with hCrη
  set Crq := rtCr (1 / 4) Cq1 Cq2 d with hCrq
  have hCrη0 : 0 ≤ Crη := by have := rtCr_one_le (θ := η) hCη1 hCη2 d; linarith
  have hCrq0 : 0 ≤ Crq := by have := rtCr_one_le (θ := 1 / 4) hCq1 hCq2 d; linarith
  set Kb := termK CLη CrT d + termK CLη Crη d + termK CL4 Crq d + 1 with hKb
  have hKT := termK_nonneg (CL := CLη) (by linarith) hCrT d
  have hKη := termK_nonneg (CL := CLη) (by linarith) hCrη0 d
  have hKq := termK_nonneg (CL := CL4) (by linarith) hCrq0 d
  refine ⟨1, le_rfl, max (max (max L₁ L₂) L₃) (max 2 (Kb ^ (1 / (2 - 2 * γ)))),
    le_max_of_le_right (le_max_left _ _), fun L hL => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hL₃ : L₃ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLb : Kb ^ (1 / (2 - 2 * γ)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have K : AlphaConsts ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ C₁a C₂a C₁b C₂b :=
    ⟨HI3 L hL₁, HC3 L hL₂, by linarith, by linarith, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), hδ.1.le, hL1, hη.1.le, hη4, hd⟩
  have hFC : TcFC (⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ : WTParams) :=
    ⟨C₁c, C₂c, HF3 L hL₃, by linarith, le_max_right _ _⟩
  have hbT := big_of_large hKT (by linarith) hγ.2 hL1 hLb hδ.1.le hδC2
  have hbη := big_of_large hKη (by linarith) hγ.2 hL1 hLb hδ.1.le hδC2
  have hbq := big_of_large hKq (by linarith) hγ.2 hL1 hLb hδ.1.le hδC2
  intro p hp n hn s hps hsp
  refine ⟨?_, ?_⟩
  · -- (i) trees
    intro X LG hwf hsz hdec hne hle hroot q' _hq' hlone hamb S ω cω hpres H B hH b₀ c₀
    exact hT K hFC (pieceLoss_eta rfl) hC₁1 (by linarith) hLOEη hbT hp hn hps hsp X LG hwf hsz hdec hne hle hroot
      hlone hamb S ω cω hpres H B hH b₀ c₀
  · -- (ii) couples
    intro Rt θ hRt hθ Q LG hwf hsz hdec hle hpin q q' hq hq' hr0 hr1 hamb S ω cω hpres H B hH b₀ c₀
    rcases hθ with hθη | ⟨hθq, hnb⟩
    · subst hθη
      exact rt_cpl_ball hη0 hCη1 hCη2 hη1' hη2' K hFC hC₁1 (pieceLoss_eta rfl) hδC (by linarith) hLOEη hbη hp hn
        hps hsp Rt hRt (fun _ => ⟨pieceLoss_eta rfl, rfl⟩) Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω
        hpres H B hH b₀ c₀
    · subst hθq
      exact rt_cpl_ball (by norm_num) hCq1 hCq2 hq1 hq2 K hFC hC₁1 (Or.inr ⟨rfl, rfl⟩) hδC (by linarith) hLOE4 hbq
        hp hn hps hsp Rt hRt (fun h => absurd h hnb) Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω hpres
        H B hH b₀ c₀

end WaveTurbulence.Flower.ProtRT
