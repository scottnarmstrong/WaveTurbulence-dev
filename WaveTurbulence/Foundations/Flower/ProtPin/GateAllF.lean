/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateF

/-! # D3 PROT-PIN: the gate assembly with FILT-COH's multi-layer coherent gate in the prefix

`protBoundGate_of`: `ProtBoundGate` from the slices of (P4) with a nonempty prefix, (P7) and the cap couples (each as
`∀ θ ∈ [0, 1/4], ∃ Cr, CfgU θ Cr sel`); the other slices are proved (`cfgU_root_tree`, `cfgU_trace_tree`,
`cfgU_rootTerm_tree`, `cfgU_pen_tree`), `none`/`term` by `ntAt_of`. Prefix: that of `protBoundNTGate`, with
`L₀ ≥ Kb^{1/(2−2γ)}` and `L₀ ≥ Kb₂^{1/(5−4γ)}` for the one- and two-cut size conditions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **`ProtBoundGate` from the three remaining slices.** -/
theorem protBoundGate_ofF
    (hPre : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr selPenPrefix)
    (hTC : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selTChild)
    (hCap : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 → ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selCap) : ProtBoundGate := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  obtain ⟨η₃, hη₃, HF⟩ := FiltCoh.filtCoherentBoundGate d hd γ hγ
  obtain ⟨Cr4, hCr4, hperk4⟩ := exists_termStarPerkU (θ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨CL4, hCL4, hLOE4⟩ := ProtOps.localOutputExtension d (1 / 4) (by norm_num)
  refine ⟨min (min (min η₁ η₂) η₃) (1 / 4), lt_min (lt_min (lt_min hη₁ hη₂) hη₃) (by norm_num),
    fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ :=
    ⟨hη.1, hη.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))⟩
  have hη2 : η ∈ Ioc 0 η₂ :=
    ⟨hη.1, hη.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))⟩
  have hη3 : η ∈ Ioc 0 η₃ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  have hη0 : 0 ≤ η := hη.1.le
  obtain ⟨Crη, hCrη, hperkη⟩ := exists_termStarPerkU (θ := η) hη0 hη4
  obtain ⟨CLη, hCLη, hLOEη⟩ := ProtOps.localOutputExtension d η hη0
  -- the slices at `θ = η`
  obtain ⟨Ca, ha0, hUa⟩ := cfgU_root_tree hη0 hη4
  obtain ⟨Cb, hb0, hUb⟩ := cfgU_trace_tree hη0 hη4
  obtain ⟨Cc, hc0, hUc⟩ := cfgU_rootTerm_tree hη0 hη4
  obtain ⟨Cd, hd0, hUd⟩ := cfgU_pen_tree hη0 hη4
  obtain ⟨Ce, he0, hUe⟩ := hPre η hη0 hη4
  obtain ⟨Cf, hf0, hUf⟩ := hTC η hη0 hη4
  obtain ⟨Cg, hg0, hUg⟩ := hCap η hη0 hη4
  set CrU : ℝ := Ca + Cb + Cc + Cd + Ce + Cf + Cg with hCrU
  have hA : CfgUF η CrU (fun w _ _ cfg => w = 1 ∧ cfg = .root) := CfgU.toF (CfgU.mono hUa (by linarith))
  have hB : CfgUF η CrU (fun w _ X cfg => w = 1 ∧ cfg = .trace ∧ X ≠ .nil) :=
    CfgU.toF (CfgU.mono hUb (by linarith))
  have hC : CfgUF η CrU (fun w _ _ cfg => w = 1 ∧ cfg = .rootTerm) := CfgU.toF (CfgU.mono hUc (by linarith))
  have hD : CfgUF η CrU (fun w _ X cfg => w = 1 ∧ cfg = .penTerm ∧ selPenNoPrefix X) :=
    CfgU.toF (CfgU.mono hUd (by linarith))
  have hE : CfgUF η CrU selPenPrefix := CfgU.toF (CfgU.mono hUe (by linarith))
  have hF : CfgUF η CrU selTChild := CfgUF.mono hUf (by linarith)
  have hG : CfgUF η CrU selCap := CfgUF.mono hUg (by linarith)
  have hU : CfgUF η CrU selRest :=
    CfgUF.weaken (CfgUF.or (CfgUF.or (CfgUF.or (CfgUF.or (CfgUF.or hA hB) hC) hD) hE) (CfgUF.or hF hG))
      fun p w LG X cfg hsh hval hs => selRest_cover p w LG X cfg hsh hval hs
  have hCrU0 : 0 ≤ CrU := by linarith
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
  have hδC : δ * C₁ ^ 2 ≤ 1 := by
    have h := hδ.2.trans (min_le_right _ _)
    rw [le_div_iff₀ hC₁p] at h
    exact h
  set Kb := termK CLη Crη d + termK CL4 Cr4 d + termK CLη CrU d + 1 with hKb
  set Kb2 := twoK CLη CrU d + 1 with hKb2
  have hKη := termK_nonneg hCLη hCrη d
  have hK4 := termK_nonneg hCL4 hCr4 d
  have hKU := termK_nonneg hCLη hCrU0 d
  have hK2U := twoK_nonneg hCLη hCrU0 d
  refine ⟨1, le_rfl, max (max (max L₁ L₂) L₃) (max 2 (max (Kb ^ (1 / (2 - 2 * γ))) (Kb2 ^ (1 / (5 - 4 * γ))))),
    le_max_of_le_right (le_max_left _ _), fun L hL => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hL₃ : L₃ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLb : Kb ^ (1 / (2 - 2 * γ)) ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLb2 : Kb2 ^ (1 / (5 - 4 * γ)) ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1 : 1 ≤ L := by linarith
  have K : AlphaConsts ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ C₁a C₂a C₁b C₂b :=
    ⟨HI3 L hL₁, HC3 L hL₂, by linarith, by linarith, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), hδ.1.le, hL1, hη.1.le, hη4, hd⟩
  have hFC : FiltCoherentBoundAt { (⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ : WTParams) with C₁ := C₁c, C₂ := C₂c } :=
    HF3 L hL₃
  have hNT := ntAt_of K hCrη hCLη hCr4 hCL4 hperkη hperk4 hLOEη hLOE4
    (big_of_large hKη (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)
    (big_of_large hK4 (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)
  exact protBoundAt_ofF K hFC (by linarith) (le_max_right _ _) hNT hCLη hC₁1 hLOEη (big_of_large hKU (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)
    (big2_of_large hK2U (by linarith) hγ.2 hL1 hLb2 hδ.1.le hδC) hU

end WaveTurbulence.Flower.ProtPin
