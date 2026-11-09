/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmProp96b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Proved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Main
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # H-ASM (packet L6-HASM): Proposition 9.6 for the components of the run, `0 < γ ≤ 1/2`

Low-range replacement (PLAN-L6 §3e "Prop 9.6 → `prop96_low_proved`") of main's `FinalCountAsm.final_component_bound`
(`FinalCount/AsmProp96b.lean`, `γ ∈ (1/2, 1)`, `hsm2`), which main's REG chain (`AsmTerm15c.unt_comp_bound`) and the
LOW chain (`LowChain40.unt_comp_boundL`) apply to the final components of the run.
* `FinalDec.toLow`: the ported `FinalDec` (G3FinalCopy; `vineLG` over the enlarged family `IsVineEnl`) is P96's
  `FinalDecLow` (vine-LG over `𝒱_γ`), with G8's class map `g8Cls`, for `γ ≤ 1/2` (`IsVineGamma γ ↔ IsVineEnl` there).
  Field-wise copy of main's `G8Copy.FinalDec.toG8` (AsmProp96).
* `final_component_bound_low`: main's statement with `γ ∈ (0, 1/2]`, without `hsm2`, the ported `FinalDec`, proved by
  `prop96_low_proved`, with N2 Lemma 5.2 from L3 (`TVine.Struct.Drawn.drawnTVine`, proved). -/
@[expose] public section
set_option autoImplicit false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u v

section transfer
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}
  {cls : V → G8Copy.Cls}

/-- The ported `FinalDec` gives P96's `FinalDecLow` at `γ ≤ 1/2` (copy of main's `G8Copy.FinalDec.toG8`; `vineLG`
read through `IsVineGamma γ = IsVineEnl` for `γ ≤ 1/2`). -/
theorem FinalDec.toLow {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop} (hγ : γ ≤ 1 / 2)
    (h : FinalDec M cls L γ η Adm) :
    WaveTurbulence.GammaLow.FinalCount.FinalDecLow M (fun a => g8Cls (cls a)) L γ η Adm where
  labRange := fun a ha hα => by rw [g8Cls_lab]; exact h.labRange a ha (g8Cls_isAlpha.1 hα)
  kapVals := fun a ha hα => by rw [g8Cls_kap]; exact h.kapVals a ha (g8Cls_isAlpha.1 hα)
  epsLG := fun κ hκ a ha he => h.epsLG κ hκ a ha (g8Cls_isEps.1 he)
  alphaGap := fun κ hκ a ha hα x y hx hy hxy => by
    rw [g8Cls_lab]; exact h.alphaGap κ hκ a ha (g8Cls_isAlpha.1 hα) x y hx hy hxy
  alphaSG := fun κ hκ a ha hα => h.alphaSG κ hκ a ha (g8Cls_isAlpha.1 hα)
  betaGap := fun κ hκ a ha hb => h.betaGap κ hκ a ha (g8Cls_isBeta.1 hb)
  vineLG := fun hv => h.vineLG (by
    rcases hv with ⟨j₁, j₂, hX⟩ | h2
    · refine Or.inl ⟨j₁, j₂, ?_⟩
      rcases hX with ⟨-, hE⟩ | ⟨hlt, -⟩
      · exact hE
      · exact absurd hγ (not_le.mpr hlt)
    · exact Or.inr h2)
  noBetaCut := h.noBetaCut
  iota := fun κ hκ v₁ h1 v₂ h2 v₃ h3 hne hα1 hα2 hβ3 hk x₁ y₁ x₂ y₂ x₃ y₃ hx1 hy1 hxy1 hx2 hy2 hxy2 hx3 hy3 hxy3 g1 g2 g3 hs => by
    have := h.iota κ hκ v₁ h1 v₂ h2 v₃ h3 hne (g8Cls_isAlpha.1 hα1) (g8Cls_isAlpha.1 hα2) (g8Cls_isBeta.1 hβ3)
      (by rw [← g8Cls_kap, ← g8Cls_kap] at *; exact hk) x₁ y₁ x₂ y₂ x₃ y₃ hx1 hy1 hxy1 hx2 hy2 hxy2 hx3 hy3 hxy3 g1 g2 g3 hs
    rwa [g8Cls_lab, g8Cls_lab]

end transfer

/-- **Prop 9.6 for the final components, `0 < γ ≤ 1/2`** (main's `final_component_bound` with `γ ∈ (0, 1/2]`, no
`hsm2`, the ported `FinalDec`; from `prop96_low_proved`). -/
theorem final_component_bound_low {d : ℕ} (hd : 3 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → G8Copy.Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        G8Copy.FinalShape M cls odd → FinalDec M cls L γ η Adm →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → (∀ S, 0 ≤ P S) →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
        (∃ v₂ : V, v₂ ∉ M.atoms) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (WaveTurbulence.FinalCountG8.finalRHS M (fun a => g8Cls (cls a)) odd L γ η) := by
  obtain ⟨Cs, hCs, h⟩ := prop96_low_proved d hd γ hγ η hη hsm hηs TVine.Struct.Drawn.drawnTVine
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨R₀, fun L hL V D _ _ _ M cls odd Adm P hs hd' hc hP hA hv => ?_⟩
  exact hR L hL M (fun a => g8Cls (cls a)) odd Adm P (G8Copy.FinalShape.toG8 hs) (FinalDec.toLow hγ.2 hd') hc hP hA hv

end WaveTurbulence.GammaLow.FinalCount.H
