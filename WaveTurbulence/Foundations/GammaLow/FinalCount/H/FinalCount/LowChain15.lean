/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain15`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (11): the chain of the five cover theorems `chain_coverL`.**  Potentials
`W₁ = N⁵ W₁ᵇ` (phase 1 and Step D1, exponent `g₁`), `W_D3 = N⁴ W`, `W₂ = N³ W`, `W₃ = N² W`, `W₄ = N W` with `W h = WPot (Y0f (RofS h.s)) gExp h`;
the index `RofS` is unchanged by the old steps (`rofS_*`) and drops by `hW_D3`/`hW_D1'` along the new steps. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section rofs
variable {L γ η : ℝ} {w : Mom d} {h h' : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {R' : ℕ}

theorem rofS_post1 [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {t : T1 h}
    (hI : Inv R' h.s) (hn : Node1 C crit L γ η h t) : RofS (post1 C crit L γ η h t).s = R' := by
  obtain ⟨K, F, hK⟩ := node1_spec hn
  rw [hK, vinePost_s]
  exact rofS_of_inv (Inv.vineStL hI K _ (alphaOrBeta_isAB _ _ _ _) F.hu F.hl F.h3a F.h3b)

end rofs

section ext
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}

theorem hext4L [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hn : Node4 h v x₁ x₂)
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls4 L w h A x₁ x₂) (hr : Reach4L C Un Fst L γ η w k h) :
    Reach4L C Un Fst L γ η w k (post4 h v x₁ x₂) :=
  hr.ext (UStep4.hstep (uStep4_node (L := L) (w := w) (A := A) hn) hk)

theorem hext3L [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V}
    {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) (hr : Reach3L C Un Fst L γ η w k h) :
    Reach3L C Un Fst L γ η w k (post3 h v x₁ x₂ z b) :=
  hr.ext (hstep3C_node hn hdes hk)

theorem hext2L [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n)
    (hdes : ∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j)))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls2 L γ η w h A n) (hr : Reach2L C Un Fst L γ η w k h) :
    Reach2L C Un Fst L γ η w k (post2 L γ η h n) := by
  obtain ⟨hcl0, ht, ha, hb, hf, -⟩ := Classical.choose_spec hn
  change (triOf hn).t = _ at ht
  change (triOf hn).a = _ at ha
  change (triOf hn).b = _ at hb
  have hel : Eligible C L γ η w k h (triOf hn) := by
    refine ⟨fun j => ?_, ?_, fun j => ?_⟩
    · rw [ha, hb]; exact hk.2.1 j
    · rw [ha, hb]; exact hk.2.2.2.1
    · rw [ht, ha, hb]; exact hdes j
  have hs2 : HStep2 L γ η w k h (post2 L γ η h n) := by
    have := UStep2.hstep (uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn) hk
    exact this
  refine hr.ext (HStep2C.mk (triOf hn) hel hs2 ⟨Q2 n, kp2 n, triOf_cl hn, ?_⟩)
  rw [post2_eq hn]; rfl

theorem hextD3L {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hn : D3Data h v x₁ x₂)
    (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) (k : D₀ → (Fin d → ℤ)) (hk : k ∈ clsD3 L w h A x₁ x₂)
    (hr : ReachD3 C Un Fst L γ η w k h) : ReachD3 C Un Fst L γ η w k (h.betaPost v x₁ x₂) :=
  hr.ext (UStepD3.hstep (uStepD3_node (C := C) (L := L) (γ := γ) (η := η) (w := w) (A := A) hn hdes) hk)

end ext

end WaveTurbulence.GammaLow.FinalCount.H
