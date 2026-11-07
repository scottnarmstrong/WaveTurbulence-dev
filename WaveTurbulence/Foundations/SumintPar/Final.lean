/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Sumint
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintSigned

/-!
# SUMINT-PAR: the signed `sumint` with weights of regularity `A ≥ d + 1`, depending on `r`

`WaveTurbulence.SumintPar.sumint` is `sumint` (signed core phases, F79) for a datum whose `𝒦` weights
may depend on the output difference `r = e - f` and whose weight bounds `propertyKj` are stated at an
arbitrary derivative order `wN ≥ d + 1` (T: `30d`) and decay `wDec > d` (T: `30d`), uniformly in `r`.
The exact existing 30d signed statement `WaveTurbulence.VineEstS2.SumintSigned` is the special case
`wN = wDec = 30 d`, `wK v r = wK v` (theorem `signed_of_sumintPar`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Monotonicity of the prefix, with the standing hypothesis `3 ≤ d`. -/
theorem wtPrefixA_mono {Q Q' : ℝ → WTParams → Prop} (h : WTPrefixA Q)
    (hQ : ∀ A P, 3 ≤ P.d → Q A P → Q' A P) : WTPrefixA Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, h0, h1⟩ := h d hd γ hγ
  refine ⟨η₀, h0, fun η hη A hA φin hφin τ hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC, ν₀, hν, h2⟩ := h1 η hη A hA φin hφin τ hτ φ hφ
  refine ⟨C₁, hC, ν₀, hν, fun ν hν' => ?_⟩
  obtain ⟨δ₀, hδ, h3⟩ := h2 ν hν'
  refine ⟨δ₀, hδ, fun δ hδ' D hD hτD => ?_⟩
  obtain ⟨C₂, hC2, L₀, hL, h4⟩ := h3 δ hδ' D hD hτD
  exact ⟨C₂, hC2, L₀, hL, fun L hL' => hQ _ _ hd (h4 L hL')⟩

/-- The field-by-field copy of a snapshot-9 datum with signs, at the `30 d` regularity. -/
noncomputable abbrev ofOrig {d : ℕ} (D : WaveTurbulence.SumintDatum d) (a b : Fin D.S.I → ℤˣ) :
    SumintDatum d where
  S := D.S
  T₁ := D.T₁
  T₁inv := D.T₁inv
  T₂ := D.T₂
  T₁_mul := D.T₁_mul
  T₁inv_mul := D.T₁inv_mul
  T_unit := D.T_unit
  H₁ := D.H₁
  H₂ := D.H₂
  H_coset := D.H_coset
  Λ := D.Λ
  prev := D.prev
  σk := D.σk
  σe := D.σe
  wK := fun v _ => D.wK v
  wL := D.wL
  wN := 30 * d
  wDec := 30 * d
  g := D.g
  g' := D.g'
  ζc := D.ζc
  Λsel := D.Λsel
  ξc := D.ξc
  param := D.param
  q := D.q
  constraints := D.constraints
  badKind := D.badKind
  qOut := D.qOut
  centre := D.centre
  wBar := D.wBar
  coreFirstSign := a
  coreSign := b

/-- **The existing signed `30d` statement is the special case `wN = wDec = 30 d`, `r`-independent
weights, of `SumintPar.sumint`.** -/
theorem signed_of_sumintPar : WaveTurbulence.VineEstS2.SumintSigned := by
  unfold WaveTurbulence.VineEstS2.SumintSigned
  refine wtPrefixA_mono sumint ?_
  intro A P hd3 hP D hI a b hD hM
  have hD' : (ofOrig D a b).Admissible A P.L P.γ P.η P.D := by
    unfold WaveTurbulence.SumintDatum.Admissible at hD
    unfold SumintDatum.Admissible
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hD
    refine ⟨h1, h2, h3, ?_, ?_, h6, h7, h8, h9, h10, ?_⟩
    · intro v
      obtain ⟨x, y, hx⟩ := h4 v
      refine ⟨x, y, ?_⟩
      rcases x with w | w | c <;> rcases y with w' | w' | c' <;> exact hx
    · intro v
      exact ⟨fun _ => (h5 v).1, (h5 v).2⟩
    · exact ⟨by show P.d + 1 ≤ 30 * P.d; omega, by show P.d < 30 * P.d; omega⟩
  exact hP (ofOrig D a b) hI hD' hM

end WaveTurbulence.SumintPar
