/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot

/-! # SUMINT-SIGNED: the sumint datum with the F79 core signs

A copy of the snapshot-9 `SumintDatum` (namespace `WaveTurbulence`), with two extra fields
`coreFirstSign`, `coreSign` and the phase replaced by the signed phase of
`WaveTurbulence.VineEstS2.signedPhase`. All other fields and definitions are verbatim.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.SumintPar
open WaveTurbulence

/-- **The datum of `sumint`** (T L1595–L1625). The affine maps `k = T₁x + h₁`, `ℓ = T₂x + h₂` have
integer matrices and shifts that are integer combinations of `(e,f,g,h)` (WAVE-B v2: "affine maps
`h₁, h₂` of `(e,f,g,h)`"). -/
structure SumintDatum (d : ℕ) where
  S : SumintShape
  /-- `T₁`, its inverse, and `T₂`, with entries in `{0, ±1}` -/
  T₁ : Matrix S.VIdx S.VIdx ℤ
  T₁inv : Matrix S.VIdx S.VIdx ℤ
  T₂ : Matrix S.VIdx S.VIdx ℤ
  T₁_mul : T₁ * T₁inv = 1
  T₁inv_mul : T₁inv * T₁ = 1
  T_unit : ∀ v v', IsUnitCoeff (T₁ v v') ∧ IsUnitCoeff (T₁inv v v') ∧ IsUnitCoeff (T₂ v v')
  /-- the shifts `h₁, h₂` as coefficients of `(e, f, g, h)` -/
  H₁ : S.VIdx → Fin 4 → ℤ
  H₂ : S.VIdx → Fin 4 → ℤ
  /-- all of `k, ℓ, e, f, g, h` lie in `w̲ + ℤ_L^d` -/
  H_coset : ∀ v, ∑ c, H₁ v c = 1 ∧ ∑ c, H₂ v c = 1
  /-- hypothesis (ii): the predecessors and the numbers `Λ_jⁱ`. Reading (stage-3 O3):
  `prev v = none` means that `ℓ_v` itself is a signed sum (otherwise (ii) would be impossible for the
  lex-first index). -/
  Λ : S.VIdx → ℕ
  prev : S.VIdx → Option S.VIdx
  /-- the signed sums of (ii): coefficients of `k` and of `(e,f,g,h)` -/
  σk : S.VIdx → S.VIdx → ℤ
  σe : S.VIdx → Fin 4 → ℤ
  /-- `𝒦_jⁱ` may depend on the output difference `r = e - f` (first argument), as in clause (b) of
  `sumint` where the weight is a difference quotient in `r`; `ℒ_jⁱ` does not. -/
  wK : S.VIdx → Mom d → Mom d → ℂ
  wL : S.VIdx → Mom d → ℂ
  /-- the derivative order of the weights in the bounds `propertyKj` (T: `30d`; the proof needs `≥ d+1`) -/
  wN : ℕ
  /-- the spatial decay order of the `𝒦` weights (T: `30d`; the proof needs `> d`) -/
  wDec : ℕ
  g : S.VIdx → ℕ
  g' : S.VIdx → ℕ
  /-- `ζ_jⁱ = a x_j + b y_j + c r` (`j ≥ 1`) -/
  ζc : (i : Fin S.I) → Fin (S.m i) → Fin 3 → ℤ
  /-- `Λ_i` choice (`true`: `⟨u₁,u₃⟩`, `false`: `⟨u₃, u₁+u₂-u₃⟩`) and `ξ_i = a u₁ + b u₂ + c u₃ + d r` -/
  Λsel : Fin S.I → Bool
  ξc : Fin S.I → Fin 4 → ℤ
  /-- parameters `λ_jⁱ` (on `t`), `μ_jⁱ` (on `s`), `σ_jⁱ` (on `τ`) -/
  param : S.TVar → ℝ
  /-- unit intervals `[q_v, q_v+1]` of the input times and the order constraints `v < w` -/
  q : S.TVar → ℕ
  constraints : Finset (S.TVar × S.TVar)
  /-- for `i ∈ Bad`, which of (a)–(d) holds (`0`–`3`) -/
  badKind : Fin S.I → Fin 4
  /-- output unit intervals for `(t, t', t'')`, unit-ball centres for `(e,f,g,h)`, and `w̲` -/
  qOut : Fin 3 → ℕ
  centre : Fin 4 → Mom d
  wBar : Mom d
  /-- F79 signs: the common sign of both pure core phases of block `i` -/
  coreFirstSign : Fin S.I → ℤˣ
  /-- F79 signs: the relative sign of the nonlinear core alternative of block `i` -/
  coreSign : Fin S.I → ℤˣ

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- `k(x; e,f,g,h)` and `ℓ(x; e,f,g,h)` for lattice indices `x` (input vectors `x_v / L`). -/
noncomputable def kVec (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (efgh : Fin 4 → Mom d) (v : D.S.VIdx) :
    Mom d :=
  ∑ v', (D.T₁ v v' : ℝ) • latticePoint L (x v') + ∑ c, (D.H₁ v c : ℝ) • efgh c

noncomputable def ℓVec (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (efgh : Fin 4 → Mom d) (v : D.S.VIdx) :
    Mom d :=
  ∑ v', (D.T₂ v v' : ℝ) • latticePoint L (x v') + ∑ c, (D.H₂ v c : ℝ) • efgh c

/-- **Hypotheses (ii), (iii) and the weight bounds** of `sumint` (T L1603–L1622), with `A` the
constant of (ii) and the bad-case conditions (a), (d). Every `Λ_v ≥ 1` ("at most `Λ` terms" with
`∏ Λ ≤ C₀^M` a genuine count): a zero factor would make `∏ Λ_v ≤ A^M` vacuous and leave the other
`Λ_v` unconstrained (stage-3 R6). -/
def Admissible (A : ℝ) (L γ η : ℝ) (Dsteps : ℕ) : Prop :=
  -- (ii) as identities of affine forms: `ℓ_v - ℓ_{prev v} = ∑ σk k + ∑ σe (e,f,g,h)`
  (∀ v, (∀ v', IsUnitCoeff (D.σk v v')) ∧ (∀ c, IsUnitCoeff (D.σe v c)) ∧
    ((Finset.univ.filter fun v' => D.σk v v' ≠ 0).card +
      (Finset.univ.filter fun c => D.σe v c ≠ 0).card ≤ D.Λ v) ∧
    (∀ w, D.prev v = some w → D.S.LexLt w v) ∧
    (∀ v'', D.T₂ v v'' - (D.prev v).elim 0 (fun w => D.T₂ w v'') =
      ∑ v', D.σk v v' * D.T₁ v' v'') ∧
    ∀ c, D.H₂ v c - (D.prev v).elim 0 (fun w => D.H₂ w c) =
      ∑ v', D.σk v v' * D.H₁ v' c + D.σe v c) ∧
  (∀ v, 1 ≤ D.Λ v) ∧ ((∏ v, (D.Λ v : ℝ)) ≤ A ^ D.S.M) ∧
  -- (iii): every input variable is the difference of two of `(k, ℓ, e, f, g, h)` (as affine forms)
  (∀ v, ∃ a b : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
    let rowT : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → D.S.VIdx → ℤ := fun z => match z with
      | .inl w => D.T₁ w | .inr (.inl w) => D.T₂ w | .inr (.inr _) => 0
    let rowH : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → Fin 4 → ℤ := fun z => match z with
      | .inl w => D.H₁ w | .inr (.inl w) => D.H₂ w | .inr (.inr c) => Pi.single c 1
    (∀ v', rowT a v' - rowT b v' = if v' = v then 1 else 0) ∧ ∀ c, rowH a c - rowH b c = 0) ∧
  -- the weight bounds (propertyKj)
  (∀ v, (∀ r : Mom d, SNorm D.wN D.wDec (D.wK v r) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g v))) ∧
    SNorm D.wN 0 (D.wL v) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g' v))) ∧
  -- coefficients in `{0, ±1}`
  (∀ i j c, IsUnitCoeff (D.ζc i j c)) ∧ (∀ i c, IsUnitCoeff (D.ξc i c)) ∧
  -- unit intervals inside `[0, 𝔇]`
  (∀ v, D.q v + 1 ≤ Dsteps) ∧ (∀ c, D.qOut c + 1 ≤ Dsteps) ∧
  -- the bad cases (a) and (d)
  (∀ i, D.S.nor i = false →
    (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩))) ∧
  -- the weight regularity needed by the proof: `d + 1` derivatives and decay `> d`
  (d + 1 ≤ D.wN ∧ d < D.wDec)

/-- The weight-regularity part of admissibility: `d + 1` derivatives, decay `> d`. -/
theorem Admissible.reg {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps) :
    d + 1 ≤ D.wN ∧ d < D.wDec :=
  hD.2.2.2.2.2.2.2.2.2.2

theorem Admissible.wN_ne_zero {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps) :
    D.wN ≠ 0 := by
  have := hD.reg.1
  omega

/-- The input time domain `𝒟(t, t', t'')` (T L1612–L1613): unit intervals, all `< t`, `t₀¹ >
max(t', t'')`, and the order constraints. Requires `I ≥ 1`. -/
def timeDom (hI : 0 < D.S.I) (t t' t'' : ℝ) : Set (D.S.TVar → ℝ) :=
  {τ | (∀ v, (D.q v : ℝ) ≤ τ v ∧ τ v ≤ D.q v + 1 ∧ τ v < t) ∧
    max t' t'' < τ (.inl ⟨⟨0, hI⟩, 0⟩) ∧ ∀ c ∈ D.constraints, τ c.1 < τ c.2}

/-- The phase of (sumintI1) at input vectors `x` and input times `τ`, including the extra factors
`|t₁ⁱ - s₁ⁱ|^{1-3η}` of the bad case (c). -/
noncomputable def phase (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  let c := δ * L ^ (2 * γ)
  let X : D.S.VIdx → Mom d := fun v => latticePoint L (x v)
  let e (θ : ℝ) : ℂ := Complex.exp ((Real.pi * θ : ℝ) * Complex.I)
  (∏ i, ((∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - τ (.inr (.inl ⟨i, j⟩))) *
        inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j)))) *
      e (c * (τ (.inl ⟨i, 0⟩) - t) * inner ℝ r (X (D.S.x0Slot i))) *
      (∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - t) * inner ℝ r
        ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j) + (D.ζc i j 1 : ℝ) • X (D.S.ySlot i j) +
          (D.ζc i j 2 : ℝ) • r))) *
      (∏ j : Fin (D.S.m i + 1), e (D.param (.inl ⟨i, j⟩) * τ (.inl ⟨i, j⟩))) *
      (∏ j : Fin (D.S.m i), e (D.param (.inr (.inl ⟨i, j⟩)) * τ (.inr (.inl ⟨i, j⟩)))) *
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1))) *
  ∏ i : {i : Fin D.S.I // D.S.nor i = true},
    let u (c' : Fin 3) := X (D.S.uSlot i.1 i.2 c')
    let τ' (c' : Fin 3) := τ (.inr (.inr ⟨i, c'⟩))
    e (c * (τ' 0 - τ' 2) * (((D.coreFirstSign i.1 : ℤ) : ℝ) * inner ℝ (u 0) (u 1))) *
      e (c * (τ' 1 - τ' 2) * (((D.coreFirstSign i.1 : ℤ) : ℝ) *
        (if D.Λsel i.1 then inner ℝ (u 0) (u 2) else (((D.coreSign i.1 : ℤ) : ℝ) * inner ℝ (u 2) (u 0 + u 1 - u 2))))) *
      e (c * (τ' 2 - t) * inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0 + (D.ξc i.1 1 : ℝ) • u 1 +
        (D.ξc i.1 2 : ℝ) • u 2 + (D.ξc i.1 3 : ℝ) • r)) *
      ∏ c', e (D.param (.inr (.inr ⟨i, c'⟩)) * τ' c')

/-- **The expression `ℐ(t, t', t'', e, f, g, h)`** of (sumintI1) (T L1608–L1611), with the extra
factor `|r|` for each bad block of case (b). -/
noncomputable def expr (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (efgh : Fin 4 → Mom d) :
    ℂ :=
  let r := efgh 0 - efgh 1
  ((‖r‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (∏ v, D.wK v (efgh 0 - efgh 1) (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x r (tt 0) τ

/-- `M₀`: the number of pairs `(t_jⁱ, s_jⁱ)` in different unit intervals, plus the number of `i ∈ Nor`
whose `τ₁ⁱ, τ₂ⁱ, τ₃ⁱ` are not in one unit interval (T L1622–L1623, "`i ∈ A`" read as `i ∈ Nor`). -/
def M₀ : ℕ :=
  (Finset.univ.filter fun p : Σ i : Fin D.S.I, Fin (D.S.m i) =>
      D.q (.inl ⟨p.1, p.2.succ⟩) ≠ D.q (.inr (.inl ⟨p.1, p.2⟩))).card +
    (Finset.univ.filter fun i : {i : Fin D.S.I // D.S.nor i = true} =>
      ¬ (D.q (.inr (.inr ⟨i, 0⟩)) = D.q (.inr (.inr ⟨i, 1⟩)) ∧
        D.q (.inr (.inr ⟨i, 1⟩)) = D.q (.inr (.inr ⟨i, 2⟩)))).card

/-- `M₁ = ∑ (g_{ij} + g'_{ij})`. -/
def M₁ : ℕ := ∑ v, (D.g v + D.g' v)

end SumintDatum

end WaveTurbulence.SumintPar
