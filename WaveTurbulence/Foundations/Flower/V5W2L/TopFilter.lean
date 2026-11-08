/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W2L.Defs
public import WaveTurbulence.Foundations.Flower.V5WT.TopFilter

/-! # V5W-2L: a finite product of region-top stem filters in V5's normalized chain coordinates

`topFilterPullbackL`: for every CL region `R` with top branch `a` and every list `S`, the product filter
`nodeWeight (topFilterWeightL S) L base a`, i.e. `∏_{s ∈ S} χ₀(|Ω_a|/s)`, has an output-dependent engine pullback of
mass `topFilterMass ^ S.length`.

Mathematics (supplement Lemma 9.3, once per factor).  Each factor `χ₀(|Ω_a|/s)` is V5W-T's `affineOutCharMix` of
mass `topFilterMass` (`V5WT.enginePullbackOut_topFilter_some`).  The product of two output-dependent mixtures over
one common output is again one (`outMul`: product measure, input frequencies add, phases multiply; at a frozen output
it is main's `CharMix.mul`, whose value is the product of the values by Fubini, `CharMix.val_mul`), and the masses
multiply (`CharMix.mass_mul`).  Induction on the list, with the empty product `1` of mass `1` (`enginePullback_one`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5W2L
open WaveTurbulence MeasureTheory Cut2A DegenVine
open WaveTurbulence.Flower.V5WT (OutCharMix EnginePullbackOut enginePullbackOut_of enginePullbackOut_congr
  enginePullbackOut_mono enginePullbackOut_topFilter_some)
open WaveTurbulence.Flower.V5W (topFilterWeight topFilterMass)

/-! ## The product of two output-dependent mixtures -/

section Mul
variable {S : SumintShape} {d : ℕ}

/-- **The product of two output-dependent character mixtures** (common output; product measure, frequencies add,
phases multiply). -/
def outMul (N₁ N₂ : OutCharMix S d) : OutCharMix S d where
  α := N₁.α × N₂.α
  μ := N₁.μ.prod N₂.μ
  ζ := fun q E => N₁.ζ q.1 E + N₂.ζ q.2 E
  hζ := fun E => ((N₁.hζ E).comp measurable_fst).add ((N₂.hζ E).comp measurable_snd)
  u := fun q E => N₁.u q.1 E * N₂.u q.2 E
  hu := fun E => ((N₁.hu E).comp measurable_fst).mul ((N₂.hu E).comp measurable_snd)
  hu1 := fun q E => by
    rw [norm_mul]
    calc _ ≤ 1 * 1 := mul_le_mul (N₁.hu1 _ _) (N₂.hu1 _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Freezing commutes with the product (values). -/
theorem outMul_val_freeze (N₁ N₂ : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (outMul N₁ N₂).val L E x = ((N₁.freeze E).mul (N₂.freeze E)).val L E x := rfl

theorem outMul_val (N₁ N₂ : OutCharMix S d) (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (outMul N₁ N₂).val L E x = N₁.val L E x * N₂.val L E x := by
  rw [outMul_val_freeze, CharMix.val_mul, OutCharMix.freeze_val, OutCharMix.freeze_val]

theorem outMul_mass (N₁ N₂ : OutCharMix S d) : (outMul N₁ N₂).mass = N₁.mass * N₂.mass := by
  have h : (outMul N₁ N₂).mass = ((N₁.freeze 0).mul (N₂.freeze 0)).mass := rfl
  rw [h, CharMix.mass_mul, OutCharMix.freeze_mass, OutCharMix.freeze_mass]

end Mul

/-! ## The product of two output-dependent engine pullbacks -/

section Pull
open RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.P3
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **Product of two output-dependent engine pullbacks** (masses multiply). -/
theorem enginePullbackOut_mul₂ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m₁ m₂ : (GNode G.tree → Fin d → ℤ) → ℂ} {mass₁ mass₂ : ℝ}
    (h₁ : EnginePullbackOut R L base m₁ mass₁) (h₂ : EnginePullbackOut R L base m₂ mass₂) :
    EnginePullbackOut R L base (fun z => m₁ z * m₂ z) (mass₁ * mass₂) := by
  intro n hM9 B hL
  obtain ⟨N₁, hN₁, he₁⟩ := h₁ n hM9 B hL
  obtain ⟨N₂, hN₂, he₂⟩ := h₂ n hM9 B hL
  refine ⟨outMul N₁ N₂, ?_, ?_⟩
  · rw [outMul_mass]
    exact mul_le_mul hN₁ hN₂ N₂.mass_nonneg (N₁.mass_nonneg.trans hN₁)
  · intro β hβ x
    beta_reduce
    rw [outMul_val, he₁ β hβ x, he₂ β hβ x]

/-- The product filter at a node splits off its first factor. -/
theorem nodeWeight_topFilterWeightL_cons (L : ℝ) (base : Mom d) (s : ℝ) (S : List ℝ) (v : GBranch G.tree)
    (z : GNode G.tree → Fin d → ℤ) :
    VineSpaceK.nodeWeight (topFilterWeightL (s :: S)) L base v z =
      VineSpaceK.nodeWeight (topFilterWeight (some s)) L base v z *
        VineSpaceK.nodeWeight (topFilterWeightL S) L base v z := by
  unfold VineSpaceK.nodeWeight
  exact topFilterWeightL_cons s S _

/-- **The product of top filters in chain coordinates** (supplement Lemma 9.3 once per factor): an output-dependent
engine pullback of mass `topFilterMass ^ S.length`.  No positivity of the dilations is needed (`s ≤ 0` is a
legitimate, if degenerate, `affineOutCharMix` of the same mass). -/
theorem topFilterPullbackL (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (S : List ℝ) :
    EnginePullbackOut R L base (VineSpaceK.nodeWeight (topFilterWeightL S) L base a)
      (topFilterMass ^ S.length) := by
  induction S with
  | nil =>
    rw [List.length_nil, pow_zero]
    refine enginePullbackOut_congr R L base
      (enginePullbackOut_of R L base (VineSpaceK.enginePullback_one R L base)) ?_
    funext z
    simp [VineSpaceK.nodeWeight, topFilterWeightL]
  | cons s S ih =>
    have h := enginePullbackOut_mul₂ R L base (enginePullbackOut_topFilter_some R L base s) ih
    rw [List.length_cons, pow_succ']
    refine enginePullbackOut_congr R L base h ?_
    funext z
    exact (nodeWeight_topFilterWeightL_cons L base s S a z).symm

end Pull

/-! ## The size of the product filter -/

theorem norm_topFilterWeight_some_le {d : ℕ} (s : ℝ) (z : Fin 4 → Mom d) : ‖topFilterWeight (some s) z‖ ≤ 1 := by
  have h : ∀ y : ℝ, ‖((WaveTurbulence.chi0 y : ℝ) : ℂ)‖ ≤ 1 := fun y => by
    have h0 : 0 ≤ WaveTurbulence.chi0 y := Real.smoothTransition.nonneg _
    have h1 : WaveTurbulence.chi0 y ≤ 1 := Real.smoothTransition.le_one _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  exact h _

theorem norm_topFilterWeightL_le {d : ℕ} (S : List ℝ) (z : Fin 4 → Mom d) : ‖topFilterWeightL S z‖ ≤ 1 := by
  induction S with
  | nil => simp [topFilterWeightL]
  | cons s S ih =>
    rw [topFilterWeightL_cons, norm_mul]
    exact (mul_le_mul (norm_topFilterWeight_some_le s z) ih (norm_nonneg _) zero_le_one).trans (one_mul 1).le

end WaveTurbulence.Flower.V5W2L
