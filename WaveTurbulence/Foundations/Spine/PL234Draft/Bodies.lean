/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SpineInputs

/-!
# The parameter prefix with a larger constant `C₁`

The spine gates `CoherentApproximationGate` and `CoherentTaylorGate` and the B2.1 anchor
`RegularAsymptoticsGate` are `WTPrefix` statements, so each chooses its own `C₁` after the data. TARGET's
`C₁` is "an arbitrary large constant" (L608): products of the single-layer bounds of B2.1 have more
factors of `C₁` than one. `wtPrefix_transfer` proves a `WTPrefix` statement from another one, with
`C₁` replaced by `g C₁` and `η₀` shrunk to at most `ηmax`.

`B21Body` is the body of `RegularAsymptoticsGate` (`regularAsymptotics_gate_eq`: `rfl`).
-/

@[expose] public section
open WaveTurbulence.Induct

open Set

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

/-- The body of the B2.1 anchor `RegularAsymptoticsGate` (text of the B2 anchor). -/
def B21Body (P : WTParams) : Prop :=
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ))

theorem regularAsymptotics_gate_eq : RegularAsymptoticsGate = WTPrefix B21Body := rfl

/-- The standing facts on the parameters available inside `WTPrefix` (with the shrunk `η₀`). -/
structure Standing (P : WTParams) (ηmax : ℝ) : Prop where
  d_ge : 3 ≤ P.d
  γ_mem : P.γ ∈ Ioo (0 : ℝ) 1
  η_pos : 0 < P.η
  η_le : P.η ≤ ηmax
  φin_nonneg : ∀ k, 0 ≤ P.φin k
  τstar_pos : 0 < P.τstar
  wke : IsWKESolution P.φin P.τstar P.φ
  C₁_ge : 1 ≤ P.C₁
  ν_pos : 0 < P.ν
  δ_pos : 0 < P.δ
  D_ge : 1 ≤ P.D
  τstar_eq : P.τstar = P.D * P.δ
  C₂_ge : 1 ≤ P.C₂
  L_ge : 2 ≤ P.L

/-- **Transfer of the parameter prefix**: a `WTPrefix` statement `B` follows from `WTPrefix A` when `B`
holds at the parameters of `A` with `C₁` replaced by `g C₁` (`g x ≥ 1` for `x ≥ 1`), for `η` at most a
threshold `ηmax d γ > 0`. -/
theorem wtPrefix_transfer {A B : WTParams → Prop} (g : ℝ → ℝ) (hg : ∀ x, 1 ≤ x → 1 ≤ g x)
    (ηmax : ℕ → ℝ → ℝ) (hηmax : ∀ d γ, 0 < ηmax d γ) (hA : WTPrefix A)
    (hAB : ∀ P : WTParams, Standing P (ηmax P.d P.γ) → A P → B { P with C₁ := g P.C₁ }) :
    WTPrefix B := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hA1⟩ := hA d hd γ hγ
  refine ⟨min η₀ (ηmax d γ), lt_min hη₀ (hηmax d γ), fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, hA2⟩ :=
    hA1 η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τstar hτ φ hφ
  refine ⟨g C₁, hg C₁ hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, hA3⟩ := hA2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, hA4⟩ := hA3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact hAB ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩
    ⟨hd, hγ, hη.1, hη.2.trans (min_le_right _ _), hφin, hτ, hφ, hC₁, hν.1, hδ.1, hD, hτD, hC₂,
      hL₀.trans hL⟩ (hA4 L hL)

/-- **Transfer of the parameter prefix from two statements**: `C` holds at parameters whose `C₁` is
`g C₁ᴬ C₁ᴮ`, where `A` and `B` hold with their own constants `C₁ᴬ`, `C₂ᴬ` and `C₁ᴮ`, `C₂ᴮ`, for `η` at most
`ηmax d γ` and `L` beyond both thresholds and an extra threshold `Lmin`. -/
theorem wtPrefix_transfer₂ {A B C : WTParams → Prop} (g : ℝ → ℝ → ℝ)
    (hg : ∀ x y, 1 ≤ x → 1 ≤ y → 1 ≤ g x y)
    (ηmax : ℕ → ℝ → ℝ) (hηmax : ∀ d γ, 0 < ηmax d γ)
    (Lmin : WTParams → ℝ) (hA : WTPrefix A) (hB : WTPrefix B)
    (hABC : ∀ P : WTParams, ∀ C₁' C₂' : ℝ, Standing P (ηmax P.d P.γ) → 1 ≤ C₁' → 1 ≤ C₂' →
      Lmin { P with C₁ := g P.C₁ C₁', L := 2 } ≤ P.L →
      A P → B { P with C₁ := C₁', C₂ := C₂' } → C { P with C₁ := g P.C₁ C₁' }) :
    WTPrefix C := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, hA1⟩ := hA d hd γ hγ
  obtain ⟨η₂, hη₂, hB1⟩ := hB d hd γ hγ
  refine ⟨min (min η₁ η₂) (ηmax d γ), lt_min (lt_min hη₁ hη₂) (hηmax d γ),
    fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  have hηA : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hηB : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨C₁, hC₁, ν₁, hν₁, hA2⟩ := hA1 η hηA φin hφin τstar hτ φ hφ
  obtain ⟨C₁', hC₁', ν₂, hν₂, hB2⟩ := hB1 η hηB φin hφin τstar hτ φ hφ
  refine ⟨g C₁ C₁', hg C₁ C₁' hC₁ hC₁', min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, hA3⟩ := hA2 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, hB3⟩ := hB2 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₁, hL₁, hA4⟩ := hA3 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂', hC₂', L₂, hL₂, hB4⟩ := hB3 δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max (max L₁ L₂) (Lmin ⟨d, γ, η, φin, τstar, φ, g C₁ C₁', ν, δ, D, C₂, 2⟩),
    le_trans hL₁ ((le_max_left _ _).trans (le_max_left _ _)), fun L hL => ?_⟩
  have hLA : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLB : L₂ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLm : Lmin ⟨d, γ, η, φin, τstar, φ, g C₁ C₁', ν, δ, D, C₂, 2⟩ ≤ L := (le_max_right _ _).trans hL
  exact hABC ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩ C₁' C₂'
    ⟨hd, hγ, hη.1, hη.2.trans (min_le_right _ _), hφin, hτ, hφ, hC₁, hν.1, hδ.1, hD, hτD, hC₂,
      hL₁.trans hLA⟩ hC₁' hC₂' hLm (hA4 L hLA) (hB4 L hLB)

end WaveTurbulence.PL234
