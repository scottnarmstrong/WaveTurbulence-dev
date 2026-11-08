/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.Comp

/-! # A5 MK-ASM: the CONDITIONAL HELPERS (capped-encoding statements; CAPS-ID A2 and CAPS-COMP A3b).

These are hypotheses, never proved here. Each is a *distinctly named* proposition; a discharge of CAPS-ID, CAPS-COMP
(and, for the gain case, the exchange of the `R`-integral with the decoration sum) must prove exactly these.

* `CapsDecompF` : for every instance of `FlowerCoreFiltAt`, the flower sum equals a finite sum, over
  *structures*, of products over irreducible capped components of the component values `CompData.val`; the capped
  widths sum to `4Pm`, the orders sum to `N`, the number of structures is at most `(4Pm)^{4Pm} (N+1)^{2Pm}`, no
  vertex is selected (`kSel ≡ none`), and every component satisfies the premises of `MarkedComponentBoundAtI` (the
  fields of `CompData`).
* `CapsDecompG` : the same for `FlowerCoreGainAt`, where the flower sum with the selected-face weight
  `cutWeight2P` equals the `R`-integral over the shell box of such a structure sum (the `R`-dependence enters only
  through the `Rs` field of the component data), and every non-cap tree carries a selected vertex so that the
  product of component gains is `∏_j R_j⁻¹ R_j^{-1/18}` whenever every class of the structure is nonempty
  (ruling R156 (4); an empty class has value `0`). The structures also index the selected stem vertices by
  garden-independent labels (the stem depths `kSel`, B0), so their number is at most `(4Pm)^{4Pm} (N+1)^{4Pm}`
  (R156 (3)). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- **Conditional helper F** at fixed `(Pm, P)` (CAPS-ID + CAPS-COMP, filtered case). -/
def CapsDecompFAt (Pm : ℕ) (P : WTParams) : Prop :=
  0 < P.L → 1 / 2 < P.γ → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → Option ℝ) (σ : Fin (2 * Pm) → Option ℕ),
      (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
      ((∃ i, σ i ≠ none) → ∀ j, ∃ r, Rf j = some r ∧
        (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L n‖) →
    ∃ (Str : Type) (_ : Fintype Str) (m : Str → ℕ) (D : ∀ x : Str, Fin (m x) → CompData P p t s b),
      (Fintype.card Str : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm) ∧
      (∀ x, ∑ c, 2 * (D x c).R = 4 * Pm) ∧
      (∀ x, ∑ c, (D x c).n = N) ∧
      (∀ x c j, (D x c).kSel j = none) ∧
      FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => Typed.frontierW LG p Rf k * Cases.stemFilter LG P.L σ k * Typed.leafProd LG h k)
        ζ t s n n' = ∑ x, ∏ c, (D x c).val

/-- **Conditional helper F** (all parameters). -/
def CapsDecompF : Prop :=
  ∀ (Pm : ℕ) (P : WTParams), CapsDecompFAt Pm P

/-- The shell box `∏_j [2^{j₂-1} L, 2^{j₂} L]`. -/
def shellBox (w : ℕ) (L : ℝ) (j₂ : ℕ) : Set (Fin w → ℝ) :=
  Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L))

/-- **Conditional helper G** at fixed `(Pm, P)` (CAPS-ID + CAPS-COMP + `R`-exchange, selected-face case). -/
def CapsDecompGAt (Pm : ℕ) (P : WTParams) : Prop :=
  0 < P.L → 1 / 2 < P.γ → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → ℝ) (j₂ : ℕ), 0 < j₂ → (∀ j, P.L / 2 ≤ Rf j) →
      (∀ j, (∀ j' x, ‖x‖ ≥ Rf j → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        Rf j ^ 10 ≤ ‖latticePoint P.L n‖) →
    ∃ (Str : Type) (_ : Fintype Str) (m : Str → ℕ)
      (D : (Fin (2 * Pm) → ℝ) → ∀ x : Str, Fin (m x) → CompData P p t s b),
      (Fintype.card Str : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) ∧
      (∀ Rs ∈ shellBox (2 * Pm) P.L j₂, ∀ x,
        (∑ c, 2 * (D Rs x c).R = 4 * Pm) ∧ (∑ c, (D Rs x c).n = N) ∧
        ((∀ c, (D Rs x c).A.Nonempty) →
          ∏ c, (D Rs x c).gain = ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))))) ∧
      FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => .plain) dagger
        (fun LG k => Typed.frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P P.L j₂ k *
          Typed.leafProd LG h k) ζ t s n n' =
        ∫ Rs in shellBox (2 * Pm) P.L j₂, ∑ x, ∏ c, (D Rs x c).val

/-- **Conditional helper G** (all parameters). -/
def CapsDecompG : Prop :=
  ∀ (Pm : ℕ) (P : WTParams), CapsDecompGAt Pm P

end WaveTurbulence.Flower.MkAsm
