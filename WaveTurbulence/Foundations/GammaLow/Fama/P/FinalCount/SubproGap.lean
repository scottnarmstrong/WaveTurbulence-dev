/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.SubproGap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# SUBPRO (S4): the gap indicator `Z` and gaps of objects

* `gapKind_of_Z`: on the support of `Z`, the pair of an entry of the gap specification has the prescribed kind.
* `hasGapKind_of_pair`: an object with a pair of darts inside it at its upper joint, with gap of kind `k`, has
  gap kind `k` (TARGET `defdiff`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.GammaLow.FinalCount

variable {w d : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]




variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An object with a pair of darts of opposite directions inside it at its upper joint, whose gap has kind `k`, has
gap kind `k`. -/
theorem hasGapKind_of_pair {M : Molecule V D} (O : Src.Object γ M) (L γ' η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (x y : D) (hx : M.atom x = O.upper) (hy : M.atom y = O.upper)
    (hxy : M.out x ≠ M.out y) (hcx : O.ContainsDart x) (hcy : O.ContainsDart y)
    (k : Molecule.GapKind) (hk : Molecule.gapKind L γ' η (Molecule.gapAt L w κ x y) = k) :
    O.HasGapKind L γ' η w κ k := by
  obtain ⟨A, a, b, sh⟩ := O
  have hgn : ∀ p q : D, Molecule.gapAt L w κ q p = -Molecule.gapAt L w κ p q := fun p q => by
    unfold Molecule.gapAt; abel
  -- orient the pair
  have key : ∃ p q : D, M.atom p = a ∧ M.atom q = a ∧ M.out p = true ∧ M.out q = false ∧
      (p = x ∧ q = y ∨ p = y ∧ q = x) := by
    cases hox : M.out x
    · cases hoy : M.out y
      · exact absurd (by rw [hox, hoy]) hxy
      · exact ⟨y, x, hy, hx, hoy, hox, Or.inr ⟨rfl, rfl⟩⟩
    · cases hoy : M.out y
      · exact ⟨x, y, hx, hy, hox, hoy, Or.inl ⟨rfl, rfl⟩⟩
      · exact absurd (by rw [hox, hoy]) hxy
  obtain ⟨p, q, hpa, hqa, hpo, hqo, hpq⟩ := key
  have hkr : Molecule.gapKind L γ' η (Molecule.gapAt L w κ p q) = k := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hk
    · rw [hgn, gapKind_neg]; exact hk
  cases sh with
  | vc h =>
    refine ⟨Molecule.gapAt L w κ p q, ?_, hkr⟩
    show M.IsBlockGap L w κ A a _
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, _, hpa, hqa, hcx, hcy, hpo, hqo, rfl⟩
    · exact ⟨_, _, hpa, hqa, hcy, hcx, hpo, hqo, rfl⟩
  | hyper R =>
    have hne : ∀ t : D, Src.Object.ContainsDart (⟨A, a, b, .hyper R⟩ : Src.Object γ M) t → t ≠ R.added ∧ t ≠ M.mate R.added :=
      fun t ht => ⟨ht.1, ht.2.1⟩
    refine ⟨Molecule.gapAt L w κ p q, ?_, hkr⟩
    show (Molecule.eraseBond M R.added).IsBlockGap L w (fun t => κ t.1) A a _
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨_, (hne _ hcx)⟩, ⟨_, (hne _ hcy)⟩, hpa, hqa, hcx.2.2, hcy.2.2, hpo, hqo, rfl⟩
    · exact ⟨⟨_, (hne _ hcy)⟩, ⟨_, (hne _ hcx)⟩, hpa, hqa, hcy.2.2, hcx.2.2, hpo, hqo, rfl⟩

end WaveTurbulence.GammaLow.Fama
