/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
import Mathlib.Tactic

/-!
# SUBPRO (S4): the gap indicator `Z` and gaps of objects

* `gapKind_of_Z`: on the support of `Z`, the pair of an entry of the gap specification has the prescribed kind.
* `hasGapKind_of_pair`: an object with a pair of darts inside it at its upper joint, with gap of kind `k`, has
  gap kind `k` (TARGET `defdiff`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

variable {w d : ℕ}

theorem gapKind_of_Z (G : Garden w) (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (h : splicedGapIndicator G D L γ η base z ≠ 0)
    {v : GBranch G.tree} {q : LocalGapSpecification G v} (hq : D.gapSpecification v = some q) :
    Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z) q.first q.second) = q.kind := by
  classical
  unfold splicedGapIndicator at h
  have h1 := (Finset.prod_ne_zero_iff.mp h) v (Finset.mem_univ v)
  rw [hq] at h1
  by_contra hne
  apply h1
  exact if_neg hne

theorem gapKind_neg (L γ η : ℝ) (r : Mom d) : Molecule.gapKind L γ η (-r) = Molecule.gapKind L γ η r := by
  classical
  unfold Molecule.gapKind
  simp [neg_eq_zero]


variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An object with a pair of darts of opposite directions inside it at its upper joint, whose gap has kind `k`, has
gap kind `k`. -/
theorem hasGapKind_of_pair {M : Molecule V D} (O : Object M) (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (x y : D) (hx : M.atom x = O.upper) (hy : M.atom y = O.upper)
    (hxy : M.out x ≠ M.out y) (hcx : O.ContainsDart x) (hcy : O.ContainsDart y)
    (k : Molecule.GapKind) (hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = k) :
    O.HasGapKind L γ η w κ k := by
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
  have hkr : Molecule.gapKind L γ η (Molecule.gapAt L w κ p q) = k := by
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
    have hne : ∀ t : D, Object.ContainsDart (⟨A, a, b, .hyper R⟩ : Object M) t → t ≠ R.added ∧ t ≠ M.mate R.added :=
      fun t ht => ⟨ht.1, ht.2.1⟩
    refine ⟨Molecule.gapAt L w κ p q, ?_, hkr⟩
    show (Molecule.eraseBond M R.added).IsBlockGap L w (fun t => κ t.1) A a _
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨_, (hne _ hcx)⟩, ⟨_, (hne _ hcy)⟩, hpa, hqa, hcx.2.2, hcy.2.2, hpo, hqo, rfl⟩
    · exact ⟨⟨_, (hne _ hcy)⟩, ⟨_, (hne _ hcx)⟩, hpa, hqa, hcy.2.2, hcx.2.2, hpo, hqo, rfl⟩

end WaveTurbulence.Subpro
