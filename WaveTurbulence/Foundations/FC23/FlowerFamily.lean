/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.FlowerSumP
/-! The literal flower carrier with extra real profile/bond weights.
The distinctly named uniform-family Prop is an open FC3 interface; this file
does not assume it as a proof of the frozen flower theorem. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open MeasureTheory Finset Set
def flowerWeighted (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid p j (pat j)),
    kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
      (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)
      (fun k => weight LG k * (dagger.elim 1 fun c => LG.sibWeight c k))
      (fun _ => t) 0 (fun _ => n) n'

/-- Replacing the weight recovers the literal D13 cut1 kernel, on its exact carrier. -/
theorem flowerWeighted_cut1 (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (j : ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerWeighted P F p N kind pat dagger (fun LG k => LG.cutWeight1P p P.L j k) ζ t s n n' =
      flowerSumP P F p N kind pat dagger (some j) none ζ t s n n' := by
  simp only [flowerWeighted, flowerSumP, Option.elim_some, Option.elim_none, mul_one]

/-- One endpoint's polynomial factor. `tail = true` denotes the T2 family. -/
def endpointFactor (p q : ℕ) (tail : Bool) (M A z r : ℝ) : ℝ :=
  if tail then (if q = p then chi0 (r / (M / 2)) else 1) *
    (1 + z * (1 - chi0 (r / A)))
  else if q = p then chi0 (r / (M / 2)) + z * (chi0 (r / M) - chi0 (r / (M / 2)))
  else 1

/-- A fixed smooth attached-bond term and the endpoint profile polynomial.
All non-flower leaf endpoints are used, including negative leaves. -/
def flowerFamilyWeight {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail small : Fin w → Bool) (z : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  (∏ a : GNode LG.garden.tree,
    if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then
      chi0 (‖k a‖ / (if tail a.1.1 && small a.1.1 then M / 2 else M)) else 1) *
  ∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then 1 else
    endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z l.1.1) ‖k l.toNode‖

/-- The exact proposed FC3 boundary for fixed frozen outer data.
`A = M/(4*nmax)` is the auxiliary scale; `ρ` includes the high profile budget.
`B` is the internal, pre-extraction flower budget described in NOTES.md.
No cut1 gain occurs in this premise. Its production remains open. -/
def FC23UniformFlowerFamily (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (M A : ℝ) (ρ : Fin w → ℝ) (B : ℝ) : Prop :=
  ∀ tail small : Fin w → Bool, ∀ z : Fin w → ℝ,
    (∀ j, z j ∈ Icc (0 : ℝ) (ρ j)) →
    ‖flowerWeighted P F p N kind pat dagger
      (fun LG k => flowerFamilyWeight LG p M A tail small z k) ζ t s n n'‖ ≤ B
end WaveTurbulence.FC23
