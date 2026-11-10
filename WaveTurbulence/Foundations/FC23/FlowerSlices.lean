/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerPolynomial
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts
/-! Finite original-tree order slices of the literal flower carrier. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset

def flowerCarrier (P : WTParams) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (pat : Fin w → FixPat) (ζ : ℤˣ) : Set (LayeredGarden w) :=
  {LG | IsCanonH (p + 1) LG ∧
    (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
    LG.FlowerKindOK p (P.N (p + 1)) kind ∧
    (∀ l : GLeaf LG.garden.tree, LG.garden.IsFlower l →
      LG.garden.sign l.toNode = ζ * LG.garden.sig l.1.1) ∧
    ∀ j, LG.PatValid p j (pat j)}

theorem flowerCarrier_finite (P : WTParams) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (pat : Fin w → FixPat) (ζ : ℤˣ) : (flowerCarrier P p N kind pat ζ).Finite :=
  (Canon.finite_canonH (p + 1) N w).subset fun _ h => ⟨h.1, h.2.2.1.le⟩

def flowerKernel (P : WTParams) (F : ℕ → Mom P.d → ℝ) (_p : ℕ) {w : ℕ}
    (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (t s : ℝ) (n n' : Fin P.d → ℤ) (LG : LayeredGarden w) : ℂ :=
  kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
    (if dagger.isSome then univ.filter LG.garden.IsFlowerParent else ∅)
    (fun k => weight LG k * (dagger.elim 1 fun c => LG.sibWeight c k))
    (fun _ => t) 0 (fun _ => n) n'

theorem flowerWeighted_eq_sum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerWeighted P F p N kind pat dagger weight ζ t s n n' =
      ∑ LG ∈ (flowerCarrier_finite P p N kind pat ζ).toFinset,
        flowerKernel P F p pat dagger weight t s n n' LG := by
  rw [← finsum_mem_eq_finite_toFinset_sum]
  rfl

theorem freeTreeLeaves_card_le {w : ℕ} (LG : LayeredGarden w) (j : Fin w) :
    (freeTreeLeaves LG j).card ≤ 2 * (LG.garden.tree j).order + 1 := by
  rw [← Comb.card_leaves]
  apply card_le_card_of_injOn (fun l : GLeaf LG.garden.tree => l.1.2)
  · intro l hl
    have hj := (mem_filter.mp hl).2
    change l.1.2 ∈ (LG.garden.tree j).leaves
    simpa only [hj] using l.2
  · intro l hl l' hl' he
    have hj := (mem_filter.mp hl).2
    have hj' := (mem_filter.mp hl').2
    apply Subtype.ext
    exact Prod.ext (hj.trans hj'.symm) he

end WaveTurbulence.FC23
