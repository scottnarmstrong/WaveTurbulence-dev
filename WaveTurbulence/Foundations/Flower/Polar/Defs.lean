/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerSlices
public import WaveTurbulence.Foundations.Spine.TypeSlopes
/-! # FL-POLAR definitions: non-flower leaves of a tree, relative leaf signs, leaf products,
the pair-type form operator and the polarization cost. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset

/-- The non-flower leaves of the `j`-th tree. -/
def nonFlowerLeavesOf {w : ℕ} (G : Garden w) (j : Fin w) : Finset (GLeaf G.tree) :=
  univ.filter fun ℓ => ℓ.1.1 = j ∧ ¬ G.IsFlower ℓ

/-- The sign of a leaf relative to the sign of the root of its tree. -/
def leafSignRel {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) : ℤˣ := G.sign ℓ.toNode * G.sig ℓ.1.1

/-- Pair-type leaf profile product over the input leaves (as in the plan's probe). -/
def leafProd {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, LGSpine.typeProfiles LG h ℓ.1 (k ℓ.toNode)

/-- The signed coefficient of the pair type `(j1, j2)` in the root form of the tree `j`. -/
def typeCoeff {w : ℕ} (σ : ℝ) (j j1 j2 : Fin w) : ℝ :=
  σ * ((if j1 = j then (1 : ℝ) else 0) - (if j2 = j then (1 : ℝ) else 0))

/-- The root-form slope: multiplication of the type `(q, j1, j2)` by `typeCoeff σ j j1 j2 · x_i`. -/
def polForm {w d : ℕ} (σ : ℝ) (j : Fin w) (i : Fin d) (g : LGSpine.TProf d w) : LGSpine.TProf d w :=
  fun q j1 j2 x => typeCoeff σ j j1 j2 * x i * g q j1 j2 x

/-- The flower-weighted sum with profile product weight. -/
def Phi (P : WTParams) (p N : ℕ) {w : ℕ} (kind : FlowerKind) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (g : LGSpine.TProf P.d w) : ℂ :=
  FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger (fun LG k => W LG k * leafProd LG g k)
    ζ t s n n'

end WaveTurbulence.Flower.Polar
