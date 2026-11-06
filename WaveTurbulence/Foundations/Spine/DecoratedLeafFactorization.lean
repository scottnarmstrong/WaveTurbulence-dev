/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.QuadraticLeafFactorization
public import WaveTurbulence.Foundations.Spine.DecoratedWeightExpansion
/-! Root weights factor into separately modified actual input profiles, with no change to the
oscillatory coefficients. This is the algebraic identity underlying TARGET L2065–L2067. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

abbrev ActualInputLeaves {w : ℕ} (G : Garden w) :=
  {l : GLeaf G.tree // l ∈ inputLeaves G}

def rootInputSlot {w : ℕ} (G : Garden w) (hp : G.IsPlain) (j : Fin w)
    (l : RootLeafSlots G j) : ActualInputLeaves G :=
  ⟨positiveRepresentative G l.1, positiveRepresentative_mem G hp l.1⟩

abbrev RootWeightChoices {w : ℕ} (G : Garden w) (d m : ℕ) :=
  ∀ j : Fin w, Fin m → RootQuadraticChoice (RootLeafSlots G j) d

def rootCoordinateSlots {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (t : (Fin w × Fin m) × Bool) :
    Option (ActualInputLeaves G × Fin d) :=
  quadraticCoordinate (mapQuadraticChoice (rootInputSlot G hp t.1.1) (c t.1.1 t.1.2)) t.2

noncomputable def rootChoiceSign {w d m : ℕ} (G : Garden w)
    (c : RootWeightChoices G d m) : ℝ :=
  ∏ j, ∏ a, quadraticSign (fun l : RootLeafSlots G j => nodeSign G.sig l.1.1) (c j a)

/-- Literal decorated root weights times the original input product are a finite sum of
products of individually modified inputs. The finite index, sign and profile modifications
depend on the garden and the choices, and are independent of every momentum decoration. -/
theorem decorated_weighted_leaf_product {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (H : ActualInputLeaves G → Mom d → ℝ)
    (k : GNode G.tree → Mom d) (hk : IsDecoration G k) (m : ℕ) :
    (∏ l : ActualInputLeaves G, H l (k l.1.toNode)) *
        (∏ j, jbr (k (GNode.root G.tree j)) ^ (2 * m)) =
      ∑ c : RootWeightChoices G d m, rootChoiceSign G c *
        ∏ l : ActualInputLeaves G, monomialLeafProfile H (rootCoordinateSlots G hp c)
          l (k l.1.toNode) := by
  classical
  simp_rw [decorated_root_weight_expansion G k hk]
  rw [Fintype.prod_sum, mul_sum]
  apply sum_congr rfl
  intro c _
  let f : ∀ t : Fin w × Fin m, RootLeafSlots G t.1 → ActualInputLeaves G :=
    fun t => rootInputSlot G hp t.1
  let ε : ∀ t : Fin w × Fin m, RootLeafSlots G t.1 → ℤˣ :=
    fun t l => nodeSign G.sig l.1.1
  let cc : ∀ t : Fin w × Fin m, RootQuadraticChoice (RootLeafSlots G t.1) d :=
    fun t => c t.1 t.2
  have hh := prod_mappedQuadratic_leaf_factorization H f ε cc
    (fun l : ActualInputLeaves G => k l.1.toNode)
  have hs : rootCoordinateSlots G hp c =
      fun tb : (Fin w × Fin m) × Bool =>
        quadraticCoordinate (mapQuadraticChoice (rootInputSlot G hp tb.1.1)
          (c tb.1.1 tb.1.2)) tb.2 := rfl
  rw [hs]
  simpa only [f, ε, cc, Function.comp_def, rootInputSlot, rootChoiceSign,
    Fintype.prod_prod_type] using hh

end WaveTurbulence.LGSpine
