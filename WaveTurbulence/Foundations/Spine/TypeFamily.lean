/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyOutputs
public import WaveTurbulence.Foundations.Molecule.PrimeGardenDefs
/-! AMEND6' (R47-FINAL, design P*): Stage 1 leaf data by PAIR TYPE, and the twist-closure premise.

A pair-type family `TypeFamilyD` carries, for each index `i`, a sign (`|sign| <= 1`), a profile
`h i : layer -> tree of the + leaf -> tree of the - leaf -> Mom d -> R` and ONE bound `b i` (uniform across
layers, types and gardens, as R46 requires). `typeProfiles` assigns each input leaf its pair type; LF twists keep
every leaf in its root tree (TARGET Def twist / lftwist, research-twistprof Q1), so pair-type profiles are
class-compatible without a leaf bijection.

`TwistClosed p A` pins R44 (i): `A` is closed under the universe's LF twists (the actual once-per-member outputs of
a separated vine family, `LFTwist.FamilyReconstruction.outputs`, on canonical objects). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- The root trees of the two leaves of the pair at a raw address: the tree of the address and the tree of
its partner leaf (non-leaf addresses: the tree of the address twice). LF-twist invariant (all twisting
happens inside the subtree of `u_1`, TARGET Def twist / lftwist). -/
noncomputable def pairTrees {w : ℕ} (G : Garden w) (a : Fin w × TTree.Path) : Fin w × Fin w :=
  if h : ∃ ℓ : GLeaf G.tree, ℓ.1 = a then (a.1, (G.pair h.choose).1.1) else (a.1, a.1)

/-- Pair-type profiles: the profile at the address `a` is `h (layer a) (tree of a) (tree of its partner)`. -/
noncomputable def typeProfiles {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) :
    LeafProfiles w d := fun a =>
  if hn : a.2 ∈ (LG.garden.tree a.1).nodes then
    h (LG.layer ⟨a, hn⟩) (pairTrees LG.garden a).1 (pairTrees LG.garden a).2
  else fun _ => 0

/-- AMEND6': leaf-modified families uniform over pair types. Index, signs and bounds do not depend on the
garden. -/
structure TypeFamilyD (d w : ℕ) where
  ι : Type
  fin : Fintype ι
  sign : ι → ℝ
  h : ι → ℕ → Fin w → Fin w → Mom d → ℝ
  b : ι → NNReal
  sign_abs_le : ∀ i, |sign i| ≤ 1

abbrev TypeFamily (P : WTParams) (w : ℕ) := TypeFamilyD P.d w

/-- The leaf family of a type family. -/
noncomputable def TypeFamilyD.toLeafFamily {d w : ℕ} (U : TypeFamilyD d w) : LeafFamilyD d w where
  ι _ := U.ι
  fin _ := U.fin
  sign _ := U.sign
  H LG i := typeProfiles LG (U.h i)
  B _ i _ := U.b i
  sign_abs_le _ := U.sign_abs_le

/-- The leaf family over the parameter record `P` (so that `LeafFamily` dot notation applies). -/
noncomputable abbrev TypeFamily.toLF {P : WTParams} {w : ℕ} (U : TypeFamily P w) : LeafFamily P w :=
  U.toLeafFamily

/-- Every profile of the family is bounded in `S^{40d,40d}` at every layer `<= p`, for every pair type. -/
def TypeFamilyD.Bounded {d w : ℕ} (U : TypeFamilyD d w) (p : ℕ) : Prop :=
  ∀ i q j j', q ≤ p → SNormR (40 * d) (40 * d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ)

theorem typeProfiles_leaf {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (ℓ : GLeaf LG.garden.tree) :
    typeProfiles LG h ℓ.1 = h (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 := by
  have hn : ℓ.1.2 ∈ (LG.garden.tree ℓ.1.1).nodes := TTree.leaves_subset_nodes _ ℓ.2
  have he : ∃ ℓ' : GLeaf LG.garden.tree, ℓ'.1 = ℓ.1 := ⟨ℓ, rfl⟩
  have hc : he.choose = ℓ := Subtype.ext he.choose_spec
  simp only [typeProfiles, pairTrees, dite_eq_left hn, dite_eq_left he, hc]
  exact congrArg (fun a : GNode LG.garden.tree => h (LG.layer a) ℓ.1.1 (LG.garden.pair ℓ).1.1) (Subtype.ext rfl)

/-- Layer-uniform families are the type families that ignore the trees. -/
theorem typeProfiles_layer {w d : ℕ} (LG : LayeredGarden w) (F : ℕ → Mom d → ℝ) :
    typeProfiles LG (fun q _ _ => F q) = layerProfiles LG F := by
  funext a
  simp only [typeProfiles, layerProfiles]

/-- The size of a type family at a garden: `∑_i b_i ^ #inputLeaves`. -/
theorem TypeFamilyD.size_eq {P : WTParams} {w : ℕ} (U : TypeFamily P w) (LG : LayeredGarden w) :
    U.toLF.size LG = @Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin)
      (fun i => (U.b i : ℝ) ^ (inputLeaves LG.garden).card) := by
  show (@Finset.sum U.ι ℝ _ (@Finset.univ _ U.fin) fun i =>
      ∏ ℓ ∈ inputLeaves LG.garden, ((U.b i : NNReal) : ℝ)) = _
  exact Finset.sum_congr rfl fun i _ => Finset.prod_const _

/-- R44 (i), pinned (AMEND6', R31 (1)): `A` is closed under LF twists at the vines of the CANONICAL skeleton.
Every actual once-per-member output `LH` of a separated vine family `B` (the universe's `LFTwist`, TARGET Def
lftwist, L1466-L1480; `kind = true` for gardens, `false` for couples) of a canonical object whose layered
garden is in `A` and whose skeleton `B.skeleton` is a PRIME garden (no embedded mini couple or tree: the
REG-STRUCT canonical skeleton, the maximal collapse of the regular objects) is in `A`. Quantifying over all
families of prime skeletons covers the vines of any collection `V`. -/
def TwistClosed {w : ℕ} (p : ℕ) (A : Finset (LayeredGarden w)) : Prop :=
  ∀ (kind : Bool) (ι : Type) (B : LFTwist.FamilyReconstruction w ι) (L : List ι),
    Reg.Skeleton.IsPrimeGarden B.skeleton →
    LFTwist.CanonicalObject p kind B.layered → B.layered ∈ A →
    ∀ LH ∈ B.outputs p kind L, LH ∈ A

end WaveTurbulence.LGSpine
