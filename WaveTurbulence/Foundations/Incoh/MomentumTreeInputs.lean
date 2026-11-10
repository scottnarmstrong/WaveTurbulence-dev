/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeData
public import WaveTurbulence.Foundations.Incoh.LeafCellProfile

/-!
# Actual root/link momenta and the localized source inputs

Every input is the root plus its fixed integer link combination. The
leaf-source map handles paired leaves and a possible root-valued lone leaf.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The literal free root/link coordinate array. -/
@[expose] def rootLinkMomenta {n : ℕ} {V : Type*} (k : V) (x : Fin n → Fin 2 → V) :
    MomentumCoordinate n → V
  | none => k
  | some (i, j) => x i j

/-- The actual source input momenta from their integer rows. -/
@[expose] def MomentumTreeData.inputMomentum {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (k : V) (x : Fin n → Fin 2 → V) (a : Fin m) : V :=
  momentumRowEval (rootLinkMomenta k x) (P.inputRow a)

/-- Every source leaf is the specified input or the root-valued lone leaf. -/
theorem MomentumTreeData.nodeMomentum_leaf {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (k : V) (x : Fin n → Fin 2 → V)
    (i : Fin w) (p : LocalizationTree.Path) (hp : p ∈ (P.tree i).leaves) :
    P.nodeMomentum (rootLinkMomenta k x) i p =
      match P.leafInput i p with
      | none => k
      | some a => P.inputMomentum k x a := by
  rw [nodeMomentum, P.leaf_row i p hp]
  cases h : P.leafInput i p with
  | none => exact momentumRowEval_unit _ none
  | some a => rfl

/-- The actual leaf-center family used by the tree localization theorem. -/
@[expose] def MomentumTreeData.leafCenters {d n m w : ℕ} (P : MomentumTreeData n m w)
    (k : Mom d) (c : Fin m → Fin d → ℤ) (i : Fin w) (p : LocalizationTree.Path) : Mom d :=
  match P.leafInput i p with
  | none => k
  | some a => NTSP.intVec (c a)

/-- The smooth input-cell product used to select a source localization region. -/
@[expose] def MomentumTreeData.inputCellWeight {d n m w : ℕ} (P : MomentumTreeData n m w)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) : ℂ :=
  ∏ a, leafCellProfile d (NTSP.intVec (c a)) (P.inputMomentum k x a)

/-- Nonzero actual cell weights imply the leaf-ball premises of tree localization. -/
theorem MomentumTreeData.leaf_bound_of_inputCellWeight_ne_zero {d n m w : ℕ}
    (P : MomentumTreeData n m w) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (x : Fin n → Fin 2 → Mom d) (hx : P.inputCellWeight c k x ≠ 0)
    (i : Fin w) (p : LocalizationTree.Path) (hp : p ∈ (P.tree i).leaves) :
    ‖P.nodeMomentum (rootLinkMomenta k x) i p - P.leafCenters k c i p‖ ≤ Real.sqrt d := by
  classical
  rw [P.nodeMomentum_leaf k x i p hp]
  unfold leafCenters
  cases hl : P.leafInput i p with
  | none => simp only [sub_self, norm_zero]; exact Real.sqrt_nonneg _
  | some a =>
      have ha : leafCellProfile d (NTSP.intVec (c a)) (P.inputMomentum k x a) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hx) a (Finset.mem_univ a)
      exact tsupport_leafCellProfile_subset d (NTSP.intVec (c a)) (subset_closure ha)

end WaveTurbulence.Incoh
