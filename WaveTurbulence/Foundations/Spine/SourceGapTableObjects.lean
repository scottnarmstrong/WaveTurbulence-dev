/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceGapTable
/-! Designated ordinary and hyper vine gap tags depend only on the finite local gap table. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset

 theorem block_gap_kind_congr {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (κ κ' : D → (Fin d → ℤ))
    (h : ∀ x y, M.atom x = M.atom y →
      Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) =
        Molecule.gapKind L γ η (Molecule.gapAt L base κ' x y))
    (S : Finset V) (a : V) (kind : Molecule.GapKind) :
    (∃ r, M.IsBlockGap L base κ S a r ∧ Molecule.gapKind L γ η r = kind) ↔
      ∃ r, M.IsBlockGap L base κ' S a r ∧ Molecule.gapKind L γ η r = kind := by
  have hforward (κ κ' : D → (Fin d → ℤ))
      (he : ∀ x y, M.atom x = M.atom y →
        Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) =
          Molecule.gapKind L γ η (Molecule.gapAt L base κ' x y)) :
      (∃ r, M.IsBlockGap L base κ S a r ∧ Molecule.gapKind L γ η r = kind) →
        ∃ r, M.IsBlockGap L base κ' S a r ∧ Molecule.gapKind L γ η r = kind := by
    rintro ⟨r, ⟨x, y, hx, hy, hxS, hyS, hxo, hyo, hr⟩, hkind⟩
    subst r
    exact ⟨_, ⟨x, y, hx, hy, hxS, hyS, hxo, hyo, rfl⟩,
      (he x y (hx.trans hy.symm)).symm.trans hkind⟩
  exact ⟨hforward κ κ' h, hforward κ' κ (fun x y hxy => (h x y hxy).symm)⟩

 theorem sourceGapTable_object_kind_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (P : SourceVine.Object G.molecule) (kind : Molecule.GapKind) :
    P.HasGapKind L γ η base κ kind ↔ P.HasGapKind L γ η base κ' kind := by
  have hloc := sourceGapTable_eq_apply G L γ η base κ κ' h
  unfold SourceVine.Object.HasGapKind SourceVine.VineLikeObject.IsGap
  cases P.shape with
  | vc hvc => exact block_gap_kind_congr G.molecule L γ η base κ κ' hloc P.atoms P.upper kind
  | hyper Q =>
    unfold SourceVine.HyperLikeRealization.IsGap
    apply block_gap_kind_congr (Molecule.eraseBond G.molecule Q.added) L γ η base _ _
    intro x y hxy
    have hh : G.molecule.atom x.1 = G.molecule.atom y.1 := hxy
    exact hloc x.1 y.1 hh

end WaveTurbulence.LGSpine
