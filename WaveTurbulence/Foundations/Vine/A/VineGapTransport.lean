/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescription
/-! VINE-A2: exact decorated gap transport of actual ordinary/hyper objects
under the molecular atom/dart isomorphism, retaining the designated deleted bond. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
variable {V V' D D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
  {M : Molecule V D} {N : Molecule V' D'}

/-- A block gap is transported without a sign ambiguity when the ordered joint is carried. -/
theorem blockGap_transport (F : MolIso M N) {d : ℕ} (L : ℝ) (base : Mom d)
    (κ : D' → (Fin d → ℤ)) (S : Finset V) (a : V) (r : Mom d) :
    N.IsBlockGap L base κ (F.img S) (F.e a) r ↔
      M.IsBlockGap L base (κ ∘ F.d) S a r := by
  constructor
  · rintro ⟨x', y', hx, hy, hSx, hSy, hox, hoy, hr⟩
    obtain ⟨x, rfl⟩ := F.d.surjective x'
    obtain ⟨y, rfl⟩ := F.d.surjective y'
    exact ⟨x, y, F.e.injective ((F.atom_comm x).symm.trans hx),
      F.e.injective ((F.atom_comm y).symm.trans hy), (F.inGroup_img S x).mp hSx,
      (F.inGroup_img S y).mp hSy, (F.out_comm x).symm.trans hox, (F.out_comm y).symm.trans hoy, hr⟩
  · rintro ⟨x, y, hx, hy, hSx, hSy, hox, hoy, hr⟩
    exact ⟨F.d x, F.d y, (F.atom_comm x).trans (congrArg F.e hx),
      (F.atom_comm y).trans (congrArg F.e hy), (F.inGroup_img S x).mpr hSx,
      (F.inGroup_img S y).mpr hSy, (F.out_comm x).trans hox, (F.out_comm y).trans hoy, hr⟩

/-- Transport the actual shape and, for a hyper-object, its actual deleted bond. -/
def mapShape (F : MolIso M N) {S : Finset V} {a b : V} (C : VineLikeObject M S a b) :
    VineLikeObject N (F.img S) (F.e a) (F.e b) := by
  cases C with
  | vc h => exact .vc (F.isVC_img h)
  | hyper R => exact .hyper ⟨F.d R.added, F.ends_img R.ends_eq, (F.erase R.added).isVC_img R.adjoint⟩

/-- The map of a designated object keeps its designation; it does not rechoose one. -/
def mapObject (F : MolIso M N) (O : Object M) : Object N where
  atoms := F.img O.atoms
  upper := F.e O.upper
  lower := F.e O.lower
  shape := mapShape F O.shape

/-- Ordered gaps of transported shape data agree for corresponding decorations. -/
theorem mapShape_gap (F : MolIso M N) {S : Finset V} {a b : V} (C : VineLikeObject M S a b)
    {d : ℕ} (L : ℝ) (base : Mom d) (κ : D' → (Fin d → ℤ)) (r : Mom d) :
    (mapShape F C).IsGap L base κ r ↔ C.IsGap L base (κ ∘ F.d) r := by
  cases C with
  | vc h => exact blockGap_transport F L base κ S a r
  | hyper R => exact blockGap_transport (F.erase R.added) L base (fun x => κ x.1) S a r

/-- Consequently every SG/LG/ZG predicate agrees, including the hyper-adjoint case. -/
theorem mapObject_gapKind (F : MolIso M N) (O : Object M) {d : ℕ}
    (L γ η : ℝ) (base : Mom d) (κ : D' → (Fin d → ℤ)) (k : Molecule.GapKind) :
    (mapObject F O).HasGapKind L γ η base κ k ↔ O.HasGapKind L γ η base (κ ∘ F.d) k := by
  constructor
  · rintro ⟨r, hr, hk⟩
    exact ⟨r, (mapShape_gap F O.shape L base κ r).mp hr, hk⟩
  · rintro ⟨r, hr, hk⟩
    exact ⟨r, (mapShape_gap F O.shape L base κ r).mpr hr, hk⟩

end WaveTurbulence.VineA
