/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreIIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreIIIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreIVAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreVAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreVIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIIAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineTemplatePaths
public import WaveTurbulence.Foundations.Molecule.VineExpansionEndpoints
import Mathlib.Tactic

/-! # Every base template has no separating atom -/

public section
namespace WaveTurbulence.Vine

/-- A path in an old graph avoids every atom beyond its endpoint range. -/
theorem path_avoids_outside {n : ℕ} {es : List (ℕ×ℕ)} (hb : EdgeBounded n es)
    {z u v : ℕ} (hz : n ≤ z) (hp : Relation.EqvGen (EdgeAdj es) u v) :
    AvoidPath es z u v := by
  induction hp with
  | rel u v huv =>
    have hh := hb.adj huv
    exact Relation.EqvGen.rel _ _ ⟨by omega,by omega,huv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Explicit checked paths connect all surviving base atoms to one root. -/
theorem template_avoid_paths (X : VineType) (z v : ℕ) (hz : z<X.template.n)
    (hv : v<X.template.n) (hvz : v ≠ z) :
    AvoidPath X.template.bonds z (if z=0 then 1 else 0) v := by
  cases X with
  | I => exact coreI_avoid_paths z v hz hv hvz
  | II => exact coreII_avoid_paths z v hz hv hvz
  | III => exact coreIII_avoid_paths z v hz hv hvz
  | IV => exact coreIV_avoid_paths z v hz hv hvz
  | V => exact coreV_avoid_paths z v hz hv hvz
  | VI => exact coreVI_avoid_paths z v hz hv hvz
  | VII => exact coreVII_avoid_paths z v hz hv hvz
  | VIII => exact coreVIII_avoid_paths z v hz hv hvz

/-- Each pinned base vine remains connected after any single atom is removed. -/
theorem template_vertexConnected (X : VineType) : VertexConnected X.template.n X.template.bonds := by
  intro z u v hu hv huz hvz
  by_cases hz : z<X.template.n
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (template_avoid_paths X z u hz hu huz))
      (template_avoid_paths X z v hz hv hvz)
  · exact path_avoids_outside (template_endpoints X) (by omega)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (template_paths X u hu))
        (template_paths X v hv))

end WaveTurbulence.Vine
