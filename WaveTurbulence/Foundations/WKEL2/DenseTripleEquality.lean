/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending identities from three dense input sets
-/

public section

namespace WaveTurbulence.WKEL2

/-- Jointly continuous identities extend from a dense set in each of three variables. -/
theorem dense_triple_ext {S E F : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    {e : S → E} (he : DenseRange e) {f g : E → E → E → F}
    (hf : Continuous (fun p : E × E × E => f p.1 p.2.1 p.2.2))
    (hg : Continuous (fun p : E × E × E => g p.1 p.2.1 p.2.2))
    (h : ∀ x y z, f (e x) (e y) (e z) = g (e x) (e y) (e z)) (x y z : E) :
    f x y z = g x y z := by
  have H := (he.prodMap (he.prodMap he)).equalizer hf hg
    (funext fun p => h p.1 p.2.1 p.2.2)
  exact congrFun H (x, y, z)

end WaveTurbulence.WKEL2
