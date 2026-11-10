/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionTransport
/-! Support alone fixes an object's ordinary/hyper tag and unordered joints.
The actual added bond of a hyper object is deliberately not identified here. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The only two shape constructors used by actual collection choices. -/
def objectHyperTag (O : Object M) : Bool := match O.shape with
  | .vc _ => false
  | .hyper _ => true

/-- Ordinary and hyper block supports cannot coincide: their joint degrees differ. -/
theorem block_not_hyper {S : Finset V} {a b c d : V} (hB : M.IsBlock S a b)
    (e : D) (he : M.ends e = s(c, d)) (hH : (Mole.eraseBond M e).IsBlock S c d) : False := by
  have hd := Mole.hyperBlock_degrees M ⟨e, he, hH⟩
  have h2 := (Mole.block_joint_degrees M hB).1
  by_cases hac : a = c
  · have h3 : M.degIn S a = 3 := hac.symm ▸ hd.1
    omega
  · by_cases had : a = d
    · have h3 : M.degIn S a = 3 := had.symm ▸ hd.2.1
      omega
    · have h4 := hd.2.2 a hB.2.1 hac had
      omega

end WaveTurbulence.VineA
