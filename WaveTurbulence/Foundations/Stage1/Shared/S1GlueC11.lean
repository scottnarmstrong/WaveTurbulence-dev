/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC10
import Mathlib.Tactic

/-!
# Gluing a template couple: the coherent couple insertion record

**`GlueC.insertion`**: from a template `T` carrying `Q` with its layer pattern at `(aT, bT)`, and a base
`LN` whose parent layers at the two roots equal those of the template, the glued layered garden
is a coherent insertion of `Q` into `LN` at `(a, b)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

theorem glued_parAt_a : parAt h.glued p a = parAt T p aT := by
  rw [h.hpa]
  exact (h.outAgree.parAt_eq_a h.indep h.embN.nodeA h.embM.nodeA).symm

theorem glued_parAt_b : parAt h.glued p b = parAt T p bT := by
  rw [h.hpb]
  exact (h.outAgree.parAt_eq_b h.indep h.embN.nodeB h.embM.nodeB).symm

theorem glued_pattern (hT : LayerPattern T p Q aT bT) : LayerPattern h.glued p Q a b := by
  have ha : couplePort a b aT bT a = aT := by simpa [addrExt] using h.port_a []
  have hb : couplePort a b aT bT b = bT := by simpa [addrExt] using h.port_b []
  refine layerPattern_map (LG := T) (couplePort a b aT bT) Q a b p h.respects_a h.respects_b
    (fun x hx => h.glued_region hx) ?_ ?_ ?_
  · rw [ha]; exact h.glued_parAt_a
  · rw [hb]; exact h.glued_parAt_b
  · rw [ha, hb]; exact hT

/-- **The glued layered garden is a coherent couple insertion** into the base. -/
theorem insertion (hT : LayerPattern T p Q aT bT) (hwf : Q.wf = true)
    (hsig : G.sig = LN.garden.sig) (hpos : nodeSign LN.garden.sig a = 1)
    (hneg : nodeSign LN.garden.sig b = -1) :
    CoherentCoupleInsertion p LN h.glued a b Q where
  wf := hwf
  signature := hsig
  positive := hpos
  negative := hneg
  oldEmbedding := h.embN
  newEmbedding := h.embM
  outside := h.outAgree
  pattern := h.glued_pattern hT

end GlueC
end WaveTurbulence.Stage1
