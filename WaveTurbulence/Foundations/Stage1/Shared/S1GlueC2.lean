/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC1
import Mathlib.Tactic

/-!
# The glued layer function is a layering (couple case)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- Hypotheses for gluing the template `T` (with `Q` at `(aT, bT)`) into the base `LN` (trivial
couple at `(a, b)`), producing a layering of the garden `G` (with `Q` at `(a, b)`). -/
structure GlueC (LN T : LayeredGarden w) (G : Garden w) (Q : RegCpl) (a b aT bT : Fin w × Path)
    (p : ℕ) : Prop where
  indep : Indep a b
  embN : Embeds LN.garden .triv a b
  embM : Embeds G Q a b
  embT : Embeds T.garden Q aT bT
  node : ∀ z, ¬ InRegion a b z → (z.2 ∈ (G.tree z.1).nodes ↔ z.2 ∈ (LN.garden.tree z.1).nodes)
  leaf : ∀ z, ¬ InRegion a b z → (z.2 ∈ (G.tree z.1).leaves ↔ z.2 ∈ (LN.garden.tree z.1).leaves)
  pair : ∀ (ℓ : GLeaf G.tree) (ℓ' : GLeaf LN.garden.tree), ¬ InRegion a b ℓ.1 → ℓ.1 = ℓ'.1 →
    (G.pair ℓ).1 = (LN.garden.pair ℓ').1
  hpa : parAt T p aT = parAt LN p a
  hpb : parAt T p bT = parAt LN p b
  hp : ∀ n, T.layer n ≤ p

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

theorem port_a (q : Path) : couplePort a b aT bT (addrExt a q) = addrExt aT q :=
  couplePort_a a b aT bT h.indep q

theorem port_b (q : Path) : couplePort a b aT bT (addrExt b q) = addrExt bT q :=
  couplePort_b a b aT bT h.indep q

theorem respects_a : RespectsAt (couplePort a b aT bT) a := by
  intro q
  rw [h.port_a]
  have : couplePort a b aT bT a = aT := by
    have := h.port_a []
    simpa [addrExt] using this
  rw [this]

theorem respects_b : RespectsAt (couplePort a b aT bT) b := by
  intro q
  rw [h.port_b]
  have : couplePort a b aT bT b = bT := by
    have := h.port_b []
    simpa [addrExt] using this
  rw [this]

theorem pairs_port : Q.pairsAt aT bT =
    (Q.pairsAt a b).map (fun r => (couplePort a b aT bT r.1, couplePort a b aT bT r.2)) := by
  have ha : couplePort a b aT bT a = aT := by simpa [addrExt] using h.port_a []
  have hb : couplePort a b aT bT b = bT := by simpa [addrExt] using h.port_b []
  have := couple_pairsAt_map_local Q (couplePort a b aT bT) a b h.respects_a h.respects_b
  rwa [ha, hb] at this

end GlueC
end WaveTurbulence.Stage1
