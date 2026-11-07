/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Base1

/-! # ZP-SURJ: exceptional data from coherent objects -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

theorem coherentTree_lone {p q q' : ℕ} {X : RegChain} {LX : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q' X LX) : layerAt LX ((0 : Fin 1), X.lonePath) = q' := by
  obtain ⟨hwf, hX, w', H, a, t, hcan, hemb, hsa, hcoh, hpa, hlone, hlay⟩ := h
  have hT0 : LX.garden.tree 0 = X.plug (LX.garden.sig 0) .leaf := hX.1
  have hr' : X.lonePath ∈ (LX.garden.tree 0).nodes := by rw [hT0]; exact lone_mem_nodes X _
  have := hlay ⟨((0 : Fin 1), X.lonePath), hr'⟩
  rw [← layerAt_of_mem LX hr'] at this
  rw [this]; exact hlone

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

/-- **Datum from coherence**: coherent objects with the right numerals form an exceptional datum. -/
theorem datum_of_coherent {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1} {a b c q' : ℕ}
    (hCQ : IsCoherentCoupleAt p a b Q LQ) (hCT : IsCoherentTreeAt p c q' X LX)
    (hmin : min (parAt (s.base ε) p (cA s ε)) (parAt (s.base ε) p (cB s ε)) = min a b)
    (hrA : layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ parAt (s.base ε) p (cA s ε))
    (hrB : layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ parAt (s.base ε) p (cB s ε))
    (hrT : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ parAt (s.base ε) p (tA s ε))
    (hsig : LX.garden.sig 0 = srcSign s ε) (hlone : q' = layerAt (s.base ε) (tA s ε))
    (hsize : X.size + Q.size = (s.data.tree s.placement.lower).size + (s.data.couple s.exceptional).size) :
    ExcDatum s ε Q X LQ LX where
  hQ := hCQ.1
  hX := hCT.1
  dQ := hCQ.2.1
  dX := hCT.2.1
  sig := hsig
  patQ := layerPatternN_change (pattern_of_coherentCouple hCQ) hmin hrA hrB
  patX := by
    have h := pattern_of_coherentTree hCT
    rw [hsig] at h
    exact treePatternN_change h hrT
  lone := by rw [coherentTree_lone hCT, hlone]
  size := hsize

end WaveTurbulence.ZpSurj
