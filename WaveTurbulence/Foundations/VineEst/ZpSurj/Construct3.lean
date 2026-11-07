/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct2

/-! # ZP-SURJ: the construction of an LF operation realizing an exceptional datum -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

theorem midG_layer_tA (hD : ExcDatum s ε Q X LQ LX) :
    layerAt (midG hD) (tA s ε) = layerAt (s.base ε) (tA s ε) :=
  ((graftC_outAgree (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ) (exc_gout Q hD.hQ)
    hD.dQ hD.rootA hD.rootB).layer _ (notRegion_tA Q hD.hQ)).symm

theorem midG_parAt_tA (hD : ExcDatum s ε Q X LQ LX) :
    parAt (midG hD) p (tA s ε) = parAt (s.base ε) p (tA s ε) := by
  have hA := graftC_outAgree (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ)
    (exc_gout Q hD.hQ) hD.dQ hD.rootA hD.rootB
  have hz : (tA s ε).2 ∈ ((s.base ε).garden.tree (tA s ε).1).nodes :=
    ((s.baseData ε).decodedNode (s.chosen_plain ε) (s.base_decodes ε) (s.branches ε s.placement.lower).toNode).2
  have hz' : (tA s ε).2 ∈ ((midG hD).garden.tree (tA s ε).1).nodes :=
    ((s.midData ε Q hD.hQ).decodedNode (s.chosen_plain ε) ((s.midData ε Q hD.hQ).garden_decodes _)
      (s.branches ε s.placement.lower).toNode).2
  exact (hA.symm.parAt_eq_out (notRegion_tA Q hD.hQ) hz' hz)

theorem ExcDatum.lone' (hD : ExcDatum s ε Q X LQ LX) :
    layerAt LX ((0 : Fin 1), X.lonePath) = layerAt (midG hD) (tA s ε) := by
  rw [midG_layer_tA]; exact hD.lone

theorem ExcDatum.root' (hD : ExcDatum s ε Q X LQ LX) :
    layerAt LX ((0 : Fin 1), ([] : Path)) ≤ parAt (midG hD) p (tA s ε) := by
  rw [midG_parAt_tA]
  by_cases hn : X.isNil = true
  · have hX : X = .nil := by cases X <;> simp_all [RegChain.isNil]
    subst hX
    have h1 := hD.lone
    simp only [RegChain.lonePath] at h1
    rw [h1]
    have hc := (s.base_canonical ε).criterion.1
    have hz : (tA s ε).2 ∈ ((s.base ε).garden.tree (tA s ε).1).nodes :=
      ((s.baseData ε).decodedNode (s.chosen_plain ε) (s.base_decodes ε) (s.branches ε s.placement.lower).toNode).2
    exact layerAt_le_parAt (s.base ε) p hc hz
  · exact treePatternN_root_le hD.patX (by simpa using hn)

theorem ExcDatum.hEX (hD : ExcDatum s ε Q X LQ LX) :
    ChainEmb LX.garden X (srcSign s ε) ((0 : Fin 1), ([] : Path)) .leaf := by
  have h := ChainEmb.of_decodesTree hD.dX
  rw [hD.sig] at h
  exact h

end WaveTurbulence.ZpSurj
