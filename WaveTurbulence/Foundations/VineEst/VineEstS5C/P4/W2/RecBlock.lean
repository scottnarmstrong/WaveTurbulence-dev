/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.HFree.Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep


/-! # P4-W2 (session 16, step 3a): the block of a record

A record `r` of an `ExcOf` witness comes from an operative member `pstar` of a level `lv`; the state of a level is a restriction of the start state, so its placement at `pstar` is the
core placement of the member `lv.e pstar = ⟨i, hcore⟩`, and `r.p0` is the anchor pair of the vine `i` (`vineAnchor_of_core`).  Hence `(assemblyPairBij ⟨r.p0, _⟩).1 = i = r.blk`, and
two records with distinct pairs have distinct blocks.
-/


@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {d : ℕ} {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)

/-- **The anchor of a record**: the pair `r.p0` is the anchor pair of the vine `r.blk`. -/
theorem excOf_anchor {V : Finset (GBranch G.tree)} {r : ExcRec G d}
    (h : ExcOf B RD hG layer hLayer BE BX XE XB V r) (hp : r.p0 ∈ clRegionalPairs hG U) :
    ∃ i : Fin n, vineAnchor hG B i = some ⟨r.p0, hp⟩ ∧ i.val = r.blk := by
  classical
  have key : ∀ (e : (assemblySourceFamily B).CoreIndex),
      r.p0 = pairOfLeaf G hG ((assemblySourceFamily B).corePlacement e).retained → r.blk = e.1.val →
      ∃ i : Fin n, vineAnchor hG B i = some ⟨r.p0, hp⟩ ∧ i.val = r.blk := by
    intro e hpe hbe
    have hp' : pairOfLeaf G hG ((assemblySourceFamily B).corePlacement e).retained ∈ clRegionalPairs hG U := hpe ▸ hp
    have hanc := vineAnchor_of_core B hG e.1 e.2 hp'
    refine ⟨e.1, ?_, hbe.symm⟩
    have hs : (⟨r.p0, hp⟩ : ↥(clRegionalPairs hG U)) =
        ⟨pairOfLeaf G hG ((assemblySourceFamily B).corePlacement e).retained, hp'⟩ := Subtype.ext hpe
    rw [hs]; exact hanc
  rcases h with ⟨lv, pstar, hk, hop, c, f, -, -, hp0, -, hblk, -⟩ | ⟨lv, pstar, h0, hop, hmax, c, f, -, -, hp0, -, hblk, -⟩
  · exact key (lv.e pstar) hp0 hblk
  · exact key (lv.e pstar) hp0 (hblk.trans h0.symm)

/-- Records with distinct pairs have distinct blocks (the anchor pair of a vine is unique). -/
theorem excOf_block_inj {V V' : Finset (GBranch G.tree)} {r r' : ExcRec G d}
    (h : ExcOf B RD hG layer hLayer BE BX XE XB V r) (h' : ExcOf B RD hG layer hLayer BE BX XE XB V' r')
    (hp : r.p0 ∈ clRegionalPairs hG U) (hp' : r'.p0 ∈ clRegionalPairs hG U) (hblk : r.blk = r'.blk) : r.p0 = r'.p0 := by
  obtain ⟨i, hi, hiv⟩ := excOf_anchor B RD hG layer hLayer BE BX XE XB h hp
  obtain ⟨i', hi', hiv'⟩ := excOf_anchor B RD hG layer hLayer BE BX XE XB h' hp'
  have : i = i' := Fin.ext (hiv.trans (hblk.trans hiv'.symm))
  subst this
  have := hi.symm.trans hi'
  exact congrArg (fun z : Option ↥(clRegionalPairs hG U) => (z.map Subtype.val).getD r.p0) this

/-- The block index (in the engine shape) of a record is its `blk`. -/
theorem excOf_pairBij_fst (hM9 : VineParamContract.VINEPARAM) {V : Finset (GBranch G.tree)} {r : ExcRec G d}
    (h : ExcOf B RD hG layer hLayer BE BX XE XB V r) (hp : r.p0 ∈ clRegionalPairs hG U) :
    ((assemblyPairBij hG B hM9 ⟨r.p0, hp⟩).1 : ℕ) = r.blk := by
  obtain ⟨i, hi, hiv⟩ := excOf_anchor B RD hG layer hLayer BE BX XE XB h hp
  have := assemblyPairBij_anchor hG B hM9 i ⟨r.p0, hp⟩ hi
  rw [this]; exact hiv

end WaveTurbulence.VineEstS5C.P4.W2
