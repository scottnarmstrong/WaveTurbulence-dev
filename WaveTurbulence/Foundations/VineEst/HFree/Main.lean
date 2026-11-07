/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.HFree.Cov
public import WaveTurbulence.Foundations.VineEst.HFree.BadVine

/-! # W2-HFREE (5): `hfreeAt_holds`

`HFreeAt` (HFree.lean) for any bundle families and exceptional factors satisfying `FrameShapeX`/`BotFrameShapeX` (as `bundleFamOf`/`stepX` and
`bundleBotFamOf`/`botX` do: `frameShapeX_bundleFamOf`, `botFrameShapeX_bundleBotFamOf`), `κ0.L ≠ 0` (as `rowFormNE_termsB_fam`), and the
standing premise that the start garden is canonical (`hcan`; without it no member is operative and the statement is false in general).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)


include hLayer in
theorem isCore_of_bad (hM9 : VINEPARAM) (i : Fin n) (hbad : (assemblyPieceAt B i).vineType.IsBad = true)
    (hnA : ¬ AClause hM9 B RD hG layer i) :
    IsCoreCLVine G (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
      (assemblyPieceAt B i).lower := by
  have hCL := assemblyPiece_cl B i
  have hV := (assemblyPieceAt B i).vine
  rcases (Vine.isBad_iff _).mp hbad with hI | hII
  · exact ⟨hV, hCL, Or.inl hI⟩
  · have hcore : ¬ ∃ p ∈ (assemblyPieceAt B i).atoms, ∃ q ∈ (assemblyPieceAt B i).atoms,
        Molecpl.IsTypeIIE G (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower p q :=
      fun h => hnA (aClause_typeII hM9 B RD hG layer hLayer i hII (Or.inl h))
    exact ⟨hV, hCL, Or.inr ⟨hII, hcore⟩⟩

theorem vineAnchor_of_core (i : Fin n)
    (hcore : IsCoreCLVine G (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
      (assemblyPieceAt B i).lower)
    (h : pairOfLeaf G hG ((assemblySourceFamily B).corePlacement ⟨i, hcore⟩).retained ∈ clRegionalPairs hG U) :
    vineAnchor hG B i = some ⟨pairOfLeaf G hG ((assemblySourceFamily B).corePlacement ⟨i, hcore⟩).retained, h⟩ := by
  classical
  have hP := (assemblySourceFamily B).corePlacement_at ⟨i, hcore⟩
  have hex : ∃ P : CorePlacement G, IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P ∧
      pairOfLeaf G hG P.retained ∈ clRegionalPairs hG U := ⟨_, hP, h⟩
  unfold vineAnchor
  rw [dif_pos hex]
  have he := placement_unique hex.choose_spec.1 hP
  congr 2
  exact congrArg (fun P : CorePlacement G => pairOfLeaf G hG P.retained) he

variable {d : ℕ} {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)

/-- **The staged hypothesis `hfree` (R100 F1) holds**, for canonical start gardens. -/
theorem hfreeAt_holds (hM9 : VINEPARAM) (hL : κ0.L ≠ 0) (hXE : FrameShapeX B RD hG layer hLayer BE XE)
    (hXB : BotFrameShapeX B RD hG layer hLayer BX XB)
    (hcan : CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)) :
    HFreeAt B RD hG layer hLayer BE BX XE XB hM9 := by
  intro ψ hψ
  obtain ⟨recs, Dm, hbody, hcov⟩ := exists_qneR B RD hG layer hLayer BE BX XE XB hL hXE hXB
    (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B) (Nat.le_succ _) ψ hψ
  refine ⟨recs, Dm, hbody, fun i hbad hnA => ?_⟩
  have hcore := isCore_of_bad B RD hG layer hLayer hM9 i hbad hnA
  by_cases hR : TopOp (p := p) (kind := kind) B RD hG layer hLayer (⟨i, hcore⟩ : (assemblySourceFamily B).CoreIndex)
  · left
    obtain ⟨r, hr, hp⟩ := hcov ⟨i, hcore⟩ hR
    have hU : r.p0 ∈ clRegionalPairs hG U := (hbody.1 r hr).2.1
    refine ⟨r, hr, hU, ?_⟩
    have hp' : r.p0 = pairOfLeaf G hG ((assemblySourceFamily B).corePlacement ⟨i, hcore⟩).retained := hp
    have hanc := vineAnchor_of_core B hG i hcore (hp' ▸ hU)
    have hs : (⟨r.p0, hU⟩ : ↥(clRegionalPairs hG U)) =
        ⟨pairOfLeaf G hG ((assemblySourceFamily B).corePlacement ⟨i, hcore⟩).retained, hp' ▸ hU⟩ :=
      Subtype.ext hp'
    rw [hs]
    exact assemblyPairBij_anchor hG B hM9 i _ hanc
  · right
    refine bad_d_vine hM9 B RD hG layer hLayer i (fun P hP ⟨he, ht, hq⟩ => hR ?_) hbad hnA
    have hPe := placement_unique hP ((assemblySourceFamily B).corePlacement_at ⟨i, hcore⟩)
    subst hPe
    exact topOp_of_ready (p := p) (kind := kind) (startState B RD hG layer hLayer) ⟨i, hcore⟩ hcan he ht hq

end WaveTurbulence.VineEstS5C.P4.W2
