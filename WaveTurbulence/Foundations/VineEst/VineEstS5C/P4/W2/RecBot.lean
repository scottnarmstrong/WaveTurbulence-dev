/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf

/-! # P4-W2 (session 16, step 1): `rec_bot01`, the representation of a bottom-case record (kinds 0, 1, 3)

For the exceptional factor `X` of a record coming from the bottom operative member `pstar` of a level `lv` (second disjunct of `ExcOf`; `botX_eq`), at the engine datum
`engDatum .. (consX .. Bex add) g g'`: if the order atoms of the summand (`ordPairs (ordRels ..) (recSlots ..)`) lie in `add` and the summand is not of kind 2, then
`X` equals the engine-variable expression `Xr` (all clocks, all decorations) and `Xr` carries a `PieceRepU` on the pair row `vp` and the branch row `vb` of the record,
with the explicit sign `ε = lowEps lower`, rigid factor `‖r‖` (kind 1) or `1`, bound `Kall d K0 · ofReal (src.sz c)`; the branch momentum is the pair momentum plus `ε r`.
When an order atom is impossible on the engine domain (`ordBad`) the summand vanishes there and the representation is the zero one.
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


variable {κ0 : KPar P.d} {hprime' : IsPrimeGarden G} (hR : RealityAll) (BSFF : BotSepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

theorem region_kept_eq {U1 U2 : Finset (GBranch G.tree)} {a1 a2 b1 b2 : GBranch G.tree} (h : U1 ⊆ U2) (hb : b1 = b2)
    (R1 : CLRegionData G U1 a1 b1) (R2 : CLRegionData G U2 a2 b2) : R1.kept = R2.kept := by
  subst hb
  exact (region_lower_eq_of_subset h R1 R2).1

open Classical VineParamContract in
theorem rec_bot01 {K0 : ℝ≥0∞} {Rb : ℝ} (hdisp : DispK01.{0} P K0) (hd2 : DispK2.{0} P Rb K0)
    (hM9 : VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d)
    (hwDec : wDec = 30 * P.d) (bk : Fin (assemblyShape hM9 B).I → Fin 4) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (hq : W.q = assemblyTimeQ hM9 B (layC RD hG layer))
    (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF lv pstar h0 hop hmax).Ch)
    (hreal : ∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G U)
    (src : Src P (BSFF lv pstar h0 hop hmax).S
      (botRemQ pstar κ0 (botQfam pstar κ0 (lv.state B RD hG layer hLayer)))
      (botRemT pstar κ0 (botTfam pstar κ0 (lv.state B RD hG layer hLayer)))
      ((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ))
    (xs : ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
      K2.XCross P src) (Kx0 : ℝ) (hKx1 : 1 ≤ Kx0) (hKx : ∀ h, (xs h).Kx ≤ Kx0)
    (hRb : max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ Rb)
    (hgood : ∀ b', (b' ∈ botA p kind pstar (lv.state B RD hG layer hLayer) lv.c ∨
        b' ∈ botB p kind pstar (lv.state B RD hG layer hLayer) lv.c) → src.good b')
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U)
    (hp0 : p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = lv.c.b)
    (X : (GNode G.tree → (Fin P.d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (f : (GNode G.tree → (Fin P.d → ℤ)) → (GNode G.tree → (Fin P.d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y)
    (hrX : ∀ x u, X x u = botX B RD hG layer hLayer hR hprime' BSFF lv pstar h0 hop hmax c (f x) u)
    (hL : κ0.L ≠ 0) (hbcb : lv.c.b = b)
    (Bx : Set (Fin 3 → ℝ))
    (hBx : Bx ⊆ outBox (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g'))
    (hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1)
    (zc : Prop) (hzb : ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (c))
        (recSlots hM9 B lv.c.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (nuOf (lv.state B RD hG layer hLayer) pstar)) → zc)
    (hzq : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) → kindOf c = 2 → zc)
    (hts : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) →
      ∃ (sa ta : (assemblyShape hM9 B).TVar),
        (recSlots hM9 B lv.c.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 1 = Sum.inl sa ∧
          recSlots hM9 B lv.c.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 2 = Sum.inl ta) ∧
        sa ≠ ta ∧ ∀ τ : (assemblyShape hM9 B).TVar → ℝ,
          k2f (S := assemblyShape hM9 B) P.η (lv.e pstar).1 τ = ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ))
    (hadd : ¬ zc → ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (c))
        (recSlots hM9 B lv.c.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (nuOf (lv.state B RD hG layer hLayer) pstar)) ⊆ add)
    (hzc : zc → ∀ (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ), (∀ s, τ s < tt 0) → ∀ (x y : Mom P.d),
      bundlePtG (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (BSFF lv pstar h0 hop hmax).S
        (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then botA p kind pstar (lv.state B RD hG layer hLayer) lv.c
          else botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
        (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then botB p kind pstar (lv.state B RD hG layer hLayer) lv.c
          else botA p kind pstar (lv.state B RD hG layer hLayer) lv.c)
        (botA p kind pstar (lv.state B RD hG layer hLayer) lv.c) (botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
        (botRemQ pstar κ0 (botQfam pstar κ0 (lv.state B RD hG layer hLayer)))
        (botRemT pstar κ0 (botTfam pstar κ0 (lv.state B RD hG layer hLayer)))
        (Sum.elim τ tt (recSlots hM9 B lv.c.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 0))
        (Sum.elim τ tt (recSlots hM9 B lv.c.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 1))
        (Sum.elim τ tt (recSlots hM9 B lv.c.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 2))
        x y c = 0) :
    ∃ (ε : ℝ) (Xr : ((assemblyShape hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      |ε| = 1 ∧
      PieceRepU (P := P) (D := engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g')
        (assemblyShape_I_pos hM9 B) (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩) ε
        (f0Of P.η (lv.e pstar).1 (kindOf c)) Xr
        (Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz (c))) Bx ∧
      (zc → ∀ tt ∈ Bx, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
        τ ∈ (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g').timeDom
          (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) → ∀ (rr k : Mom P.d), Xr τ tt rr k = 0) ∧
      ∀ (β : Fin 4 → (Fin P.d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin P.d → ℤ)) (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ),
        X (clExtendIndices R ((clNormalizedChainEquiv hL B κ0.base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
          Xr τ tt (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
              (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
              (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩))) ∧
        rowMom (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
            (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
            (Sum.inr (assemblyBranchBij hM9 B ⟨bj, hbj⟩)) =
          rowMom (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
            (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
            (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩)) +
          ε • (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1) := by
  classical
  have hI := assemblyShape_I_pos hM9 B
  set A := lv.state B RD hG layer hLayer with hA
  have hlowc : lv.c.b = (A.family.placement pstar).lower := Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0
  have hSlow := chain_slow lv.c pstar hlowc
  have key : ∀ v : GBranch G.tree, v ∈ lv.c.U → v ∈ U := fun v hv =>
    (branch_mem_clRealizationNodes v).mp (hreal _ ((branch_mem_clRealizationNodes v).mpr hv))
  have hlowU : (A.family.placement pstar).lower ∈ U := key _ hSlow.lower_mem
  have hqbU : qbOf (A.family.placement pstar) ∈ U := key _ (bot_qbOf_mem A lv.c hlowc)
  have hqrU : qrOf (A.family.placement pstar) ∈ U := key _ (bot_qrOf_mem A lv.c hlowc)
  have hlowR : (A.family.placement pstar).lower.toNode ∈ clRealizationNodes G lv.c.U :=
    (branch_mem_clRealizationNodes _).mpr hSlow.lower_mem
  have hretR : (A.family.placement pstar).retained.toNode ∈ clRealizationNodes G lv.c.U :=
    (leaf_mem_clRealizationNodes _).mpr hSlow.retained_internal
  have hfl' : ∀ x, f x (A.family.placement pstar).lower.toNode = x (A.family.placement pstar).lower.toNode :=
    fun x => hf x _ hlowR
  have hfr' : ∀ x, f x (A.family.placement pstar).retained.toNode = x (A.family.placement pstar).retained.toNode :=
    fun x => hf x _ hretR
  have hsubU : lv.c.U ⊆ U := fun v hv => key v hv
  have hkeep : R.kept = (A.family.placement pstar).keep := by
    have := region_kept_eq hsubU hbcb (clRegionData A.skeleton lv.c.block lv.c.cl) R
    exact this.symm.trans hSlow.keep
  have hbU : lv.c.b ∈ U := key _ (hlowc ▸ hSlow.lower_mem)
  have hbU' : b ∈ U := hbcb ▸ hbU
  set ν := nuOf A pstar with hν
  set ε := lowEps (A.family.placement pstar).lower with hε
  have hν1 : (ν = 1 ∧ (ν : ℂ) = 1) ∨ (ν ≠ 1 ∧ ‖(ν : ℂ)‖ = 1) := by
    rcases Int.units_eq_one_or ν with h1 | h1
    · exact Or.inl ⟨h1, by simp [h1]⟩
    · exact Or.inr ⟨by simp [h1], by simp [h1]⟩
  have hνn : ‖((ν : ℤˣ) : ℂ)‖ = 1 := by
    rcases hν1 with ⟨_, h⟩ | ⟨_, h⟩
    · simp [h]
    · exact h
  set cons := consX hM9 B (layC RD hG layer) Bex add with hcons
  set σ := recSlots hM9 B lv.c.b (qbOf (A.family.placement pstar)) (qrOf (A.family.placement pstar)) ν with hσ
  have hlay : ∀ v, layOf A v = layC RD hG layer v := fun v => congrFun (lay_lvl B RD hG layer hLayer lv) v
  have hslot : ∀ (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ),
      Sum.elim τ tt (σ 0) = clLocalClock R tt (assemblyClockEquiv hM9 B τ) lv.c.b ∧
      Sum.elim τ tt (σ 1) = dictS1 ν (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)))
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar))) ∧
      Sum.elim τ tt (σ 2) = dictT1 ν (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)))
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar))) := by
    intro τ tt
    refine ⟨?_, ?_, ?_⟩
    · exact (brSlot_spec hM9 B hbU tt τ).symm
    · have := (brSlot_spec hM9 B (v := if ν = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar))
        (by split_ifs <;> assumption) tt τ).symm
      show Sum.elim τ tt (brSlot hM9 B _) = _
      rw [this]; unfold dictS1; split_ifs <;> rfl
    · have := (brSlot_spec hM9 B (v := if ν = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar))
        (by split_ifs <;> assumption) tt τ).symm
      show Sum.elim τ tt (brSlot hM9 B _) = _
      rw [this]; unfold dictT1; split_ifs <;> rfl
  have hfacts : ∀ tt ∈ Bx, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom hI (tt 0) (tt 1) (tt 2) →
        (∀ s, τ s < tt 0) ∧ (∀ c ∈ cons, τ c.1 < τ c.2) ∧
        ((layOf A (A.family.placement pstar).lower : ℝ) < clLocalClock R tt (assemblyClockEquiv hM9 B τ) (A.family.placement pstar).lower ∧
          clLocalClock R tt (assemblyClockEquiv hM9 B τ) (A.family.placement pstar).lower < layOf A (A.family.placement pstar).lower + 1) ∧
        ((layOf A (qbOf (A.family.placement pstar)) : ℝ) < clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)) ∧
          clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)) < layOf A (qbOf (A.family.placement pstar)) + 1) ∧
        ((layOf A (qrOf (A.family.placement pstar)) : ℝ) < clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar)) ∧
          clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar)) < layOf A (qrOf (A.family.placement pstar)) + 1) := by
    intro tt htt
    have hae : ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ, ∀ s, τ s ≠ assemblyTimeQ hM9 B (layC RD hG layer) s ∧
        τ s ≠ assemblyTimeQ hM9 B (layC RD hG layer) s + 1 := by
      rw [ae_all_iff]
      intro s
      exact (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _).and
        (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _)
    filter_upwards [hae] with τ hτ hmem
    have hDom := (mem_engTimeDom_iff' hM9 B hG W wN wDec bk cons g g' tt τ).mp hmem
    have hDom' : EngDomP hM9 B (assemblyTimeQ hM9 B (layC RD hG layer)) cons hI tt τ := by rw [← hq]; exact hDom
    have hdx := engDom_to_domX hM9 B (layC RD hG layer) Bex add hI tt τ hτ hDom'
    have hext' : ((layC RD hG layer a : ℕ) : ℝ) < clLocalClock R tt (assemblyClockEquiv hM9 B τ) a ∧
        clLocalClock R tt (assemblyClockEquiv hM9 B τ) a < (layC RD hG layer a : ℕ) + 1 := by
      rw [clLocalClock_upper]; exact hext tt htt
    have hw := win_of_domX R (layC RD hG layer) Bex (tt 0) (tt 1) (tt 2) _ hdx hext' (Finset.Subset.refl U)
    refine ⟨fun s => (hDom.1 s).2.2, hDom.2.2, ?_, ?_, ?_⟩
    · rw [hlay]; exact hw _ hlowU
    · rw [hlay]; exact hw _ hqbU
    · rw [hlay]; exact hw _ hqrU
  set ex : ℝ := if ν = 1 then ε else 0 with hex
  set ey : ℝ := if ν = 1 then 0 else ε with hey
  have hfl : FlagXY ε ex ey := by
    refine ⟨abs_lowEps _, ?_⟩
    by_cases h : ν = 1
    · right; simp [hex, hey, h]
    · left; simp [hex, hey, h]
  set bsA' := botA p kind pstar A lv.c with hbsA'
  set bsB' := botB p kind pstar A lv.c with hbsB'
  let Xr : ((assemblyShape hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ := fun τ tt rr k =>
    ((ν : ℤˣ) : ℂ) * bundlePtG (CaseA (pstar := pstar) A) (BSFF lv pstar h0 hop hmax).S
      (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
      (botRemQ pstar κ0 (botQfam pstar κ0 A)) (botRemT pstar κ0 (botTfam pstar κ0 A))
      (Sum.elim τ tt (σ 0)) (Sum.elim τ tt (σ 1)) (Sum.elim τ tt (σ 2)) (k + ex • rr) (k + ey • rr) c
  have hlink : ∀ (β : Fin 4 → (Fin P.d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
      (x : (assemblyShape hM9 B).VIdx → (Fin P.d → ℤ)) (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ),
        X (clExtendIndices R ((clNormalizedChainEquiv hL B κ0.base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
          Xr τ tt (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') κ0.L x
              (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
              (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩))) ∧
        rowMom (engDatum hM9 B hG W wN wDec bk cons g g') κ0.L x
            (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
            (Sum.inr (assemblyBranchBij hM9 B ⟨bj, hbj⟩)) =
          rowMom (engDatum hM9 B hG W wN wDec bk cons g g') κ0.L x
            (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
            (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩)) +
          ε • (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1) := by
    intro β hβ x tt τ
    obtain ⟨hm1, hm2, hm3⟩ := bot_moms' hM9 B hG W wN wDec bk cons g g' hbU' (hlowc.symm.trans hbcb) hkeep hL κ0.base β hβ x p0 hp hp0 bj hbj
      (hbj'.trans hlowc)
    refine ⟨?_, by rw [hm2, hm1]; exact hm3⟩
    rw [hrX, botX_eq B RD hG layer hLayer hR BSFF lv pstar h0 hop hmax c]
    simp only [botVars]
    show _ = ((ν : ℤˣ) : ℂ) * bundlePtG (CaseA (pstar := pstar) A) (BSFF lv pstar h0 hop hmax).S
      (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
      (botRemQ pstar κ0 (botQfam pstar κ0 A)) (botRemT pstar κ0 (botTfam pstar κ0 A)) _ _ _ _ _ c
    rw [(hslot τ tt).1, (hslot τ tt).2.1, (hslot τ tt).2.2]
    have hx : ∀ (lo re r : Mom P.d), lo = re + ε • r → re + ex • r = dictX ν lo re := by
      intro lo re r h; unfold dictX; by_cases h1 : ν = 1
      · simp [hex, h1, h]
      · simp [hex, h1]
    have hy : ∀ (lo re r : Mom P.d), lo = re + ε • r → re + ey • r = dictY ν lo re := by
      intro lo re r h; unfold dictY; by_cases h1 : ν = 1
      · simp [hey, h1]
      · simp [hey, h1, h]
    rw [hm1]
    show _ = ((ν : ℤˣ) : ℂ) * bundlePtG (CaseA (pstar := pstar) A) (BSFF lv pstar h0 hop hmax).S
      (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
      (botRemQ pstar κ0 (botQfam pstar κ0 A)) (botRemT pstar κ0 (botTfam pstar κ0 A)) _ _ _ _ _ c
    rw [hx _ _ _ hm3, hy _ _ _ hm3]
    refine congrArg (fun z => ((ν : ℤˣ) : ℂ) * z) ?_
    congr 1
    all_goals first
      | exact congrArg₂ (dictX _) (congrArg (fun z => κ0.base + latticePoint κ0.L z) (hfl' _))
          (congrArg (fun z => κ0.base + latticePoint κ0.L z) (hfr' _))
      | exact congrArg₂ (dictY _) (congrArg (fun z => κ0.base + latticePoint κ0.L z) (hfl' _))
          (congrArg (fun z => κ0.base + latticePoint κ0.L z) (hfr' _))
  have hg : ∀ b', (b' ∈ (if CaseA (pstar := pstar) A then bsA' else bsB') ∨ b' ∈ (if CaseA (pstar := pstar) A then bsB' else bsA') ∨
      b' ∈ bsA' ∨ b' ∈ bsB') → src.good b' := by
    intro b' hb'
    apply hgood
    by_cases hc : CaseA (pstar := pstar) A <;> simp only [hc, ite_true, ite_false] at hb' <;>
      rcases hb' with h | h | h | h <;> first | exact Or.inl h | exact Or.inr h
  have hqh : ((zpQh A pstar : ℕ) : ℝ) = ((zpQ4 A pstar : ℕ) : ℝ) ∨ ((zpQ4 A pstar : ℕ) : ℝ) + 1 ≤ ((zpQh A pstar : ℕ) : ℝ) := by
    have h := zpQ4_le_zpQh A hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    rcases Nat.eq_or_lt_of_le h with h | h
    · left; exact_mod_cast h.symm
    · right; exact_mod_cast h
  refine ⟨ε, Xr, abs_lowEps _, ?_, ?_, hlink⟩
  by_cases hz : zc
  · refine pieceRepU_zero hI _ _ _ _ _ _ _ (fun tt htt => ?_)
    filter_upwards [hfacts tt htt] with τ hf' hmem r k hr
    show ((ν : ℤˣ) : ℂ) * bundlePtG _ _ _ _ _ _ _ _ _ _ _ _ _ c = 0
    rw [hzc hz τ tt (hf' hmem).1 _ _, mul_zero]
  · have hbad : ¬ ordBad (ordRels (CaseA (pstar := pstar) A) c) σ := fun h => hz (hzb h)
    have hgd : ∀ b', (b' ∈ (if CaseA (pstar := pstar) A then bsA' else bsB') ∨ b' ∈ (if CaseA (pstar := pstar) A then bsB' else bsA')) →
        src.good b' := fun b' hb' => hg b' (by rcases hb' with h | h <;> simp [h])
    by_cases hk2 : kindOf c = 2
    · have hne : qbOf (A.family.placement pstar) ≠ qrOf (A.family.placement pstar) := fun h => hz (hzq h hk2)
      obtain ⟨sa, ta, ⟨e1, e2⟩, hab, hk2f⟩ := hts hne
      have hf0 : f0Of (d := P.d) (S := (engDatum hM9 B hG W wN wDec bk cons g g').S) P.η (lv.e pstar).1 (kindOf c) =
          fun τ _ => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ) := by
        funext τ rr
        unfold f0Of
        rw [if_neg (by omega), if_pos hk2]
        exact hk2f τ
      rw [hf0]
      refine pieceRepU_of_dispK2 hd2 hI hwN hwDec (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩)
        ε ex ey hfl (σ 0) (σ 1) (σ 2) sa ta e1 e2 hab (CaseA (pstar := pstar) A)
        (BSFF lv pstar h0 hop hmax).S (botRemQ pstar κ0 (botQfam pstar κ0 A)) (botRemT pstar κ0 (botTfam pstar κ0 A)) src xs Kx0 hKx1 hKx hqh (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hRb
        (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
        hgd c hk2 Bx hBx ?_ ((ν : ℤˣ) : ℂ) hνn
      intro tt htt
      filter_upwards [hfacts tt htt] with τ hf' hmem
      obtain ⟨htop, hcons, hbj_, hqb_, hqr_⟩ := hf' hmem
      have hw := exc_windows A (hq2_of_op B RD hG layer hLayer lv pstar hop)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) hbj_ hqb_ hqr_
      obtain ⟨e0, e1, e2⟩ := hslot τ tt
      refine ⟨excOrd_of_dom _ c σ (recSlots_wf hM9 B _ _ _ _) τ tt cons htop hcons
        ((hadd hz).trans Finset.subset_union_right) hbad, ?_, ?_, ?_⟩
      · show Sum.elim τ tt (σ 1) ∈ _
        convert hw.2.1 using 1
        exact e1
      · show Sum.elim τ tt (σ 2) ∈ _
        convert hw.2.2 using 1
        exact e2
      · show Sum.elim τ tt (σ 0) ∈ _
        convert hw.1 using 1
        exact e0.trans (congrArg _ hlowc)
    · rw [f0Of_of_ne (S := (engDatum hM9 B hG W wN wDec bk cons g g').S) P.η (lv.e pstar).1 hk2]
      refine PieceRepU.mono (pieceRepU_of_dispK01 hdisp hI hwN hwDec (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩)
        ε ex ey hfl (σ 0) (σ 1) (σ 2) (CaseA (pstar := pstar) A)
        (BSFF lv pstar h0 hop hmax).S (botRemQ pstar κ0 (botQfam pstar κ0 A)) (botRemT pstar κ0 (botTfam pstar κ0 A)) src
        (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB' hg c hk2 Bx hBx
        ?_ ((ν : ℤˣ) : ℂ) hνn) (mul_le_mul' (Kall_le_of_ge_one P.d K0 hKx1) le_rfl)
      intro tt htt
      filter_upwards [hfacts tt htt] with τ hf' hmem
      obtain ⟨htop, hcons, hbj_, hqb_, hqr_⟩ := hf' hmem
      have hw := exc_windows A (hq2_of_op B RD hG layer hLayer lv pstar hop)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) hbj_ hqb_ hqr_
      obtain ⟨e0, e1, e2⟩ := hslot τ tt
      refine ⟨excOrd_of_dom _ c σ (recSlots_wf hM9 B _ _ _ _) τ tt cons htop hcons
        ((hadd hz).trans Finset.subset_union_right) hbad, ?_, ?_, ?_⟩
      · show Sum.elim τ tt (σ 1) ∈ _
        convert hw.2.1 using 1
        exact e1
      · show Sum.elim τ tt (σ 2) ∈ _
        convert hw.2.2 using 1
        exact e2
      · show Sum.elim τ tt (σ 0) ∈ _
        convert hw.1 using 1
        exact e0.trans (congrArg _ hlowc)
  · intro hz tt htt
    filter_upwards [hfacts tt htt] with τ hf' hmem rr k
    show ((ν : ℤˣ) : ℂ) * bundlePtG _ _ _ _ _ _ _ _ _ _ _ _ _ c = 0
    rw [hzc hz τ tt (hf' hmem).1 _ _, mul_zero]

end WaveTurbulence.VineEstS5C.P4.W2
