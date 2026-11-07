/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecDispU
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecF0
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf

/-! # P4-W2 (session 15, step 2b): `rec_step01`, the representation of a step-case record (kinds 0, 1, 3)

For the exceptional factor `X` of a record coming from the operative member `pstar` of a level `lv` (first disjunct of `ExcOf`), at the engine datum
`engDatum .. (consX .. Bex add) g g'`: if the order atoms of the summand (`ordPairs (ordRels ..) (recSlots ..)`) lie in `add` and the summand is not of kind 2, then
`X` equals the engine-variable expression `Xr` (all clocks, all decorations) and `Xr` carries a `PieceRepU` on the pair row `vp` and the branch row `vb` of the record,
with the explicit sign `ε = lowEps lower`, rigid factor `‖r‖` (kind 1) or `1`, bound `Kall d K0 · ofReal (src.sz c)`; the branch momentum is the pair momentum plus `ε r`.
When an order atom is impossible on the engine domain (`ordBad`) the summand vanishes there and the representation is the zero one.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

/-- The branches `lower`, `qb`, `qr` of a step record lie in any region containing the realization of the level. -/
theorem step_mem (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hreal : ∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G U) :
    (lv.split B RD hG layer hLayer pstar hk).tb.U ⊆ U ∧
    ((lv.state B RD hG layer hLayer).family.placement pstar).lower ∈ U ∧
    qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∈ U ∧
    qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∈ U := by
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  have hcU : sp.c.U = lv.c.U := rfl
  have key : ∀ v : GBranch G.tree, v ∈ lv.c.U → v ∈ U := fun v hv =>
    (branch_mem_clRealizationNodes v).mp (hreal _ ((branch_mem_clRealizationNodes v).mpr hv))
  have hsb : sp.sb.U ⊆ lv.c.U := by rw [← hcU, sp.union]; exact Finset.subset_union_left
  have htb : sp.tb.U ⊆ lv.c.U := by rw [← hcU, sp.union]; exact Finset.subset_union_right
  refine ⟨fun v hv => key v (htb hv), ?_, key _ (hsb (qbOf_mem _ sp)), key _ (hsb (qrOf_mem _ sp))⟩
  have := (SplitAt.slow sp).lower_mem
  exact key _ (hsb this)

open VineParamContract in
/-- The three slots of a step record: `t₀` = the lower joint, `s₁`, `t₁` = `qr`/`qb` according to `ν`. -/
noncomputable def recSlots (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (lo qb qr : GBranch G.tree) (ν : ℤˣ) :
    Fin 3 → (assemblyShape hM9 B).TVar ⊕ Fin 3 :=
  ![brSlot hM9 B lo, brSlot hM9 B (if ν = 1 then qr else qb), brSlot hM9 B (if ν = 1 then qb else qr)]

open VineParamContract in
theorem brSlot_wf (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (v : GBranch G.tree) : SlotWf (brSlot hM9 B v) := by
  classical
  intro j hj
  unfold brSlot at hj
  by_cases h : v ∈ clInteriorBranches R
  · rw [dif_pos h] at hj; exact absurd hj (by simp)
  · rw [dif_neg h] at hj; exact (Sum.inr.inj hj).symm

open VineParamContract in
theorem recSlots_wf (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (lo qb qr : GBranch G.tree) (ν : ℤˣ) :
    ∀ i, SlotWf (recSlots hM9 B lo qb qr ν i) := by
  intro i
  fin_cases i <;> exact brSlot_wf hM9 B _

variable {κ0 : KPar P.d} {hprime : IsPrimeGarden G} (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical in
/-- The summand `c` of the bundle family at an operative member, transported to the index type of `bundleExpOf`. -/
noncomputable def castCh (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (c : (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch) :
    (bundleExpOf B RD hG layer hLayer hR lv pstar hk (zpSurj_of_op B RD hG layer hLayer lv pstar hk hop)
        (zpLayers_of_op B RD hG layer hLayer lv pstar hk hop) (retParent _) (SFF lv pstar hk hop)).Ch :=
  cast (congrArg BundleExp.Ch (bundleFamOf_eq_of_op B RD hG layer hLayer hR SFF lv pstar hk hop)) c

open Classical VineParamContract in
theorem rec_step01 {K0 : ℝ≥0∞} {Rb : ℝ} (hdisp : DispK01.{0} P K0) (hd2 : DispK2.{0} P Rb K0)
    (hM9 : VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (wN wDec : ℕ) (hwN : wN + 1 = 30 * P.d)
    (hwDec : wDec = 30 * P.d) (bk : Fin (assemblyShape hM9 B).I → Fin 4) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (hq : W.q = assemblyTimeQ hM9 B (layC RD hG layer))
    (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (c : (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch)
    (hreal : ∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G U)
    (src : Src P (SFF lv pstar hk hop).S (remQ κ0 (zpQfam κ0 (lv.state B RD hG layer hLayer)))
      (remT κ0 (zpTfam κ0 (lv.state B RD hG layer hLayer))) ((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ))
    (xs : ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
      K2.XCross P src) (Kx0 : ℝ) (hKx1 : 1 ≤ Kx0) (hKx : ∀ h, (xs h).Kx ≤ Kx0)
    (hRb : max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ Rb)
    (hgood : ∀ b', (b' ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
        (lv.split B RD hG layer hLayer pstar hk) hprime ∨ b' ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val}
        (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime) → src.good b')
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U)
    (hp0 : p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = (lv.split B RD hG layer hLayer pstar hk).sb.b)
    (X : (GNode G.tree → (Fin P.d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (f : (GNode G.tree → (Fin P.d → ℤ)) → (GNode G.tree → (Fin P.d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y)
    (hrX : ∀ x u, X x u = stepX B RD hG layer hLayer hR SFF lv pstar hk c (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u)
    (hL : κ0.L ≠ 0) (hbcb : lv.c.b = b)
    (Bx : Set (Fin 3 → ℝ))
    (hBx : Bx ⊆ outBox (engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g'))
    (hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1)
    (zc : Prop) (hzb : ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))
        (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (nuOf (lv.state B RD hG layer hLayer) pstar)) → zc)
    (hzq : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) →
      kindOf (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c) = 2 → zc)
    (hts : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) →
      ∃ (sa ta : (assemblyShape hM9 B).TVar),
        (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 1 = Sum.inl sa ∧
          recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 2 = Sum.inl ta) ∧
        sa ≠ ta ∧ ∀ τ : (assemblyShape hM9 B).TVar → ℝ,
          k2f (S := assemblyShape hM9 B) P.η (lv.e pstar).1 τ = ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ))
    (hadd : ¬ zc → ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))
        (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (nuOf (lv.state B RD hG layer hLayer) pstar)) ⊆ add)
    (hzc : zc → ∀ (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ), (∀ s, τ s < tt 0) → ∀ (x y : Mom P.d),
      bundlePtG (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer))
        (SFF lv pstar hk hop).S
        (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
          bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
          else bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
        (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
          bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
          else bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
        (bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
        (bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
        (remQ κ0 (zpQfam κ0 (lv.state B RD hG layer hLayer))) (remT κ0 (zpTfam κ0 (lv.state B RD hG layer hLayer)))
        (Sum.elim τ tt (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 0))
        (Sum.elim τ tt (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 1))
        (Sum.elim τ tt (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
          (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar) 2))
        x y (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c) = 0) :
    ∃ (ε : ℝ) (Xr : ((assemblyShape hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
      |ε| = 1 ∧
      PieceRepU (P := P) (D := engDatum hM9 B hG W wN wDec bk (consX hM9 B (layC RD hG layer) Bex add) g g')
        (assemblyShape_I_pos hM9 B) (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩) ε
        (f0Of P.η (lv.e pstar).1 (kindOf (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))) Xr
        (Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (src.sz (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))) Bx ∧
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
  obtain ⟨hsubtb, hlowU, hqbU, hqrU⟩ := step_mem B RD hG layer hLayer lv pstar hk hreal
  have hsbb : (lv.split B RD hG layer hLayer pstar hk).sb.b = ((lv.state B RD hG layer hLayer).family.placement pstar).lower :=
    (lv.split B RD hG layer hLayer pstar hk).joint.trans (lv.split B RD hG layer hLayer pstar hk).bk
  have hcb : (lv.split B RD hG layer hLayer pstar hk).tb.b = b := (lv.split B RD hG layer hLayer pstar hk).tbb.trans hbcb
  have hbjl := hbj'.trans hsbb
  set ν := nuOf (lv.state B RD hG layer hLayer) pstar with hν
  set ε := lowEps ((lv.state B RD hG layer hLayer).family.placement pstar).lower with hε
  have hν1 : (ν = 1 ∧ (ν : ℂ) = 1) ∨ (ν ≠ 1 ∧ ‖(ν : ℂ)‖ = 1) := by
    rcases Int.units_eq_one_or ν with h1 | h1
    · exact Or.inl ⟨h1, by simp [h1]⟩
    · exact Or.inr ⟨by simp [h1], by simp [h1]⟩
  have hνn : ‖((ν : ℤˣ) : ℂ)‖ = 1 := by
    rcases hν1 with ⟨_, h⟩ | ⟨_, h⟩
    · simp [h]
    · exact h
  set A := lv.state B RD hG layer hLayer with hA
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  set c' := castCh B RD hG layer hLayer hR SFF lv pstar hk hop c with hc'
  set cons := consX hM9 B (layC RD hG layer) Bex add with hcons
  set σ := recSlots hM9 B sp.sb.b (qbOf (A.family.placement pstar)) (qrOf (A.family.placement pstar)) ν with hσ
  have hlay : ∀ v, layOf A v = layC RD hG layer v := fun v => congrFun (lay_lvl B RD hG layer hLayer lv) v
  -- slot values
  have hslot : ∀ (τ : (assemblyShape hM9 B).TVar → ℝ) (tt : Fin 3 → ℝ),
      Sum.elim τ tt (σ 0) = clLocalClock R tt (assemblyClockEquiv hM9 B τ) sp.sb.b ∧
      Sum.elim τ tt (σ 1) = dictS1 ν (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)))
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar))) ∧
      Sum.elim τ tt (σ 2) = dictT1 ν (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qbOf (A.family.placement pstar)))
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ) (qrOf (A.family.placement pstar))) := by
    intro τ tt
    refine ⟨?_, ?_, ?_⟩
    · exact (brSlot_spec hM9 B (hsbb ▸ hlowU) tt τ).symm
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
  set bsA' := bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} A sp hprime with hbsA'
  set bsB' := bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} A sp hprime with hbsB'
  let Xr : ((assemblyShape hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ := fun τ tt rr k =>
    ((ν : ℤˣ) : ℂ) * bundlePtG (CaseA (pstar := pstar) A) (SFF lv pstar hk hop).S
      (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
      (remQ κ0 (zpQfam κ0 A)) (remT κ0 (zpTfam κ0 A))
      (Sum.elim τ tt (σ 0)) (Sum.elim τ tt (σ 1)) (Sum.elim τ tt (σ 2)) (k + ex • rr) (k + ey • rr) c'
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
    obtain ⟨hm1, hm2, hm3⟩ := rec_moms' hM9 B hG W wN wDec bk cons g g' sp hcb hsubtb hL κ0.base β hβ x p0 hp hp0 bj hbj hbjl
    refine ⟨?_, by rw [hm2, hm1]; exact hm3⟩
    rw [hrX, stepX_eq B RD hG layer hLayer hR SFF lv pstar hk hop c f hf]
    show _ = ((ν : ℤˣ) : ℂ) * bundlePtG (CaseA (pstar := pstar) A) (SFF lv pstar hk hop).S
      (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
      (remQ κ0 (zpQfam κ0 A)) (remT κ0 (zpTfam κ0 A)) _ _ _ _ _ c'
    rw [(hslot τ tt).1, (hslot τ tt).2.1, (hslot τ tt).2.2, hm1]
    have hx : ∀ (lo re r : Mom P.d), lo = re + ε • r → re + ex • r = dictX ν lo re := by
      intro lo re r h; unfold dictX; by_cases h1 : ν = 1
      · simp [hex, h1, h]
      · simp [hex, h1]
    have hy : ∀ (lo re r : Mom P.d), lo = re + ε • r → re + ey • r = dictY ν lo re := by
      intro lo re r h; unfold dictY; by_cases h1 : ν = 1
      · simp [hey, h1]
      · simp [hey, h1, h]
    rw [hx _ _ _ hm3, hy _ _ _ hm3]
    rfl
  have hg : ∀ b', (b' ∈ (if CaseA (pstar := pstar) A then bsA' else bsB') ∨ b' ∈ (if CaseA (pstar := pstar) A then bsB' else bsA') ∨
      b' ∈ bsA' ∨ b' ∈ bsB') → src.good b' := by
    intro b' hb'
    apply hgood
    by_cases hc : CaseA (pstar := pstar) A <;> simp only [hc, if_true, if_false] at hb' <;>
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
    show ((ν : ℤˣ) : ℂ) * bundlePtG _ _ _ _ _ _ _ _ _ _ _ _ _ c' = 0
    rw [hzc hz τ tt (hf' hmem).1 _ _, mul_zero]
  · have hbad : ¬ ordBad (ordRels (CaseA (pstar := pstar) A) c') σ := fun h => hz (hzb h)
    have hgd : ∀ b', (b' ∈ (if CaseA (pstar := pstar) A then bsA' else bsB') ∨ b' ∈ (if CaseA (pstar := pstar) A then bsB' else bsA')) →
        src.good b' := fun b' hb' => hg b' (by rcases hb' with h | h <;> simp [h])
    by_cases hk2 : kindOf c' = 2
    · have hne : qbOf (A.family.placement pstar) ≠ qrOf (A.family.placement pstar) := fun h => hz (hzq h hk2)
      obtain ⟨sa, ta, ⟨e1, e2⟩, hab, hk2f⟩ := hts hne
      have hf0 : f0Of (d := P.d) (S := (engDatum hM9 B hG W wN wDec bk cons g g').S) P.η (lv.e pstar).1 (kindOf c') =
          fun τ _ => ((|τ sa - τ ta| ^ (1 - 3 * P.η) : ℝ) : ℂ) := by
        funext τ rr
        unfold f0Of
        rw [if_neg (by omega), if_pos hk2]
        exact hk2f τ
      rw [hf0]
      refine pieceRepU_of_dispK2 hd2 hI hwN hwDec (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩)
        ε ex ey hfl (σ 0) (σ 1) (σ 2) sa ta e1 e2 hab (CaseA (pstar := pstar) A)
        (SFF lv pstar hk hop).S (remQ κ0 (zpQfam κ0 A)) (remT κ0 (zpTfam κ0 A)) src xs Kx0 hKx1 hKx hqh (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hRb
        (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB'
        hgd c' hk2 Bx hBx ?_ ((ν : ℤˣ) : ℂ) hνn
      intro tt htt
      filter_upwards [hfacts tt htt] with τ hf' hmem
      obtain ⟨htop, hcons, hbj_, hqb_, hqr_⟩ := hf' hmem
      have hw := exc_windows A (hq2_of_op B RD hG layer hLayer lv pstar hop)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) hbj_ hqb_ hqr_
      obtain ⟨e0, e1, e2⟩ := hslot τ tt
      refine ⟨excOrd_of_dom _ c' σ (recSlots_wf hM9 B _ _ _ _) τ tt cons htop hcons
        ((hadd hz).trans Finset.subset_union_right) hbad, ?_, ?_, ?_⟩
      · show Sum.elim τ tt (σ 1) ∈ _
        convert hw.2.1 using 1
        exact e1
      · show Sum.elim τ tt (σ 2) ∈ _
        convert hw.2.2 using 1
        exact e2
      · show Sum.elim τ tt (σ 0) ∈ _
        convert hw.1 using 1
        exact e0.trans (congrArg _ hsbb)
    · rw [f0Of_of_ne (S := (engDatum hM9 B hG W wN wDec bk cons g g').S) P.η (lv.e pstar).1 hk2]
      refine PieceRepU.mono (pieceRepU_of_dispK01 hdisp hI hwN hwDec (assemblyPairBij hG B hM9 ⟨p0, hp⟩) (assemblyBranchBij hM9 B ⟨bj, hbj⟩)
        ε ex ey hfl (σ 0) (σ 1) (σ 2) (CaseA (pstar := pstar) A)
        (SFF lv pstar hk hop).S (remQ κ0 (zpQfam κ0 A)) (remT κ0 (zpTfam κ0 A)) src
        (if CaseA (pstar := pstar) A then bsA' else bsB') (if CaseA (pstar := pstar) A then bsB' else bsA') bsA' bsB' hg c' hk2 Bx hBx
        ?_ ((ν : ℤˣ) : ℂ) hνn) (mul_le_mul' (Kall_le_of_ge_one P.d K0 hKx1) le_rfl)
      intro tt htt
      filter_upwards [hfacts tt htt] with τ hf' hmem
      obtain ⟨htop, hcons, hbj_, hqb_, hqr_⟩ := hf' hmem
      have hw := exc_windows A (hq2_of_op B RD hG layer hLayer lv pstar hop)
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) hbj_ hqb_ hqr_
      obtain ⟨e0, e1, e2⟩ := hslot τ tt
      refine ⟨excOrd_of_dom _ c' σ (recSlots_wf hM9 B _ _ _ _) τ tt cons htop hcons
        ((hadd hz).trans Finset.subset_union_right) hbad, ?_, ?_, ?_⟩
      · show Sum.elim τ tt (σ 1) ∈ _
        convert hw.2.1 using 1
        exact e1
      · show Sum.elim τ tt (σ 2) ∈ _
        convert hw.2.2 using 1
        exact e2
      · show Sum.elim τ tt (σ 0) ∈ _
        convert hw.1 using 1
        exact e0.trans (congrArg _ hsbb)
  · intro hz tt htt
    filter_upwards [hfacts tt htt] with τ hf' hmem rr k
    show ((ν : ℤˣ) : ℂ) * bundlePtG _ _ _ _ _ _ _ _ _ _ _ _ _ c' = 0
    rw [hzc hz τ tt (hf' hmem).1 _ _, mul_zero]
