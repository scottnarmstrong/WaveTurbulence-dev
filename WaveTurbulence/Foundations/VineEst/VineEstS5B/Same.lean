/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowTransport
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Sum

/-! # V5 Step 4d-B: the S-side of a state with the same skeleton (skip or FALSE choice)

`spartFrame_congr`: the frame reads the data only through the ordinary rows and the atom layers.
`sSum_same`: the S-side of the same chart with other data `D2` equals the integral of `frame(D) * exc(D2) * Φ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (p0 : SourcePair G)

section Congr
variable
  (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
    nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
  (hsel : VineEst.SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 ((clRegionalPairs hG S).erase p0)
      ((S.erase a).erase b))

include hC hT hl hsel in
theorem spartFrame_congr (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    spartFrame D1 hG L γ δ F layer1 hLayer1 base S a b p0 x u =
      spartFrame D2 hG L γ δ F layer2 hLayer2 base S a b p0 x u := by
  classical
  unfold spartFrame
  have hdom : DomF (fun v => layer1 (D1.coreBranch hG v).toNode) S a b u ↔
      DomF (fun v => layer2 (D2.coreBranch hG v).toNode) S a b u := by
    unfold DomF
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    simp only []
    rw [hl v hv]
  have hq : ∏ p ∈ (clRegionalPairs hG S).erase p0, qRow D1 hG L γ δ F layer1 hLayer1 base (u a) x u p =
      ∏ p ∈ (clRegionalPairs hG S).erase p0, qRow D2 hG L γ δ F layer2 hLayer2 base (u a) x u p :=
    Finset.prod_congr rfl fun p hp => by unfold qRow; exact VineEst.selCoupleRow_of_selDataEq hsel hp (hC p hp) _ _ _ _ _ _ _
  have ht : ∏ v ∈ (S.erase a).erase b, tRow D1 hG L γ δ F layer1 hLayer1 base (u a) x u v =
      ∏ v ∈ (S.erase a).erase b, tRow D2 hG L γ δ F layer2 hLayer2 base (u a) x u v :=
    Finset.prod_congr rfl fun v hv => by unfold tRow; exact VineEst.selTreeRow_of_selDataEq hsel hv (hT v hv) _ _ _ _ _ _ _
  rw [hq, ht]
  simp only [hdom]

end Congr

section Sum
variable (RS : CLRegionData G S a b) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree)
  (Φ : ℝ → Mom d → Mom d → ℂ)

/-- The integrand of the same-chart form of the S-side of data `D2`. -/
@[expose] noncomputable def sameInt (x : ExtS RS L base e f) (σ : CLInternalTime RS) : ℂ :=
  spartFrame D1 hG L γ δ F layer1 hLayer1 base S a b p0 x.1 (clLocalClock RS ![t0, t1, t2] σ) *
    (spartExc D2 hG L γ δ F layer2 hLayer2 base S a b p0 x.1 (clLocalClock RS ![t0, t1, t2] σ) *
      Φ (clLocalClock RS ![t0, t1, t2] σ b) (base + latticePoint L (x.1 n0)) (base + latticePoint L (x.1 n1)))

theorem sSum_same (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
      nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (hsel : VineEst.SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 ((clRegionalPairs hG S).erase p0)
      ((S.erase a).erase b)) :
    sSum RS D2 hG L γ δ F layer2 hLayer2 base t0 t1 t2 e f n0 n1 Φ =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          sameInt hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 RS t0 t1 t2 e f n0 n1 Φ x σ := by
  unfold sSum
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  show spart D2 hG L γ δ F layer2 hLayer2 base S a b x.1 (clLocalClock RS ![t0, t1, t2] σ) * _ = _
  rw [spart_eq_frame_mul_exc D2 hG L γ δ F layer2 hLayer2 base S a b p0 hb hp0,
    ← spartFrame_congr hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 hC hT hl hsel]
  unfold sameInt
  ring

theorem sInt_same (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
      nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (hsel : VineEst.SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 ((clRegionalPairs hG S).erase p0)
      ((S.erase a).erase b))
    (x : ExtS RS L base e f) (σ : CLInternalTime RS) :
    sInt RS D2 hG L γ δ F layer2 hLayer2 base t0 t1 t2 e f n0 n1 Φ x σ =
      sameInt hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 RS t0 t1 t2 e f n0 n1 Φ x σ := by
  unfold sInt
  rw [spart_eq_frame_mul_exc D2 hG L γ δ F layer2 hLayer2 base S a b p0 hb hp0,
    ← spartFrame_congr hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 hC hT hl hsel]
  unfold sameInt
  ring

end Sum

end WaveTurbulence.VineEstS5B
