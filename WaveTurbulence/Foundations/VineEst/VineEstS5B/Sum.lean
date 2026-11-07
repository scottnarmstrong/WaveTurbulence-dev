/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Fac3
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp11Lin

/-! # V5 Step 4d-B: the S-side of a twist at the lower joint (TARGET `(tildeJ2)`, L1877-L1925)

`sSum_tw`: the S-side `sSum` of the twisted garden (lower factor `Φ'` read at the two boundary nodes `b'`, `b'.child kept`)
equals `-` the original S-side integrand with the frame of the ORIGINAL data, the exceptional factor of the twisted data
(evaluated at the label-switched decoration and the transported clocks), and the lower factor read at the exchanged
boundary labels `(x r, x lower)`.  The sign is `ζ_S' = -ζ_S`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

namespace STw
include h

theorem label_b {d : ℕ} (y : GNode G.tree → (Fin d → ℤ)) :
    twistNodeLabels G P y (eB P b).toNode = y P.retained.toNode := by
  rw [h.lower]; exact twistNodeLabels_lower G P y

theorem label_b_kept {d : ℕ} (y : GNode G.tree → (Fin d → ℤ)) :
    twistNodeLabels G P y ((eB P b).child RS'.kept) = y P.lower.toNode := by
  rw [h.keep', h.lower]
  have := twistNodeLabels_lower_child G P y P.keep
  rw [if_pos rfl] at this
  exact this

end STw

section SumTw
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (t0 t1 t2 : ℝ) (e f : Mom d) (Φ' : ℝ → Mom d → Mom d → ℂ)
  (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
    nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ S.erase a, v ≠ b →
    nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
    layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
    Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ S.erase a, v ≠ b →
    Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
  (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
    layer (D.coreBranch hG v).toNode)

/-- The integrand of the original-chart form of the twisted S-side. -/
@[expose] noncomputable def twInt (x : ExtS RS L base e f) (σ : CLInternalTime RS) : ℂ :=
  spartFrame D hG L γ δ F layer hLayer base S a b (pairOfLeaf G hG P.retained) x.1
      (clLocalClock RS ![t0, t1, t2] σ) *
    (spartExc D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b)
        (tp P hG (pairOfLeaf G hG P.retained)) (twistNodeLabels G P x.1)
        (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' σ)) *
      Φ' (clLocalClock RS ![t0, t1, t2] σ b) (base + latticePoint L (x.1 P.retained.toNode))
        (base + latticePoint L (x.1 P.lower.toNode)))

include h hC hT hl hCi hTi hlS in
/-- The pointwise form: the S-side integrand of the twisted garden at `(extEquiv x, tEquivS σ)` is `twInt x σ`. -/
theorem sInt_tw (x : ExtS RS L base e f) (σ : CLInternalTime RS) :
    sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f (eB P b).toNode
        ((eB P b).child RS'.kept) Φ' (h.extEquiv L base e f x) (tEquivS P RS RS' σ) =
      twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ := by
  have hb' : eB P b ∈ (twistedAtoms G P S).erase (eB P a) :=
    (mem_erase_twisted P (b := a) b).mpr (Finset.mem_erase.mpr ⟨h.block.2.2.2.1.symm, h.block.2.2.1⟩)
  have hp0 : pairOfLeaf G hG P.retained ∈ clRegionalPairs hG S := by
    rw [mem_clRegionalPairs]
    rcases LFTwist.pairOfLeaf_first_or_partner G hG P.retained with e | e
    · rw [e]; exact h.retained_internal
    · rw [e]; exact h.partner_internal
  have hp0' : tp P hG (pairOfLeaf G hG P.retained) ∈
      clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P S) := (mem_pairs_tw h hG _).mpr hp0
  have hu : ∀ v ∈ S, clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' σ) (eB P v) = clLocalClock RS ![t0, t1, t2] σ v :=
    fun v hv => clockS_corr P RS RS' _ σ hv
  have hx := h.extEquiv_val L base e f x
  have hpx := h.pairedAt_ext x
  show spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b)
        (h.extEquiv L base e f x).1 (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' σ)) *
      Φ' (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' σ) (eB P b))
        (base + latticePoint L ((h.extEquiv L base e f x).1 (eB P b).toNode))
        (base + latticePoint L ((h.extEquiv L base e f x).1 ((eB P b).child RS'.kept))) =
    twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ
  rw [hx, h.label_b x.1, h.label_b_kept x.1, hu b h.block.2.2.1,
    spart_eq_frame_mul_exc _ _ L γ δ F layer' hLayer' base _ _ _ _ hb' hp0',
    spartFrame_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base x.1 hpx _ _ hu hC hT hl hCi hTi hlS]
  unfold twInt
  ring

include h hC hT hl hCi hTi hlS in
theorem sSum_tw :
    sSum RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f (eB P b).toNode
        ((eB P b).child RS'.kept) Φ' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ) := by
  unfold sSum
  rw [order1_rigid P RS RS', h.zeta]
  suffices key : (∑' xS : ExtS RS' L base e f, ∫ σ : CLInternalTime RS',
      spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b) xS.1
        (clLocalClock RS' ![t0, t1, t2] σ) *
      Φ' (clLocalClock RS' ![t0, t1, t2] σ (eB P b)) (base + latticePoint L (xS.1 (eB P b).toNode))
        (base + latticePoint L (xS.1 ((eB P b).child RS'.kept)))) =
      ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
        twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ by
    rw [key]; ring
  rw [← (h.extEquiv L base e f).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun σ' => spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a)
      (eB P b) (h.extEquiv L base e f x).1 (clLocalClock RS' ![t0, t1, t2] σ') *
      Φ' (clLocalClock RS' ![t0, t1, t2] σ' (eB P b)) (base + latticePoint L ((h.extEquiv L base e f x).1 (eB P b).toNode))
        (base + latticePoint L ((h.extEquiv L base e f x).1 ((eB P b).child RS'.kept))))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun σ => sInt_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' hC hT hl hCi hTi hlS x σ)

end SumTw

end WaveTurbulence.VineEstS5B
