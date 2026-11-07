/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Fac2

/-! # V5 Step 4d-B: the frame of the twisted S-part is the frame of the original

`spartFrame_tw`: at the label-switched decoration `twistNodeLabels G P x` and the transported clocks `u'` (`u' (eB v) = u v`),
the frame (time windows and parent-clock conditions except at `b`, epsilon and phase of `S.erase b`, and all ordinary rows)
of the S-part of the twisted garden is the frame of the S-part of the original garden.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

section Frame
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (x : GNode G.tree → (Fin d → ℤ)) (hpx : PairedAt P x)
  (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v)
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

include h hpx hu hC hT hl hCi hTi hlS in
theorem spartFrame_tw :
    spartFrame D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b)
        (tp P hG (pairOfLeaf G hG P.retained)) (twistNodeLabels G P x) u' =
      spartFrame D hG L γ δ F layer hLayer base S a b (pairOfLeaf G hG P.retained) x u := by
  classical
  have hd := h.domF_iff (fun v => layer (D.coreBranch hG v).toNode)
    (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) hl u' u hu
  have hSb : ∀ v ∈ S.erase b, u' (eB P v) = u v := fun v hv => hu v (Finset.mem_of_mem_erase hv)
  have hq : ∏ p' ∈ (clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P S)).erase
        (tp P hG (pairOfLeaf G hG P.retained)),
      qRow D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (u' (eB P a)) (twistNodeLabels G P x) u' p' =
      ∏ p ∈ (clRegionalPairs hG S).erase (pairOfLeaf G hG P.retained),
        qRow D hG L γ δ F layer hLayer base (u a) x u p := by
    refine (Finset.prod_equiv (tp P hG) (fun p => ?_) (fun p hp => ?_)).symm
    · rw [Finset.mem_erase, Finset.mem_erase, (tp P hG).injective.ne_iff, mem_pairs_tw h hG p]
    · obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
      exact (qRow_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base x u' u hu p hp hp0 (hC p hp hp0) (hCi p hp hp0) hlS).symm
  have ht : ∏ v' ∈ ((twistedAtoms G P S).erase (eB P a)).erase (eB P b),
      tRow D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (u' (eB P a)) (twistNodeLabels G P x) u' v' =
      ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) x u v := by
    refine (Finset.prod_equiv (eB P) (fun v => ?_) (fun v hv => ?_)).symm
    · simp only [Finset.mem_erase, (eB P).injective.ne_iff]
      exact and_congr Iff.rfl (and_congr Iff.rfl (mem_twistedAtoms G P S v).symm)
    · obtain ⟨hvb, hv⟩ := Finset.mem_erase.mp hv
      exact (tRow_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base x u' u hu v hv hvb (hT v hv hvb) (hTi v hv hvb) hlS).symm
  unfold spartFrame
  have hdom : (if DomF (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode)
      (twistedAtoms G P S) (eB P a) (eB P b) u' then (1 : ℂ) else 0) =
      if DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u then 1 else 0 := by
    simp only [hd]
  rw [hdom, h.eps x hpx, h.phase x L γ δ base hpx u' u hSb, hq, ht]

end Frame

end WaveTurbulence.VineEstS5B
