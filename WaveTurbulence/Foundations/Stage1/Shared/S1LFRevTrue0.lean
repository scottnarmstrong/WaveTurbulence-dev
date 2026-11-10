/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFCompose
import Mathlib.Tactic

/-!
# Cast toolbox for reconstruction data over propositionally equal skeletons

Used by the reversal and composition of a true-choice LF operation: twice transporting the
reconstruction data along the (value-preserving) twist equivalences is the identity up to the cast
`unitTwistGarden_involutive`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem sourcePairEquiv_twice {G H K : Garden w} (hG : G.IsPlain) (hH : H.IsPlain) (hK : K.IsPlain)
    (EL1 : GLeaf G.tree ≃ GLeaf H.tree) (hE1 : ∀ l, EL1 (G.pair l) = H.pair (EL1 l))
    (EL2 : GLeaf H.tree ≃ GLeaf K.tree) (hE2 : ∀ l, EL2 (H.pair l) = K.pair (EL2 l))
    (hKG : K = G) (hl : ∀ l : GLeaf G.tree, (EL2 (EL1 l)).1 = l.1) (q : SourcePair G) :
    sourcePairEquiv hH hK EL2 hE2 (sourcePairEquiv hG hH EL1 hE1 q) = (hKG ▸ q : SourcePair K) := by
  subst hKG
  change sourcePairEquiv hH hK EL2 hE2 (pairOfLeaf H hH (EL1 (q.firstLeaf hG))) = q
  rw [sourcePairEquiv_pairOfLeaf]
  have : EL2 (EL1 (q.firstLeaf hG)) = q.firstLeaf hG := Subtype.ext (hl _)
  rw [this]
  exact pairOfLeaf_firstLeaf K hK q

/-- Transporting reconstruction data twice along value-preserving equivalences with a cast of the
target garden is the identity up to `HEq`. -/
theorem transport_twice_heq {G H K : Garden w} (hG : G.IsPlain) (hH : H.IsPlain) (hK : K.IsPlain)
    (EB1 : GBranch G.tree ≃ GBranch H.tree) (EL1 : GLeaf G.tree ≃ GLeaf H.tree)
    (hE1 : ∀ l, EL1 (G.pair l) = H.pair (EL1 l))
    (EB2 : GBranch H.tree ≃ GBranch K.tree) (EL2 : GLeaf H.tree ≃ GLeaf K.tree)
    (hE2 : ∀ l, EL2 (H.pair l) = K.pair (EL2 l))
    (hKG : K = G) (hb : ∀ b : GBranch G.tree, (EB2 (EB1 b)).1 = b.1)
    (hl : ∀ l : GLeaf G.tree, (EL2 (EL1 l)).1 = l.1) (D : ReconstructionData G) :
    HEq (transportReconstruction hH hK EB2 EL2 hE2 (transportReconstruction hG hH EB1 EL1 hE1 D)) D := by
  have hq := sourcePairEquiv_twice hG hH hK EL1 hE1 EL2 hE2 hKG hl
  subst hKG
  apply heq_of_eq
  apply ReconstructionData.ext_tree_couple
  · funext b
    change D.tree (EB1.symm (EB2.symm b)) = D.tree b
    congr 1
    apply Subtype.ext
    have := hb (EB1.symm (EB2.symm b))
    exact (by simpa only [Equiv.apply_symm_apply] using this : b.1 = _).symm
  · funext p
    change D.couple ((sourcePairEquiv hG hH EL1 hE1).symm ((sourcePairEquiv hH hK EL2 hE2).symm p)) = D.couple p
    congr 1
    have h2 : ∀ q, sourcePairEquiv hH hK EL2 hE2 (sourcePairEquiv hG hH EL1 hE1 q) = q := fun q => hq q
    have := h2 ((sourcePairEquiv hG hH EL1 hE1).symm ((sourcePairEquiv hH hK EL2 hE2).symm p))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm


/-! ### Congruence of reconstruction functions under `HEq` of the data -/

section HEqCongr
variable {T S : Garden w}

theorem inflatedPosition_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) {n1 : GNode T.tree} {n2 : GNode S.tree} (hn : n1.1 = n2.1) :
    inflatedPosition T D1.tree n1 = inflatedPosition S D2.tree n2 := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hn]

theorem corePosition_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) {b1 : GBranch T.tree} {b2 : GBranch S.tree} (hb : b1.1 = b2.1) :
    D1.corePosition b1 = D2.corePosition b2 := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hb]

theorem decodes_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) (h1 : T.IsPlain) (h2 : S.IsPlain) (G : Garden w) :
    D1.Decodes h1 G ↔ D2.Decodes h2 G := by
  subst h
  have := eq_of_heq hD
  subst this
  rfl

theorem coupleRoot_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) (h1 : T.IsPlain) (h2 : S.IsPlain) {q1 : SourcePair T} {q2 : SourcePair S}
    (hq : q1.1 = q2.1) (i : Fin 2) : coupleRoot D1 h1 q1 i = coupleRoot D2 h2 q2 i := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hq]

theorem rawTreeLayerCount_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) (h1 : T.IsPlain) (h2 : S.IsPlain) (LG : LayeredGarden w) (p : ℕ)
    {b1 : GBranch T.tree} {b2 : GBranch S.tree} (hb : b1.1 = b2.1) :
    rawTreeLayerCount LG D1 h1 p b1 = rawTreeLayerCount LG D2 h2 p b2 := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hb]

theorem rawCoupleLayerCount_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) (h1 : T.IsPlain) (h2 : S.IsPlain) (LG : LayeredGarden w) (p : ℕ)
    {q1 : SourcePair T} {q2 : SourcePair S} (hq : q1.1 = q2.1) :
    rawCoupleLayerCount LG D1 h1 p q1 = rawCoupleLayerCount LG D2 h2 p q2 := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hq]

theorem withTree_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) {b1 : GBranch T.tree} {b2 : GBranch S.tree} (hb : b1.1 = b2.1)
    (X : RegChain) (hX : X.wf = true) : HEq (D1.withTree b1 X hX) (D2.withTree b2 X hX) := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hb]

theorem withCouple_heq (h : T = S) {D1 : ReconstructionData T} {D2 : ReconstructionData S}
    (hD : HEq D1 D2) {q1 : SourcePair T} {q2 : SourcePair S} (hq : q1.1 = q2.1)
    (Q : RegCpl) (hQ : Q.wf = true) : HEq (D1.withCouple q1 Q hQ) (D2.withCouple q2 Q hQ) := by
  subst h
  have := eq_of_heq hD
  subst this
  rw [Subtype.ext hq]

end HEqCongr

end WaveTurbulence.Stage1
