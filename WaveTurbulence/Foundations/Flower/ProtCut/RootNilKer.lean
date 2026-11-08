/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootNil

/-! # D2c PROT-CUT: one-pair chains — (P2) and the root cut without suffix (summand level)

`PairOnly.summand_both` ((P2): root at `σ`, `𝔫_b` at `v`) and `PairOnly.summand_root0` (root at `σ`, `𝔫_b`
integrated), at one decoration `κ ↔ (e, interior, red, green)` (`PairData.decEquiv`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace PairOnly

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

/-- **The multiplier factors at the pair.** -/
def MultFactors {d : ℕ} (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) : Prop :=
  ∀ K : GNode LG.garden.tree → Mom d,
    M K = Mc (fun i => extend K (aAddr .nil i)) (fun i => extend K (bAddr .nil m inner i)) *
      (Mi (K ∘ D.hp.ιi) * (Mr (K ∘ D.hp.ιr) * Mg (K ∘ D.hp.ιg)))

variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

theorem extend0 : extend κ.1 ((0 : Fin 1), []) = 0 := by
  rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root LG.garden.tree 0).1 from rfl, extend_node]
  exact κ.2.2.1 0

theorem κ_slot (j : Fin 3) : κ.1 (D.hp.rootB.child j) =
    pairA m (D.hp.decEquiv d κ).1.1.1 (D.hp.decEquiv d κ).1.1.2.1 (D.hp.decEquiv d κ).1.1.2.2 j := by
  rw [← extend_node κ.1]
  have := D.hp.extend_slot κ.2.1 j
  convert this using 2 <;> first | rfl | simp [PairData.rootB, GBranch.child]

theorem κ_bslot (j : Fin 3) : κ.1 (D.hp.bB.child j) =
    pairB m (D.hp.decEquiv d κ).1.1.2.1 (D.hp.decEquiv d κ).1.1.2.2 j := by
  rw [← extend_node κ.1]
  exact D.hp.extend_bslot κ.2.1 (D.extend0 κ) j

theorem κ_bB : κ.1 D.hp.bB.toNode = (D.hp.decEquiv d κ).1.1.1 := by
  rw [← extend_node κ.1]
  exact D.hp.extend_bPath κ.2.1

variable (L : ℝ) (k : Mom d)

theorem starA_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (aAddr .nil i)) =
    starA m L k (D.hp.decEquiv d κ).1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show aAddr .nil 0 = D.hp.rootB.toNode.1 by simp [aAddr, PairData.rootB, GBranch.toNode, RegChain.lonePath],
      extend_node]
    show k + latticePoint L (κ.1 D.hp.rootB.toNode) = k
    rw [show κ.1 D.hp.rootB.toNode = 0 from κ.2.2.1 0, latticePoint_zero, add_zero]
  · rw [show aAddr .nil j.succ = (D.hp.rootB.child j).1 by
      simp [aAddr, PairData.rootB, GBranch.child, RegChain.lonePath], extend_node]
    show k + latticePoint L (κ.1 (D.hp.rootB.child j)) = _
    rw [D.κ_slot κ j]
    rfl

theorem starB_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (bAddr .nil m inner i)) =
    starB m L k (D.hp.decEquiv d κ).1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show bAddr .nil m inner 0 = D.hp.bB.toNode.1 by
      simp [bAddr, PairData.bB, GBranch.toNode, RegChain.lonePath], extend_node]
    show k + latticePoint L (κ.1 D.hp.bB.toNode) = _
    rw [D.κ_bB κ]
    rfl
  · rw [show bAddr .nil m inner j.succ = (D.hp.bB.child j).1 by
      simp [bAddr, PairData.bB, GBranch.child, RegChain.lonePath], extend_node]
    show k + latticePoint L (κ.1 (D.hp.bB.child j)) = _
    rw [D.κ_bslot κ j]
    rfl

theorem coset_I : cosetDecoration LG.garden L k κ.1 ∘ D.hp.ιi =
    cosetDecoration LGi.garden L (k + latticePoint L (D.hp.decEquiv d κ).1.1.1) ((D.hp.decEquiv d κ).2.1).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (D.hp.ιi z)) = k + latticePoint L ((κ.1 (D.hp.ιi z) -
    extend κ.1 ((0 : Fin 1), [m.c])) + extend κ.1 ((0 : Fin 1), [m.c]))
  rw [sub_add_cancel]

theorem coset_R : cosetDecoration LG.garden L k κ.1 ∘ D.hp.ιr =
    cosetDecoration LGr.garden L (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.1) ((D.hp.decEquiv d κ).2.2.1).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (D.hp.ιr z)) = k + latticePoint L ((κ.1 (D.hp.ιr z) -
    extend κ.1 ((0 : Fin 1), rBase m inner (LG.garden.sig 0) 0)) + extend κ.1 ((0 : Fin 1), rBase m inner (LG.garden.sig 0) 0))
  rw [sub_add_cancel]

theorem coset_G : cosetDecoration LG.garden L k κ.1 ∘ D.hp.ιg =
    cosetDecoration LGg.garden L (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.2) ((D.hp.decEquiv d κ).2.2.2).1 := by
  rw [← cosetDecoration_add_const]
  funext z
  show k + latticePoint L (κ.1 (D.hp.ιg z)) = k + latticePoint L ((κ.1 (D.hp.ιg z) -
    extend κ.1 ((0 : Fin 1), gBase m inner (LG.garden.sig 0) 0)) + extend κ.1 ((0 : Fin 1), gBase m inner (LG.garden.sig 0) 0))
  rw [sub_add_cancel]

omit L k in
theorem epsDec_pair' : epsDec LG.garden κ.1 = cutEps m (D.hp.decEquiv d κ).1 *
    (epsDec LGi.garden ((D.hp.decEquiv d κ).2.1).1 *
      (epsDec LGr.garden ((D.hp.decEquiv d κ).2.2.1).1 * epsDec LGg.garden ((D.hp.decEquiv d κ).2.2.2).1)) := by
  rw [D.hp.epsDec_pair]
  have hi : epsDec LGi.garden (κ.1 ∘ D.hp.ιi) = epsDec LGi.garden ((D.hp.decEquiv d κ).2.1).1 := by
    symm
    rw [← epsDec_add_const LGi.garden _ (extend κ.1 ((0 : Fin 1), [m.c]))]
    congr 1
    funext z
    show κ.1 (D.hp.ιi z) - extend κ.1 ((0 : Fin 1), [m.c]) + extend κ.1 ((0 : Fin 1), [m.c]) = _
    rw [sub_add_cancel]; rfl
  have hr : epsDec LGr.garden (κ.1 ∘ D.hp.ιr) = epsDec LGr.garden ((D.hp.decEquiv d κ).2.2.1).1 := by
    symm
    rw [← epsDec_add_const LGr.garden _ (extend κ.1 ((0 : Fin 1), rBase m inner (LG.garden.sig 0) 0))]
    congr 1
    funext z
    show κ.1 (D.hp.ιr z) - extend κ.1 ((0 : Fin 1), rBase m inner (LG.garden.sig 0) 0) +
      extend κ.1 ((0 : Fin 1), rBase m inner (LG.garden.sig 0) 0) = _
    rw [sub_add_cancel]; rfl
  have hg : epsDec LGg.garden (κ.1 ∘ D.hp.ιg) = epsDec LGg.garden ((D.hp.decEquiv d κ).2.2.2).1 := by
    symm
    rw [← epsDec_add_const LGg.garden _ (extend κ.1 ((0 : Fin 1), gBase m inner (LG.garden.sig 0) 0))]
    congr 1
    funext z
    show κ.1 (D.hp.ιg z) - extend κ.1 ((0 : Fin 1), gBase m inner (LG.garden.sig 0) 0) +
      extend κ.1 ((0 : Fin 1), gBase m inner (LG.garden.sig 0) 0) = _
    rw [sub_add_cancel]; rfl
  rw [hi, hr, hg, D.κ_slot κ 0, D.κ_slot κ 1, D.κ_slot κ 2, D.κ_bslot κ 0, D.κ_bslot κ 1, D.κ_bslot κ 2]
  unfold cutEps
  ring

theorem prodH_pair (H : LeafProfiles 1 d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LGi.garden, (cutHi .nil m H ℓ.1 (cosetDecoration LGi.garden L
          (k + latticePoint L (D.hp.decEquiv d κ).1.1.1) ((D.hp.decEquiv d κ).2.1).1 ℓ.toNode) : ℂ)) *
        ((∏ ℓ ∈ inputLeaves LGr.garden, (cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGr.garden L
            (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.1) ((D.hp.decEquiv d κ).2.2.1).1 ℓ.toNode) : ℂ)) *
          ∏ ℓ ∈ inputLeaves LGg.garden, (cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGg.garden L
            (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.2) ((D.hp.decEquiv d κ).2.2.2).1 ℓ.toNode) : ℂ)) := by
  set f : Fin 1 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, D.hp.prod_inputLeaves_pair f]
  have hc := D.coset_I κ L k
  have hcr := D.coset_R κ L k
  have hcg := D.coset_G κ L k
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : pφi m ℓ.1 = (D.hp.ιi ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hc ℓ.toNode]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : pφr m inner (LG.garden.sig 0) ℓ.1 = (D.hp.ιr ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcr ℓ.toNode]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : pφg m inner (LG.garden.sig 0) ℓ.1 = (D.hp.ιg ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcg ℓ.toNode]
    rfl

theorem phase_pair (γ δ : ℝ) (x y : ℝ) :
    Complex.exp ((Real.pi * ((LG.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) D.hp.rootB * x : ℝ) * Complex.I) *
      Complex.exp ((Real.pi * ((LG.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) D.hp.bB * y : ℝ) * Complex.I) =
      cutPh m (LG.garden.sig 0) L γ δ k y (D.hp.decEquiv d κ).1 x := by
  set e := (D.hp.decEquiv d κ).1
  set P0 := k
  set Px := k + latticePoint L e.1.1
  set Pr := k + latticePoint L e.1.2.1
  set Pg := k + latticePoint L e.1.2.2
  have sa : LG.garden.sign D.hp.rootB.toNode = LG.garden.sig 0 := by
    show pathSign (LG.garden.sig 0) [] = _
    simp [pathSign]
  have sb : LG.garden.sign D.hp.bB.toNode = slotSign (LG.garden.sig 0) m.c := by
    show pathSign (LG.garden.sig 0) (bPath m inner) = _
    rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign]
  have oa : omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) D.hp.rootB =
      resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 (D.hp.rootB.child j) = cA m Px Pr Pg j := fun j => by
      show k + latticePoint L (κ.1 (D.hp.rootB.child j)) = _
      rw [D.κ_slot κ j, CutTermData.coset_cA]
    have h0 : cosetDecoration LG.garden L k κ.1 D.hp.rootB.toNode = P0 := by
      show k + latticePoint L (κ.1 D.hp.rootB.toNode) = _
      rw [show κ.1 D.hp.rootB.toNode = 0 from κ.2.2.1 0, latticePoint_zero, add_zero]
    unfold omegaNode
    rw [hc 0, hc 1, hc 2, h0]
  have ob : omegaNode LG.garden (cosetDecoration LG.garden L k κ.1) D.hp.bB =
      resFactor (cB m P0 Pr Pg 0) (cB m P0 Pr Pg 1) (cB m P0 Pr Pg 2) Px := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 (D.hp.bB.child j) = cB m P0 Pr Pg j := fun j => by
      show k + latticePoint L (κ.1 (D.hp.bB.child j)) = _
      rw [D.κ_bslot κ j, CutTermData.coset_cB]
    have h0 : cosetDecoration LG.garden L k κ.1 D.hp.bB.toNode = Px := by
      show k + latticePoint L (κ.1 D.hp.bB.toNode) = _
      rw [D.κ_bB κ]
    unfold omegaNode
    rw [hc 0, hc 1, hc 2, h0]
  have hfreq : cutFreq m (LG.garden.sig 0) L γ δ k e =
      (((LG.garden.sig 0 : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 := by
    unfold cutFreq
    rw [show starA m L k e 1 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 0) from rfl,
      show starA m L k e 2 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 1) from rfl,
      show starA m L k e 3 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 2) from rfl,
      show starA m L k e 0 = k from rfl, CutTermData.coset_cA, CutTermData.coset_cA, CutTermData.coset_cA]
  have key := link_cancel m (LG.garden.sig 0) P0 Px Pr Pg
  unfold cutPh
  rw [sa, sb, oa, ob, hfreq, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
  congr 3
  linear_combination (Real.pi * δ * L ^ (2 * γ) * y) * key

/-! ### The summands -/

/-- **(P2) at one decoration.** -/
theorem summand_both (L γ δ : ℝ) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg) (T s σ v : ℝ) (hσT : σ ≤ T) (hvT : v ≤ T) (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s (pairFix m inner σ v) k κ =
      (Mc (starA m L k (D.hp.decEquiv d κ).1) (starB m L k (D.hp.decEquiv d κ).1) *
          (cutEps m (D.hp.decEquiv d κ).1 : ℂ)) *
        (cutPh m (LG.garden.sig 0) L γ δ k v (D.hp.decEquiv d κ).1 σ *
          (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none)
              (k + latticePoint L (D.hp.decEquiv d κ).1.1.1) (D.hp.decEquiv d κ).2.1 *
            (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.1) (D.hp.decEquiv d κ).2.2.1 *
              protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.2) (D.hp.decEquiv d κ).2.2.2))) := by
  unfold protSummand
  rw [hM, D.starA_eq κ L k, D.starB_eq κ L k, D.coset_I κ L k, D.coset_R κ L k, D.coset_G κ L k, D.epsDec_pair' κ,
    D.protTime_both L γ δ T s σ v hσT hvT, D.prodH_pair κ L k H, D.coset_I κ L k, D.coset_R κ L k,
    D.coset_G κ L k, D.phase_pair κ L k γ δ σ v]
  push_cast
  ring

/-- **The root pin of a one-pair tree at one decoration.** -/
theorem summand_root0 (L γ δ : ℝ) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg) (T s σ : ℝ) (hσT : σ ≤ T) (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k κ =
      (Mc (starA m L k (D.hp.decEquiv d κ).1) (starB m L k (D.hp.decEquiv d κ).1) *
          (cutEps m (D.hp.decEquiv d κ).1 : ℂ)) *
        ∫ u in rootU0 LG m inner T σ s, cutPh m (LG.garden.sig 0) L γ δ k u (D.hp.decEquiv d κ).1 σ *
          ((1 : ℂ) * (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
              (k + latticePoint L (D.hp.decEquiv d κ).1.1.1) (D.hp.decEquiv d κ).2.1 *
            (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.1) (D.hp.decEquiv d κ).2.2.1 *
              protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.hp.decEquiv d κ).1.1.2.2) (D.hp.decEquiv d κ).2.2.2))) := by
  unfold protSummand
  rw [hM, D.starA_eq κ L k, D.starB_eq κ L k, D.coset_I κ L k, D.coset_R κ L k, D.coset_G κ L k, D.epsDec_pair' κ,
    D.protTime_root0 L γ δ T s σ hσT, D.prodH_pair κ L k H]
  simp only [D.coset_I κ L k, D.coset_R κ L k, D.coset_G κ L k, D.phase_pair κ L k γ δ σ]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

end PairOnly

end WaveTurbulence.Flower.ProtCut
