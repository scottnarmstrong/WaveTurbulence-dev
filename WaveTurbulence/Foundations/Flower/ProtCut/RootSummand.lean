/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootCutTime

/-! # D2c PROT-CUT: the root pin at one decoration (summand level)

`RootData.summand_root`: the summand of `kernelProt (root at σ)` at one decoration `κ ↔ (suffix, e, interior, red,
green)` (`RootData.Φr`) is `M_cut(star_a, star_b) ε_a ε_b ∫_{rootU} e^{πiA_e(σ−u)} S_suf(u) S_in(σ, u) S_r S_g du`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The suffix profiles. -/
def rootHs (m : MiniTreeCode) (inner : RegChain) {d : ℕ} (H : LeafProfiles 1 d) : LeafProfiles 1 d :=
  fun a => H ((0 : Fin 1), lonePos m inner ++ a.2)

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

/-- The pieces placed in the protected tree. -/
def ιI (z : GNode LGi.garden.tree) : GNode LG.garden.tree := D.gd.ι₁ (D.hp.ιi z)
def ιR (z : GNode LGr.garden.tree) : GNode LG.garden.tree := D.gd.ι₁ (D.hp.ιr z)
def ιG (z : GNode LGg.garden.tree) : GNode LG.garden.tree := D.gd.ι₁ (D.hp.ιg z)
def ιS (z : GNode LGs.garden.tree) : GNode LG.garden.tree := D.gd.ι₂ z

/-- **The multiplier factors at the root cut.** -/
def MultFactors {d : ℕ} (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ) : Prop :=
  ∀ K : GNode LG.garden.tree → Mom d,
    M K = Mc (fun i => extend K (aAddr .nil i)) (fun i => extend K (bAddr .nil m inner i)) *
      (Ms (K ∘ D.ιS) * (Mi (K ∘ D.ιI) * (Mr (K ∘ D.ιR) * Mg (K ∘ D.ιG))))

/-- **Decorations of the protected tree**: suffix × (exceptional data × interior × red × green). -/
def Φr (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGs.garden d (fun _ => 0) 0 × (PairE m d × (GenDecoration LGi.garden d (fun _ => 0) 0 ×
      (GenDecoration LGr.garden d (fun _ => 0) 0 × GenDecoration LGg.garden d (fun _ => 0) 0))) :=
  ((D.gd.decEquiv (decSplit_tree D.dec' D.decZ D.sigZ D.decS D.sigS)
      (decGlue_tree D.dec' D.decZ D.sigZ D.decS D.sigS) (not_flower_of_decodesTree D.dec')
      (not_flower_of_decodesTree D.decZ) (not_flower_of_decodesTree D.decS)).trans
    ((D.hp.decEquiv d).prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)

variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

theorem Φr_s : ((D.Φr d κ).1).1 = κ.1 ∘ D.gd.ι₂ := rfl

theorem Φr_e : (D.Φr d κ).2.1.1 = (extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), [m.c]),
    extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), rBase m inner (LGZ.garden.sig 0) 0),
    extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), gBase m inner (LGZ.garden.sig 0) 0)) := rfl

theorem Φr_i : ((D.Φr d κ).2.2.1).1 = fun z =>
    κ.1 (D.gd.ι₁ (D.hp.ιi z)) - extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), [m.c]) := rfl

theorem Φr_r : ((D.Φr d κ).2.2.2.1).1 = fun z =>
    κ.1 (D.gd.ι₁ (D.hp.ιr z)) - extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), rBase m inner (LGZ.garden.sig 0) 0) := rfl

theorem Φr_g : ((D.Φr d κ).2.2.2.2).1 = fun z =>
    κ.1 (D.gd.ι₁ (D.hp.ιg z)) - extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), gBase m inner (LGZ.garden.sig 0) 0) := rfl

theorem isDec_Z : IsDecoration LGZ.garden (κ.1 ∘ D.gd.ι₁) :=
  ((decSplit_tree D.dec' D.decZ D.sigZ D.decS D.sigS (V := Fin d → ℤ)) κ.1 κ.2.1).1

theorem Z_extend0 : extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), []) = 0 := by
  rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root LGZ.garden.tree 0).1 from rfl, extend_node]
  exact κ.2.2.1 0

theorem κZ_slot (j : Fin 3) : (κ.1 ∘ D.gd.ι₁) (D.hp.rootB.child j) =
    pairA m (D.Φr d κ).2.1.1.1 (D.Φr d κ).2.1.1.2.1 (D.Φr d κ).2.1.1.2.2 j := by
  rw [D.Φr_e κ, ← extend_node (κ.1 ∘ D.gd.ι₁)]
  have := D.hp.extend_slot (D.isDec_Z κ) j
  convert this using 2
  simp [PairData.rootB, GBranch.child]

theorem κZ_bslot (j : Fin 3) : (κ.1 ∘ D.gd.ι₁) (D.hp.bB.child j) =
    pairB m (D.Φr d κ).2.1.1.2.1 (D.Φr d κ).2.1.1.2.2 j := by
  rw [D.Φr_e κ, ← extend_node (κ.1 ∘ D.gd.ι₁)]
  exact D.hp.extend_bslot (D.isDec_Z κ) (D.Z_extend0 κ) j

theorem κZ_bB : (κ.1 ∘ D.gd.ι₁) D.hp.bB.toNode = (D.Φr d κ).2.1.1.1 := by
  rw [D.Φr_e κ, ← extend_node (κ.1 ∘ D.gd.ι₁)]
  exact D.hp.extend_bPath (D.isDec_Z κ)

theorem κZ_rootB : (κ.1 ∘ D.gd.ι₁) D.hp.rootB.toNode = 0 := κ.2.2.1 0

/-! ### Momenta -/

variable (L : ℝ) (k : Mom d)

theorem extend_coset (w : GNode LGZ.garden.tree) (a : Fin 1 × Path) (ha : a = ((0 : Fin 1), w.1.2)) :
    extend (cosetDecoration LG.garden L k κ.1) a = k + latticePoint L ((κ.1 ∘ D.gd.ι₁) w) := by
  rw [ha, show ((0 : Fin 1), w.1.2) = (D.gd.ι₁ w).1 from rfl, extend_node]
  rfl

theorem starA_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (aAddr .nil i)) =
    starA m L k (D.Φr d κ).2.1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show aAddr .nil 0 = ((0 : Fin 1), D.hp.rootB.toNode.1.2) by
      simp [aAddr, PairData.rootB, GBranch.toNode, RegChain.lonePath]]
    rw [D.extend_coset κ L k _ _ rfl, D.κZ_rootB κ, latticePoint_zero, add_zero]
    rfl
  · rw [show aAddr .nil j.succ = ((0 : Fin 1), (D.hp.rootB.child j).1.2) by
      simp [aAddr, PairData.rootB, GBranch.child, RegChain.lonePath]]
    rw [D.extend_coset κ L k _ _ rfl, D.κZ_slot κ]
    rfl

theorem starB_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (bAddr .nil m inner i)) =
    starB m L k (D.Φr d κ).2.1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show bAddr .nil m inner 0 = ((0 : Fin 1), D.hp.bB.toNode.1.2) by
      simp [bAddr, PairData.bB, GBranch.toNode, RegChain.lonePath]]
    rw [D.extend_coset κ L k _ _ rfl, D.κZ_bB κ]
    rfl
  · rw [show bAddr .nil m inner j.succ = ((0 : Fin 1), (D.hp.bB.child j).1.2) by
      simp [bAddr, PairData.bB, GBranch.child, RegChain.lonePath]]
    rw [D.extend_coset κ L k _ _ rfl, D.κZ_bslot κ]
    rfl

theorem coset_S : cosetDecoration LG.garden L k κ.1 ∘ D.ιS = cosetDecoration LGs.garden L k ((D.Φr d κ).1).1 := rfl

theorem coset_I : cosetDecoration LG.garden L k κ.1 ∘ D.ιI =
    cosetDecoration LGi.garden L (k + latticePoint L (D.Φr d κ).2.1.1.1) ((D.Φr d κ).2.2.1).1 := by
  rw [← cosetDecoration_add_const, D.Φr_i κ, D.Φr_e κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rfl

theorem coset_R : cosetDecoration LG.garden L k κ.1 ∘ D.ιR =
    cosetDecoration LGr.garden L (k + latticePoint L (D.Φr d κ).2.1.1.2.1) ((D.Φr d κ).2.2.2.1).1 := by
  rw [← cosetDecoration_add_const, D.Φr_r κ, D.Φr_e κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rfl

theorem coset_G : cosetDecoration LG.garden L k κ.1 ∘ D.ιG =
    cosetDecoration LGg.garden L (k + latticePoint L (D.Φr d κ).2.1.1.2.2) ((D.Φr d κ).2.2.2.2).1 := by
  rw [← cosetDecoration_add_const, D.Φr_g κ, D.Φr_e κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rfl

/-! ### `ε`, input leaves, phases -/

omit L k in
theorem epsDec_root : epsDec LG.garden κ.1 = epsDec LGs.garden ((D.Φr d κ).1).1 *
    (cutEps m (D.Φr d κ).2.1 * (epsDec LGi.garden ((D.Φr d κ).2.2.1).1 *
      (epsDec LGr.garden ((D.Φr d κ).2.2.2.1).1 * epsDec LGg.garden ((D.Φr d κ).2.2.2.2).1))) := by
  rw [D.gd.epsDec_glue κ.1, D.hp.epsDec_pair]
  have hi : epsDec LGi.garden ((κ.1 ∘ D.gd.ι₁) ∘ D.hp.ιi) = epsDec LGi.garden ((D.Φr d κ).2.2.1).1 := by
    rw [D.Φr_i κ]
    symm
    rw [← epsDec_add_const LGi.garden _ (extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), [m.c]))]
    congr 1
    funext z
    simp
  have hr : epsDec LGr.garden ((κ.1 ∘ D.gd.ι₁) ∘ D.hp.ιr) = epsDec LGr.garden ((D.Φr d κ).2.2.2.1).1 := by
    rw [D.Φr_r κ]
    symm
    rw [← epsDec_add_const LGr.garden _ (extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), rBase m inner (LGZ.garden.sig 0) 0))]
    congr 1
    funext z
    simp
  have hg : epsDec LGg.garden ((κ.1 ∘ D.gd.ι₁) ∘ D.hp.ιg) = epsDec LGg.garden ((D.Φr d κ).2.2.2.2).1 := by
    rw [D.Φr_g κ]
    symm
    rw [← epsDec_add_const LGg.garden _ (extend (κ.1 ∘ D.gd.ι₁) ((0 : Fin 1), gBase m inner (LGZ.garden.sig 0) 0))]
    congr 1
    funext z
    simp
  rw [hi, hr, hg, D.κZ_slot κ 0, D.κZ_slot κ 1, D.κZ_slot κ 2, D.κZ_bslot κ 0, D.κZ_bslot κ 1, D.κZ_bslot κ 2]
  unfold cutEps
  rw [D.Φr_s κ]
  ring

theorem hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ (cpair m Qr Qg inner).lonePath <+: ℓ.1.2) →
    LG.garden.mark ℓ = none := by
  intro ℓ hℓ
  rw [D.dec.2.1 ℓ, lonePath_eq, ← cpair_lonePath]
  refine ite_eq_right fun he => hℓ.2 ?_
  rw [he]
  exact List.prefix_append _ _

theorem hmbot : ∀ (ℓ₂ : GLeaf LGs.garden.tree) (ℓ : GLeaf LG.garden.tree),
    ℓ.1 = botAddr (cpair m Qr Qg inner).lonePath ℓ₂.1 → LG.garden.mark ℓ = LGs.garden.mark ℓ₂ := by
  intro ℓ₂ ℓ he
  rw [D.dec.2.1 ℓ, D.decS.2.1 ℓ₂, lonePath_eq, ← cpair_lonePath]
  have hp : ℓ.1.2 = (cpair m Qr Qg inner).lonePath ++ ℓ₂.1.2 := by
    rw [he]
    have hj : ℓ₂.1.1 = 0 := Subsingleton.elim _ _
    simp [botAddr, hj]
  rw [hp]
  by_cases hc : ℓ₂.1.2 = rest.lonePath
  · rw [if_pos (by rw [hc]), if_pos hc]
  · rw [if_neg (fun h => hc (List.append_cancel_left h)), if_neg hc]

theorem prodH_root (H : LeafProfiles 1 d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LGs.garden, (rootHs m inner H ℓ.1
          (cosetDecoration LGs.garden L k ((D.Φr d κ).1).1 ℓ.toNode) : ℂ)) *
      ((∏ ℓ ∈ inputLeaves LGi.garden, (cutHi .nil m H ℓ.1 (cosetDecoration LGi.garden L
          (k + latticePoint L (D.Φr d κ).2.1.1.1) ((D.Φr d κ).2.2.1).1 ℓ.toNode) : ℂ)) *
        ((∏ ℓ ∈ inputLeaves LGr.garden, (cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGr.garden L
            (k + latticePoint L (D.Φr d κ).2.1.1.2.1) ((D.Φr d κ).2.2.2.1).1 ℓ.toNode) : ℂ)) *
          ∏ ℓ ∈ inputLeaves LGg.garden, (cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGg.garden L
            (k + latticePoint L (D.Φr d κ).2.1.1.2.2) ((D.Φr d κ).2.2.2.2).1 ℓ.toNode) : ℂ))) := by
  set f : Fin 1 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, D.gd.prod_inputLeaves_glue D.decZ.2.1 D.hmtop D.hmbot f,
    D.hp.prod_inputLeaves_pair (fun z => f (topAddr z))]
  have hc := D.coset_I κ L k
  have hcr := D.coset_R κ L k
  have hcg := D.coset_G κ L k
  rw [mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only [rootHs]
    have e1 : botAddr (cpair m Qr Qg inner).lonePath ℓ.1 = (D.gd.ι₂ ℓ.toNode).1 := rfl
    rw [e1, extend_node]
    have e2 : (D.gd.ι₂ ℓ.toNode).1 = ((0 : Fin 1), lonePos m inner ++ ℓ.1.2) := by
      rw [GlueData.ι₂_val, ← cpair_lonePath m Qr Qg inner, botAddr, if_pos (Subsingleton.elim _ _)]
      rfl
    rw [e2]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : topAddr (pφi m ℓ.1) = (D.ιI ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hc ℓ.toNode]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : topAddr (pφr m inner (LGZ.garden.sig 0) ℓ.1) = (D.ιR ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcr ℓ.toNode]
    have e2 : (D.ιR ℓ.toNode).1 = ((0 : Fin 1), rBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2) := by
      simp [ιR, PairData.ιr, GlueData.ι₁, topAddr, D.sigZ]
      rfl
    rw [e2]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : topAddr (pφg m inner (LGZ.garden.sig 0) ℓ.1) = (D.ιG ℓ.toNode).1 := rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcg ℓ.toNode]
    have e2 : (D.ιG ℓ.toNode).1 = ((0 : Fin 1), gBase m inner (LG.garden.sig 0) ℓ.1.1 ++ ℓ.1.2) := by
      simp [ιG, PairData.ιg, GlueData.ι₁, topAddr, D.sigZ]
      rfl
    rw [e2]
    rfl

/-- The linked phases at the root cut: `e^{πiζ_aΩ_a x} e^{πiζ_bΩ_b y} = e^{πiA_e(x − y)}`. -/
theorem phase_root (γ δ : ℝ) (x y : ℝ) :
    Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.rootB * x : ℝ) *
          Complex.I) *
      Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.bB * y : ℝ) *
          Complex.I) =
      cutPh m (LG.garden.sig 0) L γ δ k y (D.Φr d κ).2.1 x := by
  set e := (D.Φr d κ).2.1
  set P0 := k
  set Px := k + latticePoint L e.1.1
  set Pr := k + latticePoint L e.1.2.1
  set Pg := k + latticePoint L e.1.2.2
  have sa : LGZ.garden.sign D.hp.rootB.toNode = LG.garden.sig 0 := by
    show pathSign (LGZ.garden.sig 0) [] = _
    simp [pathSign, D.sigZ]
  have sb : LGZ.garden.sign D.hp.bB.toNode = slotSign (LG.garden.sig 0) m.c := by
    show pathSign (LGZ.garden.sig 0) (bPath m inner) = _
    rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign, D.sigZ]
  have oa : omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.rootB =
      resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 (D.gd.ι₁ (D.hp.rootB.child j)) = cA m Px Pr Pg j :=
      fun j => by
        show k + latticePoint L ((κ.1 ∘ D.gd.ι₁) (D.hp.rootB.child j)) = _
        rw [D.κZ_slot κ j, CutTermData.coset_cA]
    have h0 : cosetDecoration LG.garden L k κ.1 (D.gd.ι₁ D.hp.rootB.toNode) = P0 := by
      show k + latticePoint L ((κ.1 ∘ D.gd.ι₁) D.hp.rootB.toNode) = _
      rw [D.κZ_rootB κ, latticePoint_zero, add_zero]
    unfold omegaNode
    simp only [Function.comp_apply]
    rw [hc 0, hc 1, hc 2, h0]
  have ob : omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.bB =
      resFactor (cB m P0 Pr Pg 0) (cB m P0 Pr Pg 1) (cB m P0 Pr Pg 2) Px := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 (D.gd.ι₁ (D.hp.bB.child j)) = cB m P0 Pr Pg j :=
      fun j => by
        show k + latticePoint L ((κ.1 ∘ D.gd.ι₁) (D.hp.bB.child j)) = _
        rw [D.κZ_bslot κ j, CutTermData.coset_cB]
    have h0 : cosetDecoration LG.garden L k κ.1 (D.gd.ι₁ D.hp.bB.toNode) = Px := by
      show k + latticePoint L ((κ.1 ∘ D.gd.ι₁) D.hp.bB.toNode) = _
      rw [D.κZ_bB κ]
    unfold omegaNode
    simp only [Function.comp_apply]
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

end RootData

end WaveTurbulence.Flower.ProtCut
