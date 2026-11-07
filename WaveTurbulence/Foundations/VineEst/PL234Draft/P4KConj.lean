/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData

/-!
# The kernel of a conjugate layered garden

For `IsConjugateBy LG LH e` (TARGET deftree/defgarden: trees, pairings, marks and layers transported along the root
permutation `e`, root signs reversed), the node, leaf and branching-node sets correspond along `e`
(`nodeEquiv`, `leafEquiv`, `branchEquiv`). Decorations, `ε`, `Ω`, the time domains and the input factors only see
the trees, the pairing, the marks and the layers. Only `ζ(𝒢)` and the phases see the signs, and they are conjugated.
The input leaves of `LH` (sign `+`, unmarked) are the transported partners of the input leaves of `LG`, with the
same layer and the same decoration value.

* **`kernelK_conj`**: `kernelK LH up' = conj (kernelK LG up)` when `up' ∘ e = up` and the root labels correspond.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

namespace Conj

variable (h : IsConjugateBy LG LH e)

/-- The node correspondence. -/
def nodeEquiv : GNode LG.garden.tree ≃ GNode LH.garden.tree where
  toFun a := ⟨(e a.1.1, a.1.2), by
    show a.1.2 ∈ (LH.garden.tree (e a.1.1)).nodes
    rw [h.tree_eq]; exact a.2⟩
  invFun a := ⟨(e.symm a.1.1, a.1.2), by
    show a.1.2 ∈ (LG.garden.tree (e.symm a.1.1)).nodes
    rw [← h.tree_eq, e.apply_symm_apply]; exact a.2⟩
  left_inv a := Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)
  right_inv a := Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

/-- The leaf correspondence. -/
def leafEquiv : GLeaf LG.garden.tree ≃ GLeaf LH.garden.tree where
  toFun a := ⟨(e a.1.1, a.1.2), by
    show a.1.2 ∈ (LH.garden.tree (e a.1.1)).leaves
    rw [h.tree_eq]; exact a.2⟩
  invFun a := ⟨(e.symm a.1.1, a.1.2), by
    show a.1.2 ∈ (LG.garden.tree (e.symm a.1.1)).leaves
    rw [← h.tree_eq, e.apply_symm_apply]; exact a.2⟩
  left_inv a := Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)
  right_inv a := Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

/-- The branching-node correspondence. -/
def branchEquiv : GBranch LG.garden.tree ≃ GBranch LH.garden.tree where
  toFun a := ⟨(e a.1.1, a.1.2), by
    show a.1.2 ∈ (LH.garden.tree (e a.1.1)).branching
    rw [h.tree_eq]; exact a.2⟩
  invFun a := ⟨(e.symm a.1.1, a.1.2), by
    show a.1.2 ∈ (LG.garden.tree (e.symm a.1.1)).branching
    rw [← h.tree_eq, e.apply_symm_apply]; exact a.2⟩
  left_inv a := Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)
  right_inv a := Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

theorem branch_toNode (b : GBranch LG.garden.tree) : (branchEquiv h b).toNode = nodeEquiv h b.toNode := rfl

theorem branch_child (b : GBranch LG.garden.tree) (i : Fin 3) :
    (branchEquiv h b).child i = nodeEquiv h (b.child i) := rfl

theorem leaf_toNode (ℓ : GLeaf LG.garden.tree) : (leafEquiv h ℓ).toNode = nodeEquiv h ℓ.toNode := rfl

theorem node_root (j : Fin w) : nodeEquiv h (GNode.root LG.garden.tree j) = GNode.root LH.garden.tree (e j) := rfl

theorem mark_leaf (ℓ : GLeaf LG.garden.tree) : LH.garden.mark (leafEquiv h ℓ) = LG.garden.mark ℓ := h.mark_eq ℓ

theorem pair_leaf (ℓ : GLeaf LG.garden.tree) :
    LH.garden.pair (leafEquiv h ℓ) = leafEquiv h (LG.garden.pair ℓ) := Subtype.ext (h.pair_eq ℓ)

theorem layer_node (a : GNode LG.garden.tree) : LH.layer (nodeEquiv h a) = LG.layer a := h.layer_eq a

theorem sign_node (a : GNode LG.garden.tree) : LH.garden.sign (nodeEquiv h a) = -LG.garden.sign a := by
  show TTree.pathSign (LH.garden.sig (e a.1.1)) a.1.2 = -TTree.pathSign (LG.garden.sig a.1.1) a.1.2
  rw [h.sig_eq]
  simp [TTree.pathSign]

include h in
theorem order_eq : LH.garden.order = LG.garden.order := by
  unfold Garden.order
  rw [← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun j _ => by rw [h.tree_eq]

include h in
theorem zeta_eq : LH.garden.zeta = conj LG.garden.zeta := by
  unfold Garden.zeta
  rw [map_prod, ← (branchEquiv h).prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [branch_toNode, sign_node]
  rcases Int.units_eq_one_or (LG.garden.sign b.toNode) with hs | hs <;> rw [hs] <;> simp

theorem isChildOf_iff (b' b : GBranch LG.garden.tree) :
    (branchEquiv h b').IsChildOf (branchEquiv h b) ↔ b'.IsChildOf b := by
  show (e b'.1.1 = e b.1.1 ∧ ∃ i : Fin 3, b'.1.2 = b.1.2 ++ [i]) ↔ (b'.1.1 = b.1.1 ∧ ∃ i : Fin 3, b'.1.2 = b.1.2 ++ [i])
  rw [e.apply_eq_iff_eq]

theorem isParentOf_iff (b : GBranch LG.garden.tree) (ℓ : GLeaf LG.garden.tree) :
    (branchEquiv h b).IsParentOf (leafEquiv h ℓ) ↔ b.IsParentOf ℓ := by
  show (e ℓ.1.1 = e b.1.1 ∧ ∃ i : Fin 3, ℓ.1.2 = b.1.2 ++ [i]) ↔ (ℓ.1.1 = b.1.1 ∧ ∃ i : Fin 3, ℓ.1.2 = b.1.2 ++ [i])
  rw [e.apply_eq_iff_eq]

theorem isFlower_iff (ℓ : GLeaf LG.garden.tree) : LH.garden.IsFlower (leafEquiv h ℓ) ↔ LG.garden.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [mark_leaf]

theorem isLone_iff (ℓ : GLeaf LG.garden.tree) : LH.garden.IsLone (leafEquiv h ℓ) ↔ LG.garden.IsLone ℓ := by
  unfold Garden.IsLone
  rw [mark_leaf]

theorem flowerParent_iff (b : GBranch LG.garden.tree) :
    LH.garden.IsFlowerParent (branchEquiv h b) ↔ LG.garden.IsFlowerParent b := by
  unfold Garden.IsFlowerParent
  rw [← (leafEquiv h).exists_congr_right]
  exact exists_congr fun ℓ => and_congr (isFlower_iff h ℓ) (isParentOf_iff h b ℓ)

theorem loneParent_iff (b : GBranch LG.garden.tree) :
    LH.garden.IsLoneParent (branchEquiv h b) ↔ LG.garden.IsLoneParent b := by
  unfold Garden.IsLoneParent
  rw [← (leafEquiv h).exists_congr_right]
  exact exists_congr fun ℓ => and_congr (isLone_iff h ℓ) (isParentOf_iff h b ℓ)

/-- The free branching nodes correspond. -/
def freeEquiv : LG.garden.FreeBranch ≃ LH.garden.FreeBranch :=
  (branchEquiv h).subtypeEquiv fun b => not_congr (flowerParent_iff h b).symm

theorem extendTime_eq (s : ℝ) (τ : LG.garden.FreeBranch → ℝ) (b : GBranch LG.garden.tree) :
    LH.garden.extendTime s (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (freeEquiv h) τ) (branchEquiv h b) =
      LG.garden.extendTime s τ b := by
  unfold Garden.extendTime
  by_cases hb : LG.garden.IsFlowerParent b
  · rw [dite_eq_left hb, dite_eq_left ((flowerParent_iff h b).2 hb)]
  · rw [dite_eq_right hb, dite_eq_right (fun h' => hb ((flowerParent_iff h b).1 h'))]
    have e1 : (⟨branchEquiv h b, fun h' => hb ((flowerParent_iff h b).1 h')⟩ : LH.garden.FreeBranch) =
        freeEquiv h (⟨b, hb⟩ : LG.garden.FreeBranch) := rfl
    rw [e1, MeasurableEquiv.coe_piCongrLeft]
    exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) (freeEquiv h) τ _

variable {d : ℕ}

theorem omega_eq (k : GNode LG.garden.tree → Mom d) (b : GBranch LG.garden.tree) :
    omegaNode LH.garden (fun a => k ((nodeEquiv h).symm a)) (branchEquiv h b) = omegaNode LG.garden k b := by
  unfold omegaNode
  simp only [branch_child, branch_toNode, Equiv.symm_apply_apply]

theorem phaseProd_eq (L γ δ : ℝ) (k : GNode LG.garden.tree → Mom d) (τ : GBranch LG.garden.tree → ℝ) :
    phaseProd L γ δ LH.garden (fun a => k ((nodeEquiv h).symm a)) (fun b => τ ((branchEquiv h).symm b)) =
      conj (phaseProd L γ δ LG.garden k τ) := by
  unfold phaseProd
  rw [map_prod, ← (branchEquiv h).prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [omega_eq, branch_toNode, sign_node, Equiv.symm_apply_apply]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast [Units.val_neg]
  ring

theorem mem_kDomain_iff (up : GBranch LG.garden.tree → ℝ) (up' : GBranch LH.garden.tree → ℝ)
    (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) (τ : GBranch LG.garden.tree → ℝ) :
    (fun b => τ ((branchEquiv h).symm b)) ∈ kDomain LH up' s ↔ τ ∈ kDomain LG up s := by
  unfold kDomain
  simp only [Set.mem_ofPred_eq]
  rw [← (branchEquiv h).forall_congr_right]
  refine forall_congr' fun b => ?_
  rw [branch_toNode, layer_node, hup, Equiv.symm_apply_apply, loneParent_iff, ← (branchEquiv h).forall_congr_right]
  simp only [isChildOf_iff, Equiv.symm_apply_apply]

theorem phaseIntegral_eq (L γ δ : ℝ) (k : GNode LG.garden.tree → Mom d) (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) :
    phaseIntegral L γ δ LH.garden (kDomain LH up' s) s (fun a => k ((nodeEquiv h).symm a)) =
      conj (phaseIntegral L γ δ LG.garden (kDomain LG up s) s k) := by
  unfold phaseIntegral
  rw [← integral_conj, ← (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (freeEquiv h)).integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hT : LH.garden.extendTime s (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (freeEquiv h) τ) =
      fun b => LG.garden.extendTime s τ ((branchEquiv h).symm b) := by
    funext b'
    obtain ⟨b, rfl⟩ := (branchEquiv h).surjective b'
    rw [extendTime_eq, Equiv.symm_apply_apply]
  simp only
  rw [hT]
  by_cases hm : LG.garden.extendTime s τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem ((mem_kDomain_iff h up up' hup s _).2 hm), Set.indicator_of_mem hm]
    exact phaseProd_eq h L γ δ k _
  · rw [Set.indicator_of_notMem (fun h' => hm ((mem_kDomain_iff h up up' hup s _).1 h')),
      Set.indicator_of_notMem hm, map_zero]

/-- Decorations correspond. -/
def decEquiv (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ) :
    GenDecoration LG.garden d nroot nfl ≃ GenDecoration LH.garden d nroot' nfl where
  toFun κ := ⟨fun a => κ.1 ((nodeEquiv h).symm a), ⟨fun b' => by
      obtain ⟨b, rfl⟩ := (branchEquiv h).surjective b'
      show κ.1 ((nodeEquiv h).symm (nodeEquiv h b.toNode)) =
        κ.1 ((nodeEquiv h).symm (nodeEquiv h (b.child 0))) - κ.1 ((nodeEquiv h).symm (nodeEquiv h (b.child 1))) +
          κ.1 ((nodeEquiv h).symm (nodeEquiv h (b.child 2)))
      simp only [Equiv.symm_apply_apply]
      exact κ.2.1.1 b, fun ℓ' => by
      obtain ⟨ℓ, rfl⟩ := (leafEquiv h).surjective ℓ'
      show κ.1 ((nodeEquiv h).symm (leafEquiv h ℓ).toNode) =
        κ.1 ((nodeEquiv h).symm (LH.garden.pair (leafEquiv h ℓ)).toNode)
      rw [pair_leaf, leaf_toNode, leaf_toNode, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact κ.2.1.2 ℓ⟩, fun j => by
      obtain ⟨i, rfl⟩ := e.surjective j
      show κ.1 ((nodeEquiv h).symm (nodeEquiv h (GNode.root LG.garden.tree i))) = nroot' (e i)
      rw [Equiv.symm_apply_apply, hroot]
      exact κ.2.2.1 i, fun ℓ' hℓ => by
      obtain ⟨ℓ, rfl⟩ := (leafEquiv h).surjective ℓ'
      show κ.1 ((nodeEquiv h).symm (nodeEquiv h ℓ.toNode)) = nfl
      rw [Equiv.symm_apply_apply]
      exact κ.2.2.2 ℓ ((isFlower_iff h ℓ).1 hℓ)⟩
  invFun κ := ⟨fun a => κ.1 (nodeEquiv h a), ⟨fun b => κ.2.1.1 (branchEquiv h b), fun ℓ => by
      show κ.1 (leafEquiv h ℓ).toNode = κ.1 (nodeEquiv h (LG.garden.pair ℓ).toNode)
      rw [← leaf_toNode, ← pair_leaf]
      exact κ.2.1.2 _⟩, fun j => by
      show κ.1 (GNode.root LH.garden.tree (e j)) = nroot j
      rw [κ.2.2.1, hroot], fun ℓ hℓ => κ.2.2.2 (leafEquiv h ℓ) ((isFlower_iff h ℓ).2 hℓ)⟩
  left_inv κ := Subtype.ext (funext fun a => by simp only [Equiv.symm_apply_apply])
  right_inv κ := Subtype.ext (funext fun a => by simp only [Equiv.apply_symm_apply])

theorem epsDec_eq (κ : GNode LG.garden.tree → (Fin d → ℤ)) :
    epsDec LH.garden (fun a => κ ((nodeEquiv h).symm a)) = epsDec LG.garden κ := by
  unfold epsDec
  rw [← (branchEquiv h).prod_comp]
  simp only [branch_child, Equiv.symm_apply_apply]

/-- The input leaves of `LH` are the transported partners of those of `LG`. -/
theorem inputs_eq (F : ℕ → Mom d → ℝ) (κ : GNode LG.garden.tree → Mom d)
    (hκ : ∀ ℓ : GLeaf LG.garden.tree, κ ℓ.toNode = κ (LG.garden.pair ℓ).toNode) :
    ∏ ℓ ∈ inputLeaves LH.garden, (F (LH.layer ℓ.toNode) (κ ((nodeEquiv h).symm ℓ.toNode)) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (κ ℓ.toNode) : ℂ) := by
  symm
  refine Finset.prod_nbij' (fun ℓ => leafEquiv h (LG.garden.pair ℓ))
    (fun ℓ' => LG.garden.pair ((leafEquiv h).symm ℓ')) ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    obtain ⟨hs, hm⟩ := hℓ
    have hne : LG.garden.pair ℓ ≠ ℓ := fun he => ((LG.garden.pair_eq_iff ℓ).1 he) hm
    refine ⟨?_, ?_⟩
    · rw [leaf_toNode, sign_node]
      show -nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
      rw [LG.garden.pair_sign ℓ hne, neg_neg]
      exact hs
    · rw [mark_leaf]
      by_contra hm'
      have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 hm'
      rw [LG.garden.pair_pair] at this
      exact hne this.symm
  · intro ℓ' hℓ'
    obtain ⟨ℓ, rfl⟩ := (leafEquiv h).surjective ℓ'
    simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ' ⊢
    obtain ⟨hs, hm⟩ := hℓ'
    rw [mark_leaf] at hm
    rw [leaf_toNode, sign_node] at hs
    have hne : LG.garden.pair ℓ ≠ ℓ := fun he => ((LG.garden.pair_eq_iff ℓ).1 he) hm
    rw [Equiv.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · show nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
      rw [LG.garden.pair_sign ℓ hne]
      exact hs
    · by_contra hm'
      have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 hm'
      rw [LG.garden.pair_pair] at this
      exact hne this.symm
  · intro ℓ _
    simp only [Equiv.symm_apply_apply, LG.garden.pair_pair]
  · intro ℓ' _
    simp only [LG.garden.pair_pair, Equiv.apply_symm_apply]
  · intro ℓ _
    rw [leaf_toNode, layer_node, Equiv.symm_apply_apply, ← hκ ℓ, ← LG.isLayering.2 ℓ]

theorem summand_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) (k₀ : Mom d)
    (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ)
    (κ : GenDecoration LG.garden d nroot nfl) :
    (epsDec LH.garden (decEquiv h nroot nroot' hroot nfl κ).1 : ℂ) *
        phaseIntegral L γ δ LH.garden (kDomain LH up' s) s
          (cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1) *
        ∏ ℓ ∈ inputLeaves LH.garden, (F (LH.layer ℓ.toNode)
          (cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 ℓ.toNode) : ℂ) =
      conj ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) := by
  have hd : (decEquiv h nroot nroot' hroot nfl κ).1 = fun a => κ.1 ((nodeEquiv h).symm a) := rfl
  have hc : cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 =
      fun a => cosetDecoration LG.garden L k₀ κ.1 ((nodeEquiv h).symm a) := rfl
  have hκ : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k₀ κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    unfold cosetDecoration
    rw [κ.2.1.2 ℓ]
  rw [hc, hd, epsDec_eq h κ.1, phaseIntegral_eq h L γ δ (cosetDecoration LG.garden L k₀ κ.1) up up' hup s,
    inputs_eq h F _ hκ, map_mul, map_mul, Complex.conj_ofReal, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun ℓ _ => (Complex.conj_ofReal _).symm

/-- **The kernel of a conjugate garden is the conjugate kernel.** -/
theorem kernelK_conj (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) (k₀ : Mom d)
    (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LH up' s k₀ nroot' nfl = conj (kernelK L γ δ F LG up s k₀ nroot nfl) := by
  unfold kernelK
  rw [map_mul, map_mul, map_pow, Complex.conj_ofReal, order_eq h, zeta_eq h, Complex.conj_tsum,
    ← (decEquiv h nroot nroot' hroot nfl).tsum_eq]
  congr 1
  exact tsum_congr fun κ => summand_eq h L γ δ F up up' hup s k₀ nroot nroot' hroot nfl κ

end Conj

/-- **Prop 6.3 (i), kernel part**: conjugating a couple exchanges `t` and `s` and conjugates the kernel. -/
theorem KQstar_conj {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {LG LH : LayeredGarden 2}
    (h : IsConjugateCouple LG LH) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ F LH t s k = star (KQstar L γ δ F LG s t k) := by
  unfold KQstar
  refine Conj.kernelK_conj h L γ δ F _ _ (fun b => ?_) 0 k _ _ (fun _ => rfl) 0
  rcases b with ⟨⟨i, p⟩, hp⟩
  show (if Equiv.swap (0 : Fin 2) 1 i = 0 then t else s) = if i = 0 then s else t
  fin_cases i <;> simp

/-- **Prop 6.3 (ii), kernel part**: conjugating a paired tree conjugates its kernel. -/
theorem KTstar_conj {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {LG LH : LayeredGarden 1}
    (h : IsConjugateTree LG LH) (t s : ℝ) (k : Mom d) :
    KTstar L γ δ F LH t s k = star (KTstar L γ δ F LG t s k) := by
  unfold KTstar
  exact Conj.kernelK_conj h L γ δ F _ _ (fun _ => rfl) s k _ _ (fun _ => rfl) 0

end WaveTurbulence.PL234
