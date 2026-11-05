/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKNodeG

/-!
# O-FK, part 3: the flower-tree term as a tree term with one marked leaf

`fOp_eq_treeTermG`: `𝒥_F[b](t) = 𝒥^G_{F.toTree}(t)`, where the flower leaf carries the input `b` (evaluated at its
parent's time) and every other leaf carries `a(p)`. The proof is an induction on `F`; the node case is the root
splitting `treeTermG_node` in the stem slot.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

/-! ## One leaf input; leaf data with a marked leaf -/

/-- One time-dependent leaf input, with a summable majorant. -/
structure LeafIn (d : ℕ) where
  B : ℝ → (Fin d → ℤ) → ℂ
  U : (Fin d → ℤ) → ℝ
  cont : ∀ q, Continuous fun s => B s q
  summ : Summable U
  nonneg : ∀ k, 0 ≤ U k
  bound : ∀ s q, ‖B s q‖ ≤ U q

/-- The constant input `a(p)`. -/
noncomputable def LeafIn.const {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) : LeafIn d where
  B _ := aP
  U k := ‖aP k‖
  cont _ := continuous_const
  summ := haP
  nonneg _ := norm_nonneg _
  bound _ _ := le_rfl

/-- The input `b` on `[p, p+1]`, extended constantly. -/
noncomputable def LeafIn.ofGood {p : ℕ} {b : ArrI p d} (hb : Good p b) : LeafIn d where
  B := Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b
  U := hb.maj.choose
  cont q := hb.iccExtend q
  summ := hb.maj.choose_spec.1
  nonneg := hb.maj.choose_spec.2.1
  bound s q := hb.maj.choose_spec.2.2 _ q

open Classical in
/-- Leaf data with the input `A₁` at the marked leaf `f` and `A₀` elsewhere. -/
noncomputable def LeafData.mark (T : TTree) (f : GLeaf (single T)) (A₁ A₀ : LeafIn d) : LeafData T d where
  B ℓ := if ℓ = f then A₁.B else A₀.B
  U ℓ := if ℓ = f then A₁.U else A₀.U
  cont ℓ q := by split_ifs; exacts [A₁.cont q, A₀.cont q]
  summ ℓ := by split_ifs; exacts [A₁.summ, A₀.summ]
  nonneg ℓ k := by split_ifs; exacts [A₁.nonneg k, A₀.nonneg k]
  bound ℓ s q := by split_ifs; exacts [A₁.bound s q, A₀.bound s q]

theorem LeafData.mark_B_self (T : TTree) (f : GLeaf (single T)) (A₁ A₀ : LeafIn d) :
    (LeafData.mark T f A₁ A₀).B f = A₁.B := by
  simp [LeafData.mark]

theorem LeafData.mark_B_ne (T : TTree) (f : GLeaf (single T)) (A₁ A₀ : LeafIn d)
    {ℓ : GLeaf (single T)} (h : ℓ ≠ f) : (LeafData.mark T f A₁ A₀).B ℓ = A₀.B := by
  simp [LeafData.mark, h]

theorem LeafData.mark_U_self (T : TTree) (f : GLeaf (single T)) (A₁ A₀ : LeafIn d) :
    (LeafData.mark T f A₁ A₀).U f = A₁.U := by
  simp [LeafData.mark]

theorem LeafData.mark_U_ne (T : TTree) (f : GLeaf (single T)) (A₁ A₀ : LeafIn d)
    {ℓ : GLeaf (single T)} (h : ℓ ≠ f) : (LeafData.mark T f A₁ A₀).U ℓ = A₀.U := by
  simp [LeafData.mark, h]

theorem LeafData.mark_res_B_emb {T S : TTree} {j : Fin 3} (h : IsSubtreeAt T S j) (g : GLeaf (single S))
    (A₁ A₀ : LeafIn d) (ℓ : GLeaf (single S)) :
    ((LeafData.mark T (h.embL g) A₁ A₀).res h).B ℓ = (LeafData.mark S g A₁ A₀).B ℓ := by
  simp only [LeafData.res, LeafData.mark, h.embL_injective.eq_iff]

theorem LeafData.mark_res_B_off {T S : TTree} {j : Fin 3} (h : IsSubtreeAt T S j) (f : GLeaf (single T))
    (hf : ∀ ℓ, h.embL ℓ ≠ f) (A₁ A₀ : LeafIn d) (ℓ : GLeaf (single S)) :
    ((LeafData.mark T f A₁ A₀).res h).B ℓ = A₀.B := by
  simp only [LeafData.res, LeafData.mark, hf ℓ, ↓reduceIte]

/-- `treeTermG` only depends on the inputs `D.B`. -/
theorem treeTermG_congr (p : ℕ) (T : TTree) {D D' : LeafData T d} (h : ∀ ℓ, D.B ℓ = D'.B ℓ) (t : ℝ)
    (n : Fin d → ℤ) : treeTermG L γ δ p T D t n = treeTermG L γ δ p T D' t n := by
  have hl : ∀ κ τ t, leafFactorG T D κ τ t = leafFactorG T D' κ τ t := by
    intro κ τ t
    simp only [leafFactorG, h]
  simp only [treeTermG, timeIntG, hl]

/-! ## The stem slot -/

section Slots

variable (l m r : TTree) (A₁ : LeafIn d) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)

theorem embL_ne_of_head {T S S' : TTree} {j j' : Fin 3} (h : IsSubtreeAt T S j) (h' : IsSubtreeAt T S' j')
    (hj : j ≠ j') (ℓ : GLeaf (single S)) (g : GLeaf (single S')) : h.embL ℓ ≠ h'.embL g := by
  intro e
  have := congrArg (fun x => x.1.2) e
  simp only [IsSubtreeAt.embL, List.cons.injEq] at this
  exact hj this.1

theorem treeTermG_mark_left (p : ℕ) (g : GLeaf (single l)) {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    treeTermG L γ δ p (TTree.node l m r)
        (LeafData.mark _ ((isSubtreeAt_left l m r).embL g) A₁ (LeafIn.const haP)) t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTermG L γ δ p l (LeafData.mark l g A₁ (LeafIn.const haP)) s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (treeTerm L γ δ p r aP s) n := by
  rw [treeTermG_node L γ δ l m r p _ ht]
  have h1 : ∀ s, treeTermG L γ δ p l ((LeafData.mark _ ((isSubtreeAt_left l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_left l m r)) s =
      treeTermG L γ δ p l (LeafData.mark l g A₁ (LeafIn.const haP)) s := fun s => funext fun k =>
    treeTermG_congr L γ δ p l (LeafData.mark_res_B_emb _ g A₁ _) s k
  have h2 : ∀ s, treeTermG L γ δ p m ((LeafData.mark _ ((isSubtreeAt_left l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_mid l m r)) s = treeTerm L γ δ p m aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p m _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  have h3 : ∀ s, treeTermG L γ δ p r ((LeafData.mark _ ((isSubtreeAt_left l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_right l m r)) s = treeTerm L γ δ p r aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p r _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  simp only [h1, h2, h3]

theorem treeTermG_mark_mid (p : ℕ) (g : GLeaf (single m)) {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    treeTermG L γ δ p (TTree.node l m r)
        (LeafData.mark _ ((isSubtreeAt_mid l m r).embL g) A₁ (LeafIn.const haP)) t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
        (fun k => (starRingEnd ℂ) (treeTermG L γ δ p m (LeafData.mark m g A₁ (LeafIn.const haP)) s k))
        (treeTerm L γ δ p r aP s) n := by
  rw [treeTermG_node L γ δ l m r p _ ht]
  have h1 : ∀ s, treeTermG L γ δ p l ((LeafData.mark _ ((isSubtreeAt_mid l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_left l m r)) s = treeTerm L γ δ p l aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p l _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  have h2 : ∀ s, treeTermG L γ δ p m ((LeafData.mark _ ((isSubtreeAt_mid l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_mid l m r)) s =
      treeTermG L γ δ p m (LeafData.mark m g A₁ (LeafIn.const haP)) s := fun s => funext fun k =>
    treeTermG_congr L γ δ p m (LeafData.mark_res_B_emb _ g A₁ _) s k
  have h3 : ∀ s, treeTermG L γ δ p r ((LeafData.mark _ ((isSubtreeAt_mid l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_right l m r)) s = treeTerm L γ δ p r aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p r _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  simp only [h1, h2, h3]

theorem treeTermG_mark_right (p : ℕ) (g : GLeaf (single r)) {t : ℝ} (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) :
    treeTermG L γ δ p (TTree.node l m r)
        (LeafData.mark _ ((isSubtreeAt_right l m r).embL g) A₁ (LeafIn.const haP)) t n =
      ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
        (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k))
        (treeTermG L γ δ p r (LeafData.mark r g A₁ (LeafIn.const haP)) s) n := by
  rw [treeTermG_node L γ δ l m r p _ ht]
  have h1 : ∀ s, treeTermG L γ δ p l ((LeafData.mark _ ((isSubtreeAt_right l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_left l m r)) s = treeTerm L γ δ p l aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p l _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  have h2 : ∀ s, treeTermG L γ δ p m ((LeafData.mark _ ((isSubtreeAt_right l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_mid l m r)) s = treeTerm L γ δ p m aP s := fun s => funext fun k =>
    treeTermG_const L γ δ p m _ (fun ℓ s => by
      rw [LeafData.mark_res_B_off _ _ (fun ℓ => embL_ne_of_head _ _ (by decide) ℓ g)]; rfl) s k
  have h3 : ∀ s, treeTermG L γ δ p r ((LeafData.mark _ ((isSubtreeAt_right l m r).embL g) A₁
      (LeafIn.const haP)).res (isSubtreeAt_right l m r)) s =
      treeTermG L γ δ p r (LeafData.mark r g A₁ (LeafIn.const haP)) s := fun s => funext fun k =>
    treeTermG_congr L γ δ p r (LeafData.mark_res_B_emb _ g A₁ _) s k
  simp only [h1, h2, h3]

end Slots

/-! ## Flower trees -/

/-- The leaf data of a flower tree: `A₁` at the flower, `a(p)` elsewhere. -/
noncomputable def flowerData (F : FTree) (A₁ : LeafIn d) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) : LeafData F.toTree d :=
  LeafData.mark F.toTree F.flowerLeaf A₁ (LeafIn.const haP)

/-- The root splitting of a flower tree term, in the stem slot. -/
theorem treeTermG_flowerData_node (p : ℕ) (A₁ : LeafIn d) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) (i : Fin 3) (F : FTree) (T₁ T₂ : TTree) {t : ℝ} (ht : (p : ℝ) ≤ t)
    (n : Fin d → ℤ) :
    treeTermG L γ δ p (FTree.node i F T₁ T₂).toTree (flowerData (FTree.node i F T₁ T₂) A₁ haP) t n =
      ∫ s in (p : ℝ)..t, slotNonlin L γ δ i s (treeTermG L γ δ p F.toTree (flowerData F A₁ haP) s)
        (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n := by
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero]
    exact treeTermG_mark_left L γ δ F.toTree T₁ T₂ A₁ haP p F.flowerLeaf ht n
  · simp only [Fin.mk_one, slotNonlin_one]
    exact treeTermG_mark_mid L γ δ T₁ F.toTree T₂ A₁ haP p F.flowerLeaf ht n
  · simp only [Fin.reduceFinMk, slotNonlin_two]
    exact treeTermG_mark_right L γ δ T₁ T₂ F.toTree A₁ haP p F.flowerLeaf ht n

/-- **`𝒥_F[b]` is the tree term of `F.toTree` with `b` at the flower.** -/
theorem fOp_eq_treeTermG (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {b : ArrI p d}
    (hb : Good p b) :
    ∀ (F : FTree) (t : Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ),
      fOp L γ δ p aP F b t n = treeTermG L γ δ p F.toTree (flowerData F (LeafIn.ofGood hb) haP) t n
  | .flower, t, n => by
    refine Eq.trans ?_ (treeTermG_leaf L γ δ p (d := d)
      (flowerData FTree.flower (LeafIn.ofGood hb) haP) t n).symm
    show b t n = (LeafData.mark FTree.flower.toTree FTree.flower.flowerLeaf _ _).B
      FTree.flower.flowerLeaf t n
    rw [LeafData.mark_B_self]
    show b t n = Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n
    rw [Set.IccExtend_val]
  | .node i F T₁ T₂, t, n => by
    have ih := fOp_eq_treeTermG p haP hb F
    rw [treeTermG_flowerData_node L γ δ p _ haP i F T₁ T₂ t.2.1 n]
    show ∫ s in (p : ℝ)..t, slotNonlin L γ δ i s
      (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (fOp L γ δ p aP F b) s)
      (treeTerm L γ δ p T₁ aP s) (treeTerm L γ δ p T₂ aP s) n = _
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le t.2.1] at hs
    have hs' : s ∈ Icc (p : ℝ) (p + 1) := ⟨hs.1, hs.2.trans t.2.2⟩
    have : Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (fOp L γ δ p aP F b) s =
        treeTermG L γ δ p F.toTree (flowerData F (LeafIn.ofGood hb) haP) s := by
      funext k
      rw [Set.IccExtend_of_mem _ _ hs', ih]
    simp only [this]

end WaveTurbulence.SysAPI
