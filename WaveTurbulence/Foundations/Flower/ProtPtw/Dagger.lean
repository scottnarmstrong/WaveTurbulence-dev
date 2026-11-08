/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.SelBound

/-! # D6a PROT-PTW: the dagger is a weight of the pinned link

A dagger (`TermChildIndicator`) reads the momenta of the children of the terminal chain node `T` (the lone parent).
On a paired tree the lone leaf is a child of `T` and carries the output; the children differences of `T` are its link
parameters (`xNode`, `yNode`), which are `±` those of its link's chosen branch (`tree_xy_link`). So on link arrays the
dagger depends only on the lattice pair of the link containing `T`: it is a link weight of that (exceptional) link,
o82 Prop 14.2's bounded multiplier `R_E` of the exceptional link variables. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links TTree

variable {G : Garden 1} {X : RegChain}

/-- The lone leaf is the child of the lone parent at the last index of the lone path. -/
theorem loneLeaf_eq_child (hX : X.DecodesTree G) (hne : X.lonePath ≠ []) (b : GBranch G.tree)
    (hb : b.1.2 = X.lonePath.dropLast) :
    (loneLeaf hX).toNode = b.child (X.lonePath.getLast hne) := by
  apply Subtype.ext
  change ((0 : Fin 1), X.lonePath) = (b.1.1, b.1.2 ++ [X.lonePath.getLast hne])
  rw [hb, List.dropLast_append_getLast, Subsingleton.elim b.1.1 0]

/-- With the pinned link's parameters zero and root value zero, the terminal node and its children carry zero. -/
theorem star_zero (hX : X.DecodesTree G) (hne : X.lonePath ≠ []) {V : Type} [AddCommGroup V]
    (θ : Fin (X.treeLinks (G.sig 0)).length → V × V) (j₀ : Fin (X.treeLinks (G.sig 0)).length) (e₀ : Fin 2)
    (hθ : θ j₀ = (0, 0)) (hT : (treeLinkBranch hX j₀ e₀).1.2 = X.lonePath.dropLast) (c : Fin 3) :
    (treeDecOfParams hX (0 : V) θ).1 ((treeLinkBranch hX j₀ e₀).child c) = 0 := by
  have hκ : IsDecoration G (treeDecOfParams hX (0 : V) θ).1 := (treeDecOfParams hX (0 : V) θ).2.1
  have hroot : (treeDecOfParams hX (0 : V) θ).1 (GNode.root G.tree 0) = 0 := (treeDecOfParams hX (0 : V) θ).2.2
  have hxc : xNode (treeDecOfParams hX (0 : V) θ).1 (treeChosenBranch hX j₀) = 0 := by
    rw [tree_xNode_decOfParams hX (0 : V) θ j₀, hθ]
  have hyc : yNode (treeDecOfParams hX (0 : V) θ).1 (treeChosenBranch hX j₀) = 0 := by
    rw [tree_yNode_decOfParams hX (0 : V) θ j₀, hθ]
  generalize (treeDecOfParams hX (0 : V) θ).1 = κ at hκ hroot hxc hyc ⊢
  have hxy : xNode κ (treeLinkBranch hX j₀ e₀) = 0 ∧ yNode κ (treeLinkBranch hX j₀ e₀) = 0 := by
    fin_cases e₀
    · exact ⟨hxc, hyc⟩
    · obtain ⟨s₁, s₂, h, -⟩ := tree_xy_link hX hκ (List.get_mem (X.treeLinks (G.sig 0)) j₀)
        (treeChosenBranch hX j₀) (treeLinkBranch hX j₀ 1) rfl rfl
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.trans (by rw [hxc, smul_zero]), h2.trans (by rw [hyc, smul_zero])⟩
      · exact ⟨h1.trans (by rw [hyc, smul_zero]), h2.trans (by rw [hxc, smul_zero])⟩
  generalize treeLinkBranch hX j₀ e₀ = b at hxy hT ⊢
  have h0 : κ (b.child 0) = κ b.toNode := by
    have := hxy.1; unfold xNode at this; exact sub_eq_zero.mp this
  have h2 : κ (b.child 2) = κ b.toNode := by
    have := hxy.2; unfold yNode at this; exact (sub_eq_zero.mp this).symm
  have h1 : κ (b.child 1) = κ b.toNode := by
    have h := hκ.1 b
    rw [h0, h2] at h
    have h' : κ (b.child 1) = κ b.toNode + κ b.toNode - (κ b.toNode - κ (b.child 1) + κ b.toNode) := by abel
    rw [h', ← h]; abel
  have hall (c' : Fin 3) : κ (b.child c') = κ b.toNode := by
    fin_cases c'
    · exact h0
    · exact h1
    · exact h2
  have hb : κ b.toNode = 0 := by
    rw [← hall (X.lonePath.getLast hne), ← loneLeaf_eq_child hX hne b hT, ← tree_root_eq_lone hX hκ, hroot]
  rw [hall c, hb]

/-- **Decorations agreeing on the pinned link agree at the terminal node's children.** -/
theorem coset_children_eq (hX : X.DecodesTree G) (hne : X.lonePath ≠ []) {d : ℕ} (L : ℝ) (k : Mom d)
    (j₀ : Fin (X.treeLinks (G.sig 0)).length) (e₀ : Fin 2)
    (hT : (treeLinkBranch hX j₀ e₀).1.2 = X.lonePath.dropLast)
    (p p' : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) (hp : ∀ e, p (j₀, e) = p' (j₀, e)) (c : Fin 3) :
    cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1
        ((treeLinkBranch hX j₀ e₀).child c) =
      cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p' (j, 0), p' (j, 1)))).1
        ((treeLinkBranch hX j₀ e₀).child c) := by
  rw [← tree_decOfParams_eq_coset hX L k, ← tree_decOfParams_eq_coset hX L k]
  set a := (treeLinkBranch hX j₀ e₀).child c
  let u : MomentumCoordinate (X.treeLinks (G.sig 0)).length → Mom d := fun q => match q with
    | none => k
    | some (i, e) => latticePoint L (p (i, e))
  let u' : MomentumCoordinate (X.treeLinks (G.sig 0)).length → Mom d := fun q => match q with
    | none => k
    | some (i, e) => latticePoint L (p' (i, e))
  have hu : momentumRowEval u (treeNodeRow hX a) = (treeDecOfParams hX k (fun j =>
      ((latticePoint L (p (j, 0)), latticePoint L (p (j, 1))) : Mom d × Mom d))).1 a := treeNodeRow_eval hX a u
  have hu' : momentumRowEval u' (treeNodeRow hX a) = (treeDecOfParams hX k (fun j =>
      ((latticePoint L (p' (j, 0)), latticePoint L (p' (j, 1))) : Mom d × Mom d))).1 a := treeNodeRow_eval hX a u'
  have hd := treeNodeRow_eval hX a (u - u')
  have hz : (treeDecOfParams hX ((u - u') none) (fun j => ((u - u') (some (j, 0)), (u - u') (some (j, 1))))).1 a = 0 := by
    have h0 : (u - u') none = 0 := by simp [u, u']
    rw [h0]
    apply star_zero hX hne _ j₀ e₀ _ hT c
    simp [u, u', hp 0, hp 1]
  have hlin : momentumRowEval (u - u') (treeNodeRow hX a) =
      momentumRowEval u (treeNodeRow hX a) - momentumRowEval u' (treeNodeRow hX a) := by
    simp only [momentumRowEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  rw [hz, hlin] at hd
  change (treeDecOfParams hX k (fun j =>
      ((latticePoint L (p (j, 0)), latticePoint L (p (j, 1))) : Mom d × Mom d))).1 a =
    (treeDecOfParams hX k (fun j =>
      ((latticePoint L (p' (j, 0)), latticePoint L (p' (j, 1))) : Mom d × Mom d))).1 a
  rw [← hu, ← hu']
  exact sub_eq_zero.mp hd

/-- The dagger as a weight of the pinned link's lattice pair. -/
def daggerWeight (hX : X.DecodesTree G) {d : ℕ} (L : ℝ) (k : Mom d) (ind : (GNode G.tree → Mom d) → ℝ)
    (j₀ : Fin (X.treeLinks (G.sig 0)).length) (q : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  (ind (cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ)
    (fun j => if j = j₀ then q else (0, 0))).1) : ℂ)

theorem ind_coset_eq_dagger (hX : X.DecodesTree G) (hne : X.lonePath ≠ []) {d : ℕ} (L : ℝ) (k : Mom d)
    (ind : (GNode G.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind)
    (j₀ : Fin (X.treeLinks (G.sig 0)).length) (e₀ : Fin 2)
    (hT : (treeLinkBranch hX j₀ e₀).1.2 = X.lonePath.dropLast)
    (p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) :
    (ind (cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) : ℂ) =
      daggerWeight hX L k ind j₀ (p (j₀, 0), p (j₀, 1)) := by
  unfold daggerWeight
  congr 1
  apply hind.2
  intro a ha0 hane hadl
  set c : Fin 3 := a.1.2.getLast hane
  have ha : a = (treeLinkBranch hX j₀ e₀).child c := by
    apply Subtype.ext
    change a.1 = ((treeLinkBranch hX j₀ e₀).1.1, (treeLinkBranch hX j₀ e₀).1.2 ++ [c])
    rw [hT, ← hadl, List.dropLast_append_getLast]
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [ha]
  let p' : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ := fun ie =>
    if ie.1 = j₀ then (if ie.2 = 0 then p (j₀, 0) else p (j₀, 1)) else 0
  have hpp : (fun j => (p' (j, 0), p' (j, 1))) =
      (fun j => if j = j₀ then (p (j₀, 0), p (j₀, 1)) else ((0 : Fin d → ℤ), (0 : Fin d → ℤ))) := by
    funext j
    by_cases hj : j = j₀ <;> simp [p', hj]
  rw [coset_children_eq hX hne L k j₀ e₀ hT p p' (fun e => by fin_cases e <;> simp [p']) c, hpp]

theorem daggerWeight_norm_le (hX : X.DecodesTree G) {d : ℕ} (L : ℝ) (k : Mom d) (ind : (GNode G.tree → Mom d) → ℝ)
    (hind : TermChildIndicator X ind) (j₀ : Fin (X.treeLinks (G.sig 0)).length) (q : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖daggerWeight hX L k ind j₀ q‖ ≤ 1 := by
  unfold daggerWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind.1 _).1]
  exact (hind.1 _).2

end WaveTurbulence.Flower.ProtPtw
