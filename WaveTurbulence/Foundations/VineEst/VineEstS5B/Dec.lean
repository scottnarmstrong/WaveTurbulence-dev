/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Geom

/-! # V5 Step 4d-B: the extended decorations of `S` under a twist at its lower joint

`extEquiv : ExtS RS L base β0 β1 ≃ ExtS RS' L base β0 β1`, `x ↦ twistNodeLabels G P x`: the lower joint and the retained
leaf exchange their labels (TARGET `twistexplain` (d)), both leaves of the exceptional pair receive the old lower label,
and every other label (in particular the child labels of every atom `≠ P.lower`, also the atoms `u₃, u₄` whose child
slots are exchanged by the twist) is unchanged.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

/-- Labels agree on the exceptional pair. -/
@[expose] def PairedAt (P : CorePlacement G) {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) : Prop :=
  x P.retained.toNode = x (G.pair P.retained).toNode

theorem switched_retained {E : Type*} (κ : GNode G.tree → E) :
    switchedOldLabels G P κ P.retained.toNode = κ P.lower.toNode := by
  have : P.retained.toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower P.retained).symm
  simp [switchedOldLabels, this]

theorem switched_partner {E : Type*} (κ : GNode G.tree → E) :
    switchedOldLabels G P κ (G.pair P.retained).toNode = κ P.lower.toNode := by
  have : (G.pair P.retained).toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower _).symm
  simp [switchedOldLabels, this]

theorem switched_other {E : Type*} (κ : GNode G.tree → E) {n : GNode G.tree} (h1 : n ≠ P.lower.toNode)
    (h2 : n ≠ P.retained.toNode) (h3 : n ≠ (G.pair P.retained).toNode) :
    switchedOldLabels G P κ n = κ n := by
  simp [switchedOldLabels, h1, h2, h3]

theorem twist_untwist_local {E : Type*} (η : GNode (unitTwistGarden G P).tree → E)
    (hη : η (naiveNodeEquiv G P P.retained.toNode) = η (naiveNodeEquiv G P (G.pair P.retained).toNode)) :
    twistNodeLabels G P (untwistNodeLabels G P η) = η := by
  funext n
  unfold twistNodeLabels untwistNodeLabels
  rw [switchedOldLabels_involutive G P _ hη]
  rw [Equiv.apply_symm_apply]

theorem untwist_paired {E : Type*} (η : GNode (unitTwistGarden G P).tree → E) :
    untwistNodeLabels G P η P.retained.toNode = untwistNodeLabels G P η (G.pair P.retained).toNode := by
  unfold untwistNodeLabels
  rw [switched_retained, switched_partner]

namespace STw
include h

theorem retained_mem_splitA : P.retained.toNode ∈ splitA RS := Finset.mem_union_left _ h.retained_real
theorem partner_mem_splitA : (G.pair P.retained).toNode ∈ splitA RS := Finset.mem_union_left _ h.partner_real
theorem lower_mem_splitA : P.lower.toNode ∈ splitA RS := Finset.mem_union_left _ h.lower_real

theorem switched_eq_of_notMem {E : Type*} (κ : GNode G.tree → E) {n : GNode G.tree} (hn : n ∉ splitA RS) :
    switchedOldLabels G P κ n = κ n :=
  switched_other κ (fun e => hn (e ▸ h.lower_mem_splitA)) (fun e => hn (e ▸ h.retained_mem_splitA))
    (fun e => hn (e ▸ h.partner_mem_splitA))

theorem internal_iff (l : GLeaf G.tree) :
    Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) (eL P l) ↔ Mole.IsInternalLeaf G S l := by
  by_cases hr1 : l = P.retained
  · subst hr1
    exact iff_of_true h.retained_internal' h.retained_internal
  by_cases hr2 : l = G.pair P.retained
  · subst hr2
    refine iff_of_true ?_ h.partner_internal
    have := h.partner_internal'
    change Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
    rw [unitTwistGarden_pair] at this
    exact this
  · exact ordinary_internal_iff G P l hr1 hr2

section Dec
variable {d : ℕ} (L : ℝ) (base : Mom d) (β0 β1 : Mom d)

theorem free_zero_iff (x : GNode G.tree → (Fin d → ℤ)) :
    (∀ y, y ∉ splitA RS → x y = 0) ↔
      (∀ y', y' ∉ splitA RS' → twistNodeLabels G P x y' = 0) := by
  constructor
  · intro H y' hy'
    obtain ⟨y, rfl⟩ := (naiveNodeEquiv G P).surjective y'
    have hy : y ∉ splitA RS := fun hh => hy' ((h.splitA_iff y).mp hh)
    rw [twistNodeLabels_naive, h.switched_eq_of_notMem x hy]
    exact H y hy
  · intro H y hy
    have hy' : naiveNodeEquiv G P y ∉ splitA RS' := fun hh => hy ((h.splitA_iff y).mpr hh)
    have := H _ hy'
    rwa [twistNodeLabels_naive, h.switched_eq_of_notMem x hy] at this

theorem cons_iff (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) :
    consOn (S.erase b) x ↔ consOn ((twistedAtoms G P S).erase (eB P b)) (twistNodeLabels G P x) := by
  have rel : ∀ v : GBranch G.tree, v ≠ P.lower →
      (twistNodeLabels G P x (eB P v).toNode = x v.toNode ∧
      twistNodeLabels G P x ((eB P v).child 0) = x (v.child 0) ∧
      twistNodeLabels G P x ((eB P v).child 1) = x (v.child 1) ∧
      twistNodeLabels G P x ((eB P v).child 2) = x (v.child 2)) := fun v hvl =>
    ⟨twistNodeLabels_branch G P x v hvl, twistNodeLabels_other_child G P x hp v hvl 0,
      twistNodeLabels_other_child G P x hp v hvl 1, twistNodeLabels_other_child G P x hp v hvl 2⟩
  constructor
  · intro H v' hv'
    obtain ⟨v, rfl⟩ := (eB P).surjective v'
    have hv : v ∈ S.erase b := (mem_erase_twisted P v).mp hv'
    have hvl : v ≠ P.lower := h.lower ▸ (Finset.mem_erase.mp hv).1
    obtain ⟨r0, r1, r2, r3⟩ := rel v hvl
    rw [r0, r1, r2, r3]
    exact H v hv
  · intro H v hv
    have hv' := (mem_erase_twisted P (b := b) v).mpr hv
    have hvl : v ≠ P.lower := h.lower ▸ (Finset.mem_erase.mp hv).1
    obtain ⟨r0, r1, r2, r3⟩ := rel v hvl
    have := H (eB P v) hv'
    rw [r0, r1, r2, r3] at this
    exact this

theorem leaf_iff (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) :
    leafOn G S x ↔ leafOn (unitTwistGarden G P) (twistedAtoms G P S) (twistNodeLabels G P x) := by
  have key : ∀ l : GLeaf G.tree, (l = P.retained ∨ l = G.pair P.retained) ↔
      (G.pair l = P.retained ∨ G.pair l = G.pair P.retained) := by
    intro l
    constructor
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (G.pair_pair _)
    · rintro (hh | hh)
      · refine Or.inr ?_
        have := congrArg G.pair hh
        rwa [G.pair_pair] at this
      · refine Or.inl ?_
        have := congrArg G.pair hh
        rwa [G.pair_pair, G.pair_pair] at this
  have hval : ∀ l : GLeaf G.tree, twistNodeLabels G P x ((unitTwistGarden G P).pair (eL P l)).toNode =
      (if G.pair l = P.retained ∨ G.pair l = G.pair P.retained then x P.lower.toNode else x (G.pair l).toNode) := by
    intro l
    have e : (unitTwistGarden G P).pair (eL P l) = eL P (G.pair l) := unitTwistGarden_pair G P l
    rw [e]
    exact twistNodeLabels_leaf G P x (G.pair l)
  constructor
  · intro H l' hl'
    obtain ⟨l, rfl⟩ := (eL P).surjective l'
    have hl := (h.internal_iff l).mp hl'
    have t0 : twistNodeLabels G P x (eL P l).toNode =
        if l = P.retained ∨ l = G.pair P.retained then x P.lower.toNode else x l.toNode :=
      twistNodeLabels_leaf G P x l
    rw [hval l, t0]
    by_cases hc : l = P.retained ∨ l = G.pair P.retained
    · rw [if_pos hc, if_pos ((key l).mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc ((key l).mpr hh))]
      exact H l hl
  · intro H l hl
    have hl' := (h.internal_iff l).mpr hl
    have := H (eL P l) hl'
    have t0 : twistNodeLabels G P x (eL P l).toNode =
        if l = P.retained ∨ l = G.pair P.retained then x P.lower.toNode else x l.toNode :=
      twistNodeLabels_leaf G P x l
    rw [hval l, t0] at this
    by_cases hc : l = P.retained ∨ l = G.pair P.retained
    · rcases hc with rfl | rfl
      · exact hp
      · have hpp : x (G.pair (G.pair P.retained)).toNode = x (G.pair P.retained).toNode := by
          rw [G.pair_pair]; exact hp
        exact hpp.symm
    · rw [if_neg hc, if_neg (fun hh => hc ((key l).mpr hh))] at this
      exact this

theorem bd_iff (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) :
    BdS RS L base β0 β1 x ↔ BdS RS' L base β0 β1 (twistNodeLabels G P x) := by
  have hal : a ≠ P.lower := h.a_ne_lower
  have e0 : twistNodeLabels G P x (eB P a).toNode = x a.toNode := twistNodeLabels_branch G P x a hal
  have e1 : twistNodeLabels G P x ((eB P a).child RS'.excluded) = x (a.child RS.excluded) := by
    rw [h.excluded_eq]
    exact twistNodeLabels_other_child G P x hp a hal _
  unfold BdS
  rw [e0, e1]

theorem ext_iff (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x) :
    (FreeS RS x ∧ BdS RS L base β0 β1 x) ↔
      (FreeS RS' (twistNodeLabels G P x) ∧ BdS RS' L base β0 β1 (twistNodeLabels G P x)) := by
  unfold FreeS
  rw [h.free_zero_iff x, h.cons_iff x hp, h.leaf_iff x hp, h.bd_iff L base β0 β1 x hp]

end Dec

theorem pairedAt_ext {d : ℕ} {L : ℝ} {base β0 β1 : Mom d} (x : ExtS RS L base β0 β1) : PairedAt P x.1 :=
  x.2.1.2.2 P.retained h.retained_internal

theorem pulled_paired {d : ℕ} {L : ℝ} {base β0 β1 : Mom d} (x' : ExtS RS' L base β0 β1) :
    x'.1 (naiveNodeEquiv G P P.retained.toNode) = x'.1 (naiveNodeEquiv G P (G.pair P.retained).toNode) := by
  have := x'.2.1.2.2 (eL P P.retained) h.retained_internal'
  have e : (unitTwistGarden G P).pair (eL P P.retained) = eL P (G.pair P.retained) :=
    unitTwistGarden_pair G P P.retained
  rw [e] at this
  rw [naiveNodeEquiv_leaf, naiveNodeEquiv_leaf]
  exact this

/-- **The extended decorations of the upper block correspond under the twist** (the lower joint and the retained leaf
exchange labels). -/
@[expose] noncomputable def extEquiv {d : ℕ} (L : ℝ) (base β0 β1 : Mom d) :
    ExtS RS L base β0 β1 ≃ ExtS RS' L base β0 β1 where
  toFun x := ⟨twistNodeLabels G P x.1, (h.ext_iff L base β0 β1 x.1 (h.pairedAt_ext x)).mp x.2⟩
  invFun x' := ⟨untwistNodeLabels G P x'.1, by
    have e := twist_untwist_local x'.1 (h.pulled_paired x')
    refine (h.ext_iff L base β0 β1 _ (untwist_paired x'.1)).mpr ?_
    rw [e]
    exact x'.2⟩
  left_inv x := Subtype.ext (untwist_twistNodeLabels G P x.1 (h.pairedAt_ext x))
  right_inv x' := Subtype.ext (twist_untwist_local x'.1 (h.pulled_paired x'))

theorem extEquiv_val {d : ℕ} (L : ℝ) (base β0 β1 : Mom d) (x : ExtS RS L base β0 β1) :
    (h.extEquiv L base β0 β1 x).1 = twistNodeLabels G P x.1 := rfl

end STw


end WaveTurbulence.VineEstS5B
