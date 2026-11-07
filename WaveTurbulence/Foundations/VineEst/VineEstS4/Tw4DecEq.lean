/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw3Dec

/-! # K^T twist invariance, the decoration equivalence (V5 Step 4b, step 3, part 4) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)

section
variable {d : ℕ} (ext : GNode G.tree → (Fin d → ℤ)) (ext' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
  (hext : ∀ x, ext x = ext' (twNode P x))

include hext hB hCL in
theorem cons_at {v : GBranch G.tree} (hv : v ∈ T) :
    (ext v.toNode = ext (v.child 0) - ext (v.child 1) + ext (v.child 2)) ↔
    (ext' (eB P v).toNode = ext' ((eB P v).child 0) - ext' ((eB P v).child 1) + ext' ((eB P v).child 2)) := by
  by_cases hl : v = P.lower
  · subst hl
    exact cons_lower_iff P ext ext' hext
  · have a0 : ext v.toNode = ext' (eB P v).toNode := (hext _).trans (congrArg ext' (twNode_branch P v hl))
    have a1 : ∀ i : Fin 3, ext (v.child i) = ext' ((eB P v).child i) := fun i =>
      (hext _).trans (congrArg ext' (twNode_child P hB hCL hv hl i))
    rw [a0, a1 0, a1 1, a1 2]

include hext hB hCL R' in
theorem leaf_at {l : GLeaf G.tree} (hl : Mole.IsInternalLeaf G T l) :
    (ext l.toNode = ext (G.pair l).toNode) ↔
    (ext' (eL P l).toNode = ext' ((unitTwistGarden G P).pair (eL P l)).toNode) := by
  have h1 : l ≠ P.retained := fun h => not_internal_retained P hB hCL (h ▸ hl)
  have h2 : l ≠ G.pair P.retained := fun h => not_internal_pair P hB hCL (h ▸ hl)
  have h3 : G.pair l ≠ P.retained := fun h => h2 (by rw [← h, G.pair_pair])
  have a0 : ext l.toNode = ext' (eL P l).toNode := (hext _).trans (congrArg ext' (twNode_leaf P l h1))
  have a1 : ext (G.pair l).toNode = ext' (eL P (G.pair l)).toNode :=
    (hext _).trans (congrArg ext' (twNode_leaf P _ h3))
  have a2 : eL P (G.pair l) = (unitTwistGarden G P).pair (eL P l) := (unitTwistGarden_pair G P l).symm
  rw [a0, a1, a2]

end

variable {d : ℕ} (L : ℝ) (base : Mom d) (e f g h : Mom d)

include hB hCL in
theorem dec_iff (zz : ↥(clLocalSupport R') → (Fin d → ℤ)) :
    ((∀ v ∈ twistedAtoms G P T, clExtendIndices R' zz v.toNode = clExtendIndices R' zz (v.child 0) -
        clExtendIndices R' zz (v.child 1) + clExtendIndices R' zz (v.child 2)) ∧
      (∀ l, Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P T) l →
        clExtendIndices R' zz l.toNode = clExtendIndices R' zz ((unitTwistGarden G P).pair l).toNode) ∧
      ∀ j, base + latticePoint L (clExtendIndices R' zz (clBoundaryNodes R' j)) = ![e, f, g, h] j) ↔
    ((∀ v ∈ T, clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) v.toNode =
        clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) (v.child 0) -
        clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) (v.child 1) +
        clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) (v.child 2)) ∧
      (∀ l, Mole.IsInternalLeaf G T l →
        clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) l.toNode =
          clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) (G.pair l).toNode) ∧
      ∀ j, base + latticePoint L (clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y))
        (clBoundaryNodes R j)) = ![f, e, g, h] j) := by
  set ext := clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) with hext_def
  set ext' := clExtendIndices R' zz with hext'_def
  have hext : ∀ x, ext x = ext' (twNode P x) := fun x => ext_comp P hB hCL R R' zz x
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro H v hv
      exact (cons_at P hB hCL ext ext' hext hv).mpr (H _ ((mem_twistedAtoms G P T v).mpr hv))
    · intro H v' hv'
      obtain ⟨v, rfl⟩ := (eB P).surjective v'
      exact (cons_at P hB hCL ext ext' hext ((mem_twistedAtoms G P T v).mp hv')).mp (H v ((mem_twistedAtoms G P T v).mp hv'))
  · constructor
    · intro H l hl
      have hl' := (internal_iff P hB hCL R' l).mp hl
      exact (leaf_at P hB hCL R' ext ext' hext hl).mpr (H _ hl')
    · intro H l' hl'
      obtain ⟨l, rfl⟩ := (eL P).surjective l'
      have hl := (internal_iff P hB hCL R' l).mpr hl'
      exact (leaf_at P hB hCL R' ext ext' hext hl).mp (H l hl)
  · have hb : ∀ j, ext (clBoundaryNodes R j) = ext' (clBoundaryNodes R' (Equiv.swap (0 : Fin 4) 1 j)) :=
      fun j => (hext _).trans (congrArg ext' (tw_bd P hB hCL R R' j))
    have hv : ∀ j, ![f, e, g, h] j = ![e, f, g, h] (Equiv.swap (0 : Fin 4) 1 j) := by
      intro j; fin_cases j <;> rfl
    constructor
    · intro H j
      rw [hb j, hv j]
      exact H _
    · intro H j'
      have := H (Equiv.swap (0 : Fin 4) 1 j')
      rw [hb, Equiv.swap_apply_self, hv] at this
      rw [Equiv.swap_apply_self] at this
      exact this

@[expose] noncomputable def decEquiv :
    CLLocalDecoration R' L base ![e, f, g, h] ≃ CLLocalDecoration R L base ![f, e, g, h] :=
  Equiv.subtypeEquiv (Equiv.arrowCongr (suppEquiv P hB hCL R R').symm (Equiv.refl _))
    (fun zz => dec_iff P hB hCL R R' L base e f g h zz)

include hB hCL in
theorem decEquiv_ext (κ : CLLocalDecoration R' L base ![e, f, g, h]) (x : GNode G.tree) :
    clExtendIndices R (decEquiv P hB hCL R R' L base e f g h κ).1 x = clExtendIndices R' κ.1 (twNode P x) :=
  ext_comp P hB hCL R R' κ.1 x

section Factors
variable {d : ℕ} (ext : GNode G.tree → (Fin d → ℤ)) (ext' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
  (hext : ∀ x, ext x = ext' (twNode P x))

include hext hB hCL in
theorem eps_at {v : GBranch G.tree} (hv : v ∈ T)
    (hcons : ext P.lower.toNode = ext (P.lower.child 0) - ext (P.lower.child 1) + ext (P.lower.child 2)) :
    epsBranch ext' (eB P v) = epsBranch ext v := by
  by_cases hl : v = P.lower
  · subst hl
    exact eps_lower P ext ext' hext hcons
  · have a1 : ∀ i : Fin 3, ext (v.child i) = ext' ((eB P v).child i) := fun i =>
      (hext _).trans (congrArg ext' (twNode_child P hB hCL hv hl i))
    unfold epsBranch
    rw [a1 0, a1 1, a1 2]

end Factors

section Phase
variable {d : ℕ} (k : GNode G.tree → Mom d) (k' : GNode (unitTwistGarden G P).tree → Mom d)
  (hk : ∀ x, k x = k' (twNode P x))

include hk hB hCL in
theorem sign_omega_at {v : GBranch G.tree} (hv : v ∈ T) :
    (((unitTwistGarden G P).sign (eB P v).toNode : ℤˣ) : ℤ) * omegaNode (unitTwistGarden G P) k' (eB P v) =
      ((G.sign v.toNode : ℤˣ) : ℤ) * omegaNode G k v := by
  have hs := coreBranchEquiv_sign G P v
  by_cases hl : v = P.lower
  · subst hl
    have ho : omegaNode (unitTwistGarden G P) k' (eB P P.lower) = -omegaNode G k P.lower := omega_lower P k k' hk
    have hs' : (unitTwistGarden G P).sign (eB P P.lower).toNode = -G.sign P.lower.toNode := by
      rw [show (eB P P.lower).toNode = (coreBranchEquiv G P P.lower).toNode from rfl, hs, if_pos rfl]
    rw [hs', ho]
    push_cast
    simp
  · have a1 : ∀ i : Fin 3, k (v.child i) = k' ((eB P v).child i) := fun i =>
      (hk _).trans (congrArg k' (twNode_child P hB hCL hv hl i))
    have a0 : k v.toNode = k' (eB P v).toNode := (hk _).trans (congrArg k' (twNode_branch P v hl))
    have hs' : (unitTwistGarden G P).sign (eB P v).toNode = G.sign v.toNode := by
      rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, hs, ite_eq_right hl]
    rw [hs']
    congr 1
    unfold omegaNode
    rw [a1 0, a1 1, a1 2, a0]

end Phase

theorem phaseAtom_congr (L γ δ : ℝ) (ζ ζ' : ℤˣ) (Ω Ω' t : ℝ) (h : ((ζ' : ℤ) : ℝ) * Ω' = ((ζ : ℤ) : ℝ) * Ω) :
    phaseAtom L γ δ ζ' Ω' t = phaseAtom L γ δ ζ Ω t := by
  have h2 : Real.pi * ((ζ' : ℤ) : ℝ) * δ * L ^ (2 * γ) * Ω' * t =
      Real.pi * ((ζ : ℤ) : ℝ) * δ * L ^ (2 * γ) * Ω * t := by
    calc _ = Real.pi * δ * L ^ (2 * γ) * t * (((ζ' : ℤ) : ℝ) * Ω') := by ring
      _ = Real.pi * δ * L ^ (2 * γ) * t * (((ζ : ℤ) : ℝ) * Ω) := by rw [h]
      _ = _ := by ring
  unfold phaseAtom
  rw [h2]

end WaveTurbulence.VineEstS4
