/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Dec
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Frame

/-! # V5 Step 4d-B: the factors of the S-side under a twist at the lower joint (part 1)

Order, `ζ_S` (the twist changes the sign of the lower joint, hence `ζ_S' = -ζ_S`), epsilon and phase factors of the atoms
`S.erase b` (the labels at all children of every atom `≠ P.lower` are unchanged by the label switch), and the parent
clocks of the nodes other than `lower`, `retained`, `partner`.
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

namespace STw

include h in
theorem zeta : clLocalZeta RS' = - clLocalZeta RS := by
  classical
  unfold clLocalZeta
  have hlow : P.lower ∈ clInteriorBranches RS := by
    unfold clInteriorBranches
    exact Finset.mem_erase.mpr ⟨fun he => h.a_ne_lower he.symm, h.lower_mem⟩
  have e1 : ∏ v' ∈ clInteriorBranches RS', Complex.I * (((unitTwistGarden G P).sign v'.toNode : ℤ) : ℂ) =
      ∏ v ∈ clInteriorBranches RS, Complex.I * (((unitTwistGarden G P).sign (eB P v).toNode : ℤ) : ℂ) :=
    (Finset.prod_equiv (eB P) (fun v => (mem_interior_rigid P RS RS' v).symm) (fun v _ => rfl)).symm
  rw [e1, ← Finset.mul_prod_erase _ _ hlow, ← Finset.mul_prod_erase _ _ hlow]
  have hs : (unitTwistGarden G P).sign (eB P P.lower).toNode = -G.sign P.lower.toNode := by
    rw [show (eB P P.lower).toNode = (coreBranchEquiv G P P.lower).toNode from rfl, coreBranchEquiv_sign, if_pos rfl]
  have hprod : ∏ v ∈ (clInteriorBranches RS).erase P.lower,
      Complex.I * (((unitTwistGarden G P).sign (eB P v).toNode : ℤ) : ℂ) =
      ∏ v ∈ (clInteriorBranches RS).erase P.lower, Complex.I * ((G.sign v.toNode : ℤ) : ℂ) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvl : v ≠ P.lower := (Finset.mem_erase.mp hv).1
    rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, coreBranchEquiv_sign, if_neg hvl]
  rw [hprod, hs]
  simp only [Units.val_neg, Int.cast_neg]
  ring

section Labels
variable {d : ℕ} (x : GNode G.tree → (Fin d → ℤ))

theorem branch_rel {v : GBranch G.tree} (hvl : v ≠ P.lower) :
    twistNodeLabels G P x (eB P v).toNode = x v.toNode := twistNodeLabels_branch G P x v hvl

theorem child_rel (hp : PairedAt P x) {v : GBranch G.tree} (hvl : v ≠ P.lower) (i : Fin 3) :
    twistNodeLabels G P x ((eB P v).child i) = x (v.child i) := twistNodeLabels_other_child G P x hp v hvl i

include h in
theorem ne_lower_of_mem_erase {v : GBranch G.tree} (hv : v ∈ S.erase b) : v ≠ P.lower :=
  h.lower ▸ (Finset.mem_erase.mp hv).1

include h in
theorem eps (hp : PairedAt P x) :
    clRegionalEpsilon (unitTwistGarden G P) ((twistedAtoms G P S).erase (eB P b)) (twistNodeLabels G P x) =
      clRegionalEpsilon G (S.erase b) x := by
  unfold clRegionalEpsilon
  refine (Finset.prod_equiv (eB P) (fun v => (mem_erase_twisted P v).symm) (fun v hv => ?_)).symm
  have hvl := h.ne_lower_of_mem_erase hv
  unfold epsBranch
  rw [child_rel x hp hvl 0, child_rel x hp hvl 1, child_rel x hp hvl 2]

include h in
theorem omega_eq (L : ℝ) (base : Mom d) (hp : PairedAt P x) {v : GBranch G.tree} (hv : v ∈ S.erase b) :
    omegaNode (unitTwistGarden G P) (cosetDecoration (unitTwistGarden G P) L base (twistNodeLabels G P x)) (eB P v) =
      omegaNode G (cosetDecoration G L base x) v := by
  have hvl := h.ne_lower_of_mem_erase hv
  unfold omegaNode cosetDecoration
  rw [child_rel x hp hvl 0, child_rel x hp hvl 1, child_rel x hp hvl 2, branch_rel x hvl]

include h in
theorem phase (L γ δ : ℝ) (base : Mom d) (hp : PairedAt P x) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S.erase b, u' (eB P v) = u v) :
    clRegionalPhase (unitTwistGarden G P) ((twistedAtoms G P S).erase (eB P b)) L γ δ
        (cosetDecoration (unitTwistGarden G P) L base (twistNodeLabels G P x)) u' =
      clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base x) u := by
  unfold clRegionalPhase
  refine (Finset.prod_equiv (eB P) (fun v => (mem_erase_twisted P v).symm) (fun v hv => ?_)).symm
  have hvl := h.ne_lower_of_mem_erase hv
  have hs : (unitTwistGarden G P).sign (eB P v).toNode = G.sign v.toNode := by
    rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, coreBranchEquiv_sign, if_neg hvl]
  rw [hu v hv, hs, h.omega_eq x L base hp hv]

end Labels

section Clock

include h in
theorem parentClock_naive {x : GNode G.tree} (hx : x ∈ clRealizationNodes G S) (hxa : x ≠ a.toNode)
    (hxl : x ≠ P.lower.toNode) (hxp : x ≠ (G.pair P.retained).toNode) (t0 : ℝ)
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) :
    parentClock t0 u' (naiveNodeEquiv G P x) = parentClock t0 u x := by
  obtain ⟨v, i, hv, hxv, hn⟩ : ∃ (v : GBranch G.tree) (i : Fin 3), v ∈ S ∧ x = v.child i ∧
      naiveNodeEquiv G P x = (eB P v).child (exchangeChildSlot P.lower.1 P.keep v.1 i) := by
    obtain ⟨hn, hp⟩ := cl_realization_parent h.block RS x hx hxa
    have hxv : x = (x.parent hn).child (x.1.2.getLast hn) := (Mole.parent_child_eq_node x hn).symm
    exact ⟨x.parent hn, x.1.2.getLast hn, hp, hxv, naiveNodeEquiv_child G P hxv hxl hxp⟩
  rw [hn, hxv, parentClock_child, parentClock_child]
  exact hu v hv

include h in
theorem domF_iff (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ)
    (hl : ∀ v ∈ S.erase a, lay' (eB P v) = lay v) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v) :
    DomF lay' (twistedAtoms G P S) (eB P a) (eB P b) u' ↔ DomF lay S a b u := by
  have hua : u' (eB P a) = u a := hu a h.block.2.1
  have key : ∀ v ∈ S.erase a, v ≠ b → parentClock (u' (eB P a)) u' (eB P v).toNode = parentClock (u a) u v.toNode := by
    intro v hv hvb
    have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
    have hvl : v ≠ P.lower := h.lower ▸ hvb
    rw [hua, show (eB P v).toNode = naiveNodeEquiv G P v.toNode from (naiveNodeEquiv_branch G P v).symm]
    exact h.parentClock_naive ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun he => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective he))
      (fun he => hvl (Mole.branch_toNode_injective he)) (Mole.branch_toNode_ne_leaf v _) (u a) u' u hu
  unfold DomF
  constructor
  · intro H v hv
    have := H (eB P v) ((mem_erase_twisted P (b := a) v).mpr hv)
    rw [hl v hv, hu v (Finset.mem_of_mem_erase hv)] at this
    refine ⟨this.1, this.2.1, this.2.2.1, fun hvb => ?_⟩
    have h4 := this.2.2.2 (fun he => hvb ((eB P).injective he))
    rwa [key v hv hvb] at h4
  · intro H v' hv'
    obtain ⟨v, rfl⟩ := (eB P).surjective v'
    have hv : v ∈ S.erase a := (mem_erase_twisted P (b := a) v).mp hv'
    have := H v hv
    rw [hl v hv, hu v (Finset.mem_of_mem_erase hv)]
    refine ⟨this.1, this.2.1, this.2.2.1, fun hvb => ?_⟩
    have hvb' : v ≠ b := fun he => hvb (he ▸ rfl)
    rw [key v hv hvb']
    exact this.2.2.2 hvb'

end Clock

end STw

end WaveTurbulence.VineEstS5B
