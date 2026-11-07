/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.DecGlue
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic

/-!
# VINE-B: the `ε` factors and the phases

* `eps_split`: `ε_{I_sk} = ε̃_{I_sb} · Π_j Π_{n ∈ U_j} ε_n` (TARGET L1957 (i): `ε̃` omits exactly the hinges, the unit
  products include `u1^j`, as in V5's `clRegionalEpsilon`).
* `hinge_energy`: at a hinge, `ζ_{u1} Ω^{sb}_{u1} = Γ = ζ_{u11}|k_{u11}|² + |k_{u21}|² - |k_{u22}|² - ζ_{u1}|k_{u1}|²`
  (V5's `boundaryEnergyFromMomenta`), so the phase of `G_sb` at the hinge is the inverse of the recentering factor
  `e^{-πiδL^{2γ} t_{u1} Γ}` of (vineest1) (TARGET L1957: "exactly cancels").
* `phase_split`, `phaseProd_sb`: the phase products of `S` and of `G_sb` over the non-hinge branches agree.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.LGSpine

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem eps_split (hd : Disj blk) (κ : GNode S.tree → (Fin d → ℤ)) :
    epsDec S κ = splicedEpsilon Gsb (Φ.hinges hd) (fun y => κ (Φ.node y)) *
      ∏ j, clRegionalEpsilon S (blk j).atoms κ := by
  unfold epsDec splicedEpsilon clRegionalEpsilon
  rw [Φ.prod_split_atoms hd]
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  have hh := (Φ.not_mem_hinges hd c).mp (Finset.mem_filter.mp hc).2
  simp only [Φ.child c _ hh]

theorem omega_nonhinge (hd : Disj blk) (k : GNode S.tree → Mom d) (c : GBranch Gsb.tree)
    (hc : c ∉ Φ.hinges hd) : omegaNode Gsb (fun y => k (Φ.node y)) c = omegaNode S k (Φ.br c) := by
  have hh := (Φ.not_mem_hinges hd c).mp hc
  unfold omegaNode
  simp only [Φ.child c _ hh, Φ.br_node]

/-- The signed resonance of `G_sb` at a hinge is the boundary energy `Γ` of the unit. -/
theorem hinge_energy (hd : Disj blk) (k : GNode S.tree → Mom d) (j : J) :
    ((Gsb.sign (Φ.hinge hd j).toNode : ℤˣ) : ℤ) * omegaNode Gsb (fun y => k (Φ.node y)) (Φ.hinge hd j) =
      boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode) (k (blk j).upper.toNode)
        (k ((blk j).upper.child (regionOf (blk j)).excluded)) (k ((blk j).lower.child (regionOf (blk j)).positive))
        (k ((blk j).lower.child (regionOf (blk j)).negative)) := by
  set c := Φ.hinge hd j
  have hcj : Φ.br c = (blk j).upper := Φ.br_hinge hd j
  have hσ : Gsb.sign c.toNode = S.sign (blk j).upper.toNode := by
    rw [← Φ.sign, ← Φ.br_node, hcj]
  have hs0 : Gsb.sign (c.child 0) = Gsb.sign c.toNode := Mole.outer_child_sign Gsb c 0 (by decide)
  have hs2 : Gsb.sign (c.child 2) = Gsb.sign c.toNode := Mole.outer_child_sign Gsb c 2 (by decide)
  have hs1 : Gsb.sign (c.child 1) = -Gsb.sign c.toNode := by
    rw [Mole.child_sign_formula c 1]; rfl
  have hsum := sum_crown (blk j) (fun i => Φ.node (c.child i)) (fun i i' h => (child_inj (Φ.inj h)).2)
    (Φ.crown c j hcj) (fun x => (((S.sign x : ℤˣ) : ℤ) : ℝ) * ‖k x‖ ^ 2)
  simp only [Fin.sum_univ_three, Φ.sign, hs0, hs1, hs2, hσ] at hsum
  have he : S.sign ((blk j).upper.child (regionOf (blk j)).excluded) = S.sign (blk j).upper.toNode :=
    Mole.outer_child_sign S _ _ (regionOf (blk j)).excluded_ne_middle
  rw [he, (regionOf (blk j)).positive_sign, (regionOf (blk j)).negative_sign] at hsum
  have hc0 : Φ.node c.toNode = (blk j).upper.toNode := by rw [← Φ.br_node, hcj]
  unfold omegaNode resFactor boundaryEnergyFromMomenta
  beta_reduce
  rw [hσ, hc0]
  rcases Int.units_eq_one_or (S.sign (blk j).upper.toNode) with h | h <;>
    simp only [h, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_mul,
      neg_neg] at hsum ⊢ <;> linarith

/-- The phase of the hinge is `e^{πiδL^{2γ} t Γ}`. -/
theorem hinge_phase (hd : Disj blk) (L γ δ : ℝ) (k : GNode S.tree → Mom d) (j : J) (t : ℝ) :
    phaseAtom L γ δ (Gsb.sign (Φ.hinge hd j).toNode) (omegaNode Gsb (fun y => k (Φ.node y)) (Φ.hinge hd j)) t =
      Complex.exp ((((Real.pi * δ * L ^ (2 * γ)) * t *
        boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode) (k (blk j).upper.toNode)
          (k ((blk j).upper.child (regionOf (blk j)).excluded)) (k ((blk j).lower.child (regionOf (blk j)).positive))
          (k ((blk j).lower.child (regionOf (blk j)).negative)) : ℝ) : ℂ) * Complex.I) := by
  rw [← Φ.hinge_energy hd k j]
  unfold phaseAtom
  congr 2
  push_cast
  ring

theorem phase_split (hd : Disj blk) (L γ δ : ℝ) (k : GNode S.tree → Mom d) (τ : GBranch S.tree → ℝ) :
    phaseProd L γ δ S k τ =
      (∏ c ∈ (univ : Finset (GBranch Gsb.tree)).filter (fun c => c ∉ Φ.hinges hd),
        phaseAtom L γ δ (S.sign (Φ.br c).toNode) (omegaNode S k (Φ.br c)) (τ (Φ.br c))) *
      ∏ j, clRegionalPhase S (blk j).atoms L γ δ k τ := by
  unfold phaseProd clRegionalPhase
  rw [Φ.prod_split_atoms hd]
  rfl

theorem phaseProd_sb (hd : Disj blk) (L γ δ : ℝ) (k : GNode S.tree → Mom d) (τ : GBranch Gsb.tree → ℝ) :
    phaseProd L γ δ Gsb (fun y => k (Φ.node y)) τ =
      (∏ c ∈ (univ : Finset (GBranch Gsb.tree)).filter (fun c => c ∉ Φ.hinges hd),
        phaseAtom L γ δ (S.sign (Φ.br c).toNode) (omegaNode S k (Φ.br c)) (τ c)) *
      ∏ j, phaseAtom L γ δ (Gsb.sign (Φ.hinge hd j).toNode)
        (omegaNode Gsb (fun y => k (Φ.node y)) (Φ.hinge hd j)) (τ (Φ.hinge hd j)) := by
  unfold phaseProd
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun c => c ∈ Φ.hinges hd), mul_comm]
  have hf : (univ : Finset (GBranch Gsb.tree)).filter (fun c => c ∈ Φ.hinges hd) = Φ.hinges hd := by
    ext c; simp
  rw [hf, Φ.prod_hinges hd]
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  rw [Φ.omega_nonhinge hd k c (Finset.mem_filter.mp hc).2, Φ.br_node, Φ.sign]
  rfl

end SpliceShape

end WaveTurbulence.VineB
