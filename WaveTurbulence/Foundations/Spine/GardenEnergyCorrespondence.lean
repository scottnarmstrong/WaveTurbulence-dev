/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.GardenLatticeCorrespondence
public import WaveTurbulence.Foundations.Spine.GardenBoundarySource
import Mathlib.Tactic

/-! # TARGET `molegammav`: quadratic energies under the actual correspondence -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w d : ℕ} (G : Garden w)

/-- The signed four-node quadratic sum is minus the tree resonance times
its actual node sign, with no conservation premise needed. -/
theorem slotSum_energy (κ : GNode G.tree → Mom d) (v : GBranch G.tree) :
    slotSum G (fun a => ‖κ a‖^2) v = -((G.sign v.toNode : ℤ):ℝ)*omegaNode G κ v := by
  unfold slotSum
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  have h0 : slotNode G v 0 = v.toNode := rfl
  have h1 : slotNode G v 1 = v.child 0 := rfl
  have h2 : slotNode G v 2 = v.child 1 := rfl
  have h3 : slotNode G v 3 = v.child 2 := rfl
  rcases Int.units_eq_one_or (G.sign v.toNode) with hs | hs <;>
    norm_num [slotWeight,hs,h0,h1,h2,h3,omegaNode,resFactor] <;> ring

/-- TARGET `molegammav` for the exact B2 lattice decoration and the actual
extended garden decoration, including all root boundary energy terms. -/
theorem garden_molecule_Gamma (hP : G.IsPlain) (n : Fin w → Mom d)
    (hn : RootPairCompatible G n) (L : ℝ) (base : Mom d)
    (k : GardenDart G → (Fin d → ℤ))
    (hk : G.molecule.IsDecoration L base (gardenSource G hP n) k)
    (v : GBranch G.tree) :
    let κ := extendLabels G hP n (Molecule.kvec L base k)
    G.molecule.Gamma L base k v = -((G.sign v.toNode : ℤ):ℝ)*omegaNode G κ v +
      gardenSource G hP (fun i => ‖n i‖^2) v := by
  let κ := extendLabels G hP n (Molecule.kvec L base k)
  obtain ⟨hκ,hr,hrec⟩ := gardenDecoration_of_molecule G hP n hn L base k hk
  let f : GNode G.tree → ℝ := fun a => ‖κ a‖^2
  let ke : GardenDart G → ℝ := fun x => ‖Molecule.kvec L base k x‖^2
  have hkm : ∀ x, ke (G.molecule.mate x) = ke x := by
    intro x
    dsimp only [ke,Molecule.kvec]
    rw [hk.1 x]
  have hf : ∀ l : GLeaf G.tree, f l.toNode = f (G.pair l).toNode :=
    fun l => congrArg (fun y : Mom d => ‖y‖^2) (hκ.2 l)
  have hfr : ∀ i, f (GNode.root G.tree i) = ‖n i‖^2 :=
    fun i => congrArg (fun y : Mom d => ‖y‖^2) (hr i)
  have hrestrict : restrictLabels G f = ke := by
    funext x
    exact congrArg (fun y : Mom d => ‖y‖^2) (congrFun hrec x)
  have hext : extendLabels G hP (fun i => ‖n i‖^2) ke = f := by
    rw [← hrestrict]
    exact extend_restrictLabels G hP _ f hfr hf
  have hs := slotSum_extension G hP (fun i => ‖n i‖^2) ke hkm v
  rw [hext,slotSum_energy] at hs
  simp only [smul_eq_mul] at hs
  change G.molecule.Gamma L base k v = _
  change -((G.sign v.toNode : ℤ):ℝ)*omegaNode G κ v =
    G.molecule.Gamma L base k v - gardenSource G hP (fun i => ‖n i‖^2) v at hs
  linarith only [hs]

end WaveTurbulence.Mole
