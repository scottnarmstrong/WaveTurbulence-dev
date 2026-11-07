/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproStep1
import Mathlib.Tactic

/-!
# S4-DISJ goal 3: a vc-shaped object excludes the `eraseBond` disjunct of `step1_vc_shape`

An ordinary (VC-shaped) object `P` is a block of the molecule `M`, so its joints have `M`-internal degree 2. If `P.atoms` were a
double chain or a type-V vine of the adjoint molecule `eraseBond M e` with `e` a bond joining the joints, the joint would have
`M`-internal degree `>= 3`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A double chain has at least internal degree two at its first joint. -/
theorem doubleChain_two_le_degIn {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.DoubleChain M S a b n) : 2 ≤ M.degIn S a := by
  induction h with
  | single h => exact (Mole.block_joint_degrees M h.1).1.ge
  | @append S T a b c n _ _ _ _ ih => exact ih.trans (Mole.degIn_mono M Finset.subset_union_left a)

/-- If `e` joins the two joints `a ≠ b` of a block `S`, then the adjoint `eraseBond M e` has internal degree `<= 1`
at `a` (the block has `M`-degree 2). -/
theorem eraseBond_degIn_lt_two_of_block {M : Molecule V D} {S : Finset V} {a b : V} {e : D}
    (hB : M.IsBlock S a b) (he : M.ends e = s(a, b)) : (Mole.eraseBond M e).degIn S a < 2 := by
  have hne : a ≠ b := hB.2.2.2.1
  have hd := (Mole.block_joint_degrees M hB).1
  have hend := Sym2.eq_iff.mp he
  change (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) at hend
  rcases hend with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have h1 := Mole.eraseBond_degIn_endpoint M e ha hb hne hB.2.1 hB.2.2.1
    omega
  · have h1 := Mole.eraseBond_degIn_endpoint M (M.mate e) hb (by rw [M.mate_mate]; exact ha) hne
      hB.2.1 hB.2.2.1
    rw [Mole.eraseBond_mate_degIn] at h1
    omega

/-- **S4-DISJ goal 3.** For an object of ordinary (VC) shape the `eraseBond` disjunct of `step1_vc_shape` is impossible:
the SG object outside `C_1` and hinge-free is a single vine of type V, or one or two double bonds, in `M` itself. -/
theorem step1_vc_shape' {w d : ℕ} (G : Garden w) (C : SubproChoices G) (L γ η : ℝ) (base : Mom d)
    (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ))
    (hs : SubproSupportA G C L γ η base kFix κ)
    (c : GBranch G.tree → Mom d) (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (P : Object G.molecule) (hP : P.HasGapKind L γ η base κ .SG)
    (hout : ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) (hdis : Disjoint P.atoms C.hinges)
    (hvc : ∃ h, P.shape = VineLikeObject.vc h) :
    Vine.DoubleChain G.molecule P.atoms P.upper P.lower 1 ∨ Vine.DoubleChain G.molecule P.atoms P.upper P.lower 2 ∨
      G.molecule.IsVine .V P.atoms P.upper P.lower := by
  rcases step1_vc_shape G C L γ η base kFix κ hs c hκ hc P hP hout hdis hvc with h | h | h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have hB := object_vc_block P hvc
    have hlt := eraseBond_degIn_lt_two_of_block hB he
    rcases h with h | h
    · exact absurd (doubleChain_two_le_degIn h) (by omega)
    · exact absurd (Mole.block_joint_degrees _ h.1).1 (by omega)

end WaveTurbulence.Subpro
