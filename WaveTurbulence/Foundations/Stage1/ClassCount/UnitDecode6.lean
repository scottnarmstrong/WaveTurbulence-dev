/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
import Mathlib.Tactic

/-!
# CLASSCOUNT: every unit of `unitBlocks G σ` is a unit code (UL)

`unit_decode`: for a unit `u ∈ unitBlocks G σ` there are ingredient codes `cs` and a labelling `lab` of the atoms of `u`
by `0 … unitWeight cs`, injective on `u.atoms`, whose arcs (the oriented bonds of `G` inside `u.atoms`) are `unitArcs cs`.
Cases: a whole-group unit (`whole_vc`: the group is a VC), or a skip-run `L₀`/`R₀` of an SG group around a skipped
ingredient (`SkipData`; the runs are chains by `ingredient_runs`, identified with `L₀`, `R₀` by `left_run_eq`,
`right_run_eq`); for an HVC the chain lives in `eraseBond G.molecule e`, and `groupArcs_erase` transfers the arcs.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.RedSplice WaveTurbulence.Stage1

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem skel_b_not_L0 {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule V D'} {S A L0 R0 : Finset V}
    {a b x y : V} (sk : SkelDecomp N S A L0 R0 a b x y) : b ∉ L0 := by
  intro hb
  have hxy : x ≠ y := sk.hA.2.2.2.1
  rcases sk.hR with ⟨-, hyb⟩ | ⟨-, hRB, hRI⟩
  · have : b ∈ L0 ∩ A := by
      refine Finset.mem_inter.mpr ⟨hb, ?_⟩
      rw [← hyb]; exact sk.hA.2.2.1
    rcases sk.hL with ⟨h0, -⟩ | ⟨-, -, hLI⟩
    · rw [h0] at hb; simp at hb
    · rw [hLI, Finset.mem_singleton] at this
      exact hxy (this.symm.trans hyb.symm)
  · exact Finset.disjoint_left.mp sk.hd hb hRB.2.2.1

theorem skel_a_not_R0 {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule V D'} {S A L0 R0 : Finset V}
    {a b x y : V} (sk : SkelDecomp N S A L0 R0 a b x y) : a ∉ R0 := by
  intro ha
  have hxy : x ≠ y := sk.hA.2.2.2.1
  rcases sk.hL with ⟨-, hxa⟩ | ⟨-, hLB, hLI⟩
  · have : a ∈ R0 ∩ A := by
      refine Finset.mem_inter.mpr ⟨ha, ?_⟩
      rw [← hxa]; exact sk.hA.2.1
    rcases sk.hR with ⟨h0, -⟩ | ⟨-, -, hRI⟩
    · rw [h0] at ha; simp at ha
    · rw [hRI, Finset.mem_singleton] at this
      exact hxy (hxa.trans this)
  · exact Finset.disjoint_right.mp sk.hd ha hLB.2.1


end WaveTurbulence.ClassCount
