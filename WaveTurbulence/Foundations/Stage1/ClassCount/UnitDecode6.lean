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

/-- A run of a skip decomposition is a unit code (in the molecule `N` of the chain). -/
theorem run_decode {D' : Type*} [Fintype D'] [DecidableEq D'] (N : Molecule V D') {S A L0 R0 : Finset V}
    {a b x y : V} {n : ℕ} (hI : ChainIngredient N S a b n A x y)
    (sk : SkelDecomp N S A L0 R0 a b x y) {P : Finset V} (hP : P = L0 ∨ P = R0) (hne : P.Nonempty) :
    ∃ cs : List IngCode, (∀ c ∈ cs, c.Wf) ∧ ∃ lab : V → ℕ, Set.InjOn lab P ∧
      P.image lab = Finset.range (unitWeight cs + 1) ∧
      groupArcs N P lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  obtain ⟨L, R, hS1, hL, hR, hd⟩ := ingredient_runs sk.mol hI sk.hSB
  rcases hP with rfl | rfl
  · -- left run
    rcases sk.hL with ⟨h0, -⟩ | ⟨hxa, hLB, hLI⟩
    · rw [h0] at hne; simp at hne
    · have hR0 : R0 = ∅ ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y}) := by
        rcases sk.hR with ⟨h, -⟩ | h
        · exact Or.inl h
        · exact Or.inr h
      have hRr : R = ∅ ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y}) := by
        rcases hR with ⟨h, -⟩ | ⟨h1, h2, ⟨m, hm⟩, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, h4⟩
      have hLl : L = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}) := by
        rcases hL with h | ⟨h1, h2, ⟨m, hm⟩, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, h4⟩
      have heq := left_run_eq N sk.mol sk.hSB sk.hA sk.hS (Or.inr ⟨hxa, hLB, hLI⟩) hR0 hS1 hLl hRr
      rcases hL with ⟨-, hxa'⟩ | ⟨-, hLB', ⟨m, hm⟩, -⟩
      · exact absurd hxa' hxa
      · rw [← heq] at hm hLB'
        obtain ⟨cs, -, hwf, lab, hinj, himg, -, -, harcs⟩ := chain_decode N sk.mol hm hLB'
        exact ⟨cs, hwf, lab, hinj, himg, harcs⟩
  · rcases sk.hR with ⟨h0, -⟩ | ⟨hyb, hRB, hRI⟩
    · rw [h0] at hne; simp at hne
    · have hL0 : L0 = ∅ ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x}) := by
        rcases sk.hL with ⟨h, -⟩ | h
        · exact Or.inl h
        · exact Or.inr h
      have hLl : L = ∅ ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}) := by
        rcases hL with ⟨h, -⟩ | ⟨h1, h2, ⟨m, hm⟩, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, h4⟩
      have hRr : R = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y}) := by
        rcases hR with h | ⟨h1, h2, ⟨m, hm⟩, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, h4⟩
      have heq := right_run_eq N sk.mol sk.hSB sk.hA sk.hS hL0 (Or.inr ⟨hyb, hRB, hRI⟩) hS1 hLl hRr
      rcases hR with ⟨-, hyb'⟩ | ⟨-, hRB', ⟨m, hm⟩, -⟩
      · exact absurd hyb' hyb
      · rw [← heq] at hm hRB'
        obtain ⟨cs, -, hwf, lab, hinj, himg, -, -, harcs⟩ := chain_decode N sk.mol hm hRB'
        exact ⟨cs, hwf, lab, hinj, himg, harcs⟩


/-- **UL**: every unit of `unitBlocks G σ` is a unit code. -/
theorem unit_decode {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    ∃ cs : List IngCode, (∀ c ∈ cs, c.Wf) ∧ ∃ lab : GBranch G.tree → ℕ, Set.InjOn lab u.atoms ∧
      u.atoms.image lab = Finset.range (unitWeight cs + 1) ∧
      groupArcs G.molecule u.atoms lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  obtain ⟨S', hSm, hσ, huU⟩ := mem_unitBlocks.mp hu
  have hne : u.atoms.Nonempty := ⟨u.upper, u.isBlock.2.1⟩
  rcases hsk : (groupUnitsOf G S').skip with _ | sk
  · have h1 := (groupUnitsOf G S').noskip_units hsk u huU
    obtain ⟨a, b, hB, n, hC⟩ := (groupUnitsOf G S').whole_vc hsk (List.ne_nil_of_mem huU)
    obtain ⟨cs, -, hwf, lab, hinj, himg, -, -, harcs⟩ :=
      chain_decode G.molecule hM (chain_of_source hC) hB
    rw [h1]; exact ⟨cs, hwf, lab, hinj, himg, harcs⟩
  · have hskip := ((groupUnitsOf G S').skip_units sk hsk).1 u huU
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have skel := sk.skelM hb
      rcases hskip with ⟨hL, -⟩ | ⟨hR, -⟩
      · exact run_decode G.molecule hI skel (P := u.atoms) (Or.inl hL) hne
      · exact run_decode G.molecule hI skel (P := u.atoms) (Or.inr hR) hne
    · obtain ⟨n, -, hI⟩ := sk.chainN e hb
      have skel := sk.skelN e hb
      have hends := (sk.blockN e hb).1
      have hends' : (G.molecule.atom e = sk.a ∧ G.molecule.atom (G.molecule.mate e) = sk.b) ∨
          (G.molecule.atom e = sk.b ∧ G.molecule.atom (G.molecule.mate e) = sk.a) := by
        have := Sym2.eq_iff.mp hends
        exact this
      rcases hskip with ⟨hL, -⟩ | ⟨hR, -⟩
      · obtain ⟨cs, hwf, lab, hinj, himg, harcs⟩ :=
          run_decode (G.molecule.eraseBond e) hI skel (P := u.atoms) (Or.inl hL) hne
        refine ⟨cs, hwf, lab, hinj, himg, ?_⟩
        rw [← groupArcs_erase G.molecule e u.atoms (by
          rintro ⟨h1, h2⟩
          rw [hL] at h1 h2
          have hb' := skel_b_not_L0 skel
          rcases hends' with ⟨-, h⟩ | ⟨h, -⟩
          · rw [h] at h2; exact hb' h2
          · rw [h] at h1; exact hb' h1) lab]
        exact harcs
      · obtain ⟨cs, hwf, lab, hinj, himg, harcs⟩ :=
          run_decode (G.molecule.eraseBond e) hI skel (P := u.atoms) (Or.inr hR) hne
        refine ⟨cs, hwf, lab, hinj, himg, ?_⟩
        rw [← groupArcs_erase G.molecule e u.atoms (by
          rintro ⟨h1, h2⟩
          rw [hR] at h1 h2
          have ha' := skel_a_not_R0 skel
          rcases hends' with ⟨h, -⟩ | ⟨-, h⟩
          · rw [h] at h1; exact ha' h1
          · rw [h] at h2; exact ha' h2) lab]
        exact harcs

end WaveTurbulence.ClassCount
