/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: every unit of `Fama.unitBlocks γ G σ` is a unit code (UL)

`unit_decode`: for a unit `u ∈ Fama.unitBlocks γ G σ` there are ingredient codes `cs` and a labelling `lab` of the atoms of `u`
by `0 … unitWeight cs`, injective on `u.atoms`, whose arcs (the oriented bonds of `G` inside `u.atoms`) are `unitArcs cs`.
Cases: a whole-group unit (`whole_vc`: the group is a VC), or a skip-run `L₀`/`R₀` of an SG group around a skipped
ingredient (`Fama.SkipData`; the runs are chains by `Fama.ingredient_runs`, identified with `L₀`, `R₀` by `left_run_eq`,
`right_run_eq`); for an HVC the Fama.chain lives in `eraseBond G.molecule e`, and `groupArcs_erase` transfers the arcs.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]


theorem skel_a_not_R0 {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule V D'} {S A L0 R0 : Finset V}
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

/-- A run of a skip decomposition is a unit code (in the molecule `N` of the Fama.chain). -/
theorem run_decode {D' : Type} [Fintype D'] [DecidableEq D'] (N : Molecule V D') {S A L0 R0 : Finset V}
    {a b x y : V} {n : ℕ} (hI : ChainIngredientG γ N S a b n A x y)
    (sk : SkelDecomp N S A L0 R0 a b x y) {P : Finset V} (hP : P = L0 ∨ P = R0) (hne : P.Nonempty) :
    ∃ cs : List IngCodeG, (∀ c ∈ cs, c.Wf) ∧ ∃ lab : V → ℕ, Set.InjOn lab P ∧
      P.image lab = Finset.range (unitWeight cs + 1) ∧
      groupArcs N P lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  obtain ⟨L, R, hS1, hL, hR, hd⟩ := Fama.ingredient_runs sk.mol hI sk.hSB
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


/-- **UL**: every unit of `Fama.unitBlocks γ G σ` is a unit code. -/
theorem unit_decode {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ) :
    ∃ cs : List IngCodeG, (∀ c ∈ cs, c.Wf) ∧ ∃ lab : GBranch G.tree → ℕ, Set.InjOn lab u.atoms ∧
      u.atoms.image lab = Finset.range (unitWeight cs + 1) ∧
      groupArcs G.molecule u.atoms lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  obtain ⟨S', hSm, hσ, huU⟩ := Fama.mem_unitBlocks.mp hu
  have hne : u.atoms.Nonempty := ⟨u.upper, u.isBlock.2.1⟩
  rcases hsk : (Fama.groupUnitsOf γ G S').skip with _ | sk
  · have h1 := (Fama.groupUnitsOf γ G S').noskip_units hsk u huU
    obtain ⟨a, b, hB, n, hC⟩ := (Fama.groupUnitsOf γ G S').whole_vc hsk (List.ne_nil_of_mem huU)
    obtain ⟨cs, -, hwf, lab, hinj, himg, -, -, harcs⟩ :=
      chain_decode G.molecule hM (hC) hB
    rw [h1]; exact ⟨cs, hwf, lab, hinj, himg, harcs⟩
  · have hskip := ((Fama.groupUnitsOf γ G S').skip_units sk hsk).1 u huU
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

end WaveTurbulence.GammaLow.Famc.ClassCount
