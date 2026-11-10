/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: units are vine chains `Src.Chain γ G.molecule u.atoms u.upper u.lower n`

Same case analysis as `unit_decode` (whole-group units, skip runs of the molecule of the Fama.chain, runs of an HVC in the
molecule with the deleted bond), returning the Fama.chain instead of the code.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

theorem chain_orient {M : Molecule V D} {P : Finset V} {a' b' up lo : V} {n : ℕ}
    (hC : Src.Chain γ M P a' b' n) (hB' : M.IsBlock P a' b') (hB : M.IsBlock P up lo) :
    ∃ n', Src.Chain γ M P up lo n' := by
  have hj := Vine.block_joints_unique M hB' hB
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact ⟨n, hC⟩
  · subst h1; subst h2
    exact ⟨n, (chain_swap (hC))⟩

/-- A run of a skip decomposition is a unit code (in the molecule `N` of the Fama.chain). -/
theorem run_chain {D' : Type} [Fintype D'] [DecidableEq D'] (N : Molecule V D') {S A L0 R0 : Finset V}
    {a b x y : V} {n : ℕ} (hI : ChainIngredientG γ N S a b n A x y)
    (sk : SkelDecomp N S A L0 R0 a b x y) {P : Finset V} (hP : P = L0 ∨ P = R0) (hne : P.Nonempty) :
    ∃ a' b' n', N.IsBlock P a' b' ∧ Src.Chain γ N P a' b' n' := by
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
        exact ⟨_, _, _, hLB', hm⟩
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
        exact ⟨_, _, _, hRB', hm⟩



/-- **Every unit of `Fama.unitBlocks γ G σ` is a vine Fama.chain of the molecule of `G`.** -/
theorem unit_chain {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ) :
    ∃ n, Src.Chain γ G.molecule u.atoms u.upper u.lower n := by
  classical
  obtain ⟨S', hSm, hσ, huU⟩ := Fama.mem_unitBlocks.mp hu
  have hne : u.atoms.Nonempty := ⟨u.upper, u.isBlock.2.1⟩
  rcases hsk : (Fama.groupUnitsOf γ G S').skip with _ | sk
  · have h1 := (Fama.groupUnitsOf γ G S').noskip_units hsk u huU
    obtain ⟨a, b, hB, n, hC⟩ := (Fama.groupUnitsOf γ G S').whole_vc hsk (List.ne_nil_of_mem huU)
    rw [h1]
    have hB2 := u.isBlock
    rw [h1] at hB2
    exact chain_orient (hC) hB hB2
  · have hskip := ((Fama.groupUnitsOf γ G S').skip_units sk hsk).1 u huU
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have skel := sk.skelM hb
      obtain ⟨a', b', n', hB', hC'⟩ : ∃ a' b' n', G.molecule.IsBlock u.atoms a' b' ∧
          Src.Chain γ G.molecule u.atoms a' b' n' := by
        rcases hskip with ⟨hL, -⟩ | ⟨hR, -⟩
        · exact run_chain G.molecule hI skel (P := u.atoms) (Or.inl hL) hne
        · exact run_chain G.molecule hI skel (P := u.atoms) (Or.inr hR) hne
      exact chain_orient hC' hB' u.isBlock
    · obtain ⟨n, -, hI⟩ := sk.chainN e hb
      have skel := sk.skelN e hb
      have hends := (sk.blockN e hb).1
      have hends' : (G.molecule.atom e = sk.a ∧ G.molecule.atom (G.molecule.mate e) = sk.b) ∨
          (G.molecule.atom e = sk.b ∧ G.molecule.atom (G.molecule.mate e) = sk.a) := by
        have := Sym2.eq_iff.mp hends
        exact this
      have hnot : ¬ G.molecule.InGroup u.atoms e := by
        rintro ⟨h1, h2⟩
        rcases hskip with ⟨hL, -⟩ | ⟨hR, -⟩
        · rw [hL] at h1 h2
          have hb' := skel_b_not_L0 skel
          rcases hends' with ⟨-, h⟩ | ⟨h, -⟩
          · rw [h] at h2; exact hb' h2
          · rw [h] at h1; exact hb' h1
        · rw [hR] at h1 h2
          have ha' := skel_a_not_R0 skel
          rcases hends' with ⟨h, -⟩ | ⟨-, h⟩
          · rw [h] at h1; exact ha' h1
          · rw [h] at h2; exact ha' h2
      obtain ⟨a', b', n', hB', hC'⟩ : ∃ a' b' n', (G.molecule.eraseBond e).IsBlock u.atoms a' b' ∧
          Src.Chain γ (G.molecule.eraseBond e) u.atoms a' b' n' := by
        rcases hskip with ⟨hL, -⟩ | ⟨hR, -⟩
        · exact run_chain (G.molecule.eraseBond e) hI skel (P := u.atoms) (Or.inl hL) hne
        · exact run_chain (G.molecule.eraseBond e) hI skel (P := u.atoms) (Or.inr hR) hne
      exact chain_orient (chain_of_eraseBond e hC' hnot) (isBlock_of_eraseBond e hB' hnot) u.isBlock

/-- B1b (Mk-general form of `unit_chain`): every unit (a run at a marked group: the `Fama.chain` field of
`Fama.MarkedGroupUnits`) is a vine Fama.chain. -/
theorem unit_chainMk {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ Mk) :
    ∃ n, Src.Chain γ G.molecule u.atoms u.upper u.lower n := by
  classical
  obtain ⟨S, hS, hσ, hum⟩ := Fama.mem_unitBlocksMk.mp hu
  by_cases hm : Fama.markedGroup γ G Mk S
  · unfold Fama.groupUnitsMk at hum
    simp only [hm, ↓reduceIte] at hum
    split_ifs at hum with hne
    · exact (Classical.choice hne).chain u hum
    · simp at hum
  · rw [Fama.groupUnitsMk_of_not_marked hm] at hum
    exact unit_chain G hM σ (Fama.mem_unitBlocks.mpr ⟨S, hS, hσ, hum⟩)

/-- B2d: **UL at a marking**: every unit of `Fama.unitBlocks γ G σ Mk` is a unit code.  (A unit is a vine Fama.chain from its
upper to its lower joint, `unit_chainMk`, so `chain_decode` applies; no skip decomposition is needed.) -/
theorem unit_decodeMk {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {Mk : Set (CLVineG γ G)} {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ Mk) :
    ∃ cs : List IngCodeG, (∀ c ∈ cs, c.Wf) ∧ ∃ lab : GBranch G.tree → ℕ, Set.InjOn lab u.atoms ∧
      u.atoms.image lab = Finset.range (unitWeight cs + 1) ∧
      groupArcs G.molecule u.atoms lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  obtain ⟨n, hC⟩ := unit_chainMk G hM σ hu
  obtain ⟨cs, -, hwf, lab, hinj, himg, -, -, harcs⟩ := chain_decode G.molecule hM hC u.isBlock
  exact ⟨cs, hwf, lab, hinj, himg, harcs⟩

end WaveTurbulence.GammaLow.Famc.ClassCount
