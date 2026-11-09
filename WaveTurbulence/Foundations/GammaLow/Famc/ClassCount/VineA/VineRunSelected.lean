/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineRunSelected` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.Vine.A.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
/-! Declared skipped runs have spines consisting entirely of selected V
ingredients in the original garden molecule. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- A spine is determined by its ingredient vines and the source concatenations. -/
theorem spine_replace_molecule {V D E : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {M : Molecule V D} {N : Molecule V E}
    {L : List (Finset V × V × V)} {S : Finset V} {a b : V} (hs : Fama.Spine γ M L S a b)
    (hv : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine γ N T p q) :
    Fama.Spine γ N L S a b := by
  induction hs with
  | one _ => exact .one (hv _ _ _ (List.mem_singleton_self _))
  | snoc hs ht hi hne ih =>
    exact .snoc (ih (fun T p q hm => hv T p q (List.mem_append_left _ hm)))
      (hv _ _ _ (List.mem_append_right _ (List.mem_singleton_self _))) hi hne

/-- An atom set with distinct Fama.joints cannot fit into a singleton intersection. -/
theorem atoms_ne_skipped {D : Type} [Fintype D] [DecidableEq D]
    {N : Molecule (GBranch G.tree) D} {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S)
    {LL : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {R : Finset (GBranch G.tree)} {a b j : GBranch G.tree}
    (hs : Fama.Spine γ N LL R a b) (hi : R ∩ sk.A = {j})
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ LL) : t.1 ≠ sk.A := by
  intro he
  have hsub : sk.A ⊆ R := he ▸ (hs.mem_vine ht).2
  have hj := Fama.isSomeVine_ends sk.vine
  have hx := mem_inter.mpr ⟨hsub hj.1, hj.1⟩
  have hy := mem_inter.mpr ⟨hsub hj.2.1, hj.2.1⟩
  rw [hi, mem_singleton] at hx hy
  exact hj.2.2 (hx.trans hy.symm)

/-- A declared skipped run has only V ingredients, in the original molecule. -/
theorem skipped_run_spines {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    (hS : S ∈ maximalGroupsG γ G.molecule) (sk : Fama.SkipData γ G S) (hsk : U.skip = some sk)
    {D : Type} [Fintype D] [DecidableEq D] {N : Molecule (GBranch G.tree) D}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (H : SkelDecomp N S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y)
    (hs : Fama.Spine γ N L S sk.a sk.b) (hA : (sk.A, sk.x, sk.y) ∈ L)
    (hv : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine γ G.molecule T p q)
    (hi : ∀ T p q, (T, p, q) ∈ L → IsIngredientG γ G.molecule S T) :
    (sk.L0 = ∅ ∨ ∃ LL, Fama.Spine γ G.molecule LL sk.L0 sk.a sk.x ∧
      ∀ t ∈ LL, ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1) ∧
    (sk.R0 = ∅ ∨ ∃ RR, Fama.Spine γ G.molecule RR sk.R0 sk.y sk.b ∧
      ∀ t ∈ RR, ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1) := by
  obtain ⟨LL, RR, L0, R0, hL, hScut, hl, hr, hd⟩ := hs.split_around H.mol H.hSB hA
  have K : SkelDecomp N S sk.A L0 R0 sk.a sk.b sk.x sk.y := {
    mol := H.mol, hS := hScut, hSB := H.hSB, hA := H.hA,
    hL := hl.imp (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.1, h.2.1, h.2.2.2⟩),
    hR := hr.imp (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.1, h.2.1, h.2.2.2⟩), hd := hd }
  obtain ⟨heL, heR⟩ := run_unique H K
  rw [← heL] at hl
  rw [← heR] at hr
  have hLL : ∀ t ∈ LL, t ∈ L := by intro t ht; rw [hL]; exact List.mem_append_left _ ht
  have hRR : ∀ t ∈ RR, t ∈ L := by
    intro t ht; rw [hL]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
  have hsel := skip_spine_selected U hS sk hsk hs hA hv hi
  constructor
  · rcases hl with ⟨_, he, _⟩ | ⟨_, _, hsL, hiL⟩
    · exact Or.inl he
    · refine Or.inr ⟨LL, spine_replace_molecule hsL (fun T p q ht => hv T p q (hLL _ ht)), ?_⟩
      intro t ht
      exact hsel t (hLL t ht) (atoms_ne_skipped sk hsL hiL ht)
  · rcases hr with ⟨_, he, _⟩ | ⟨_, _, hsR, hiR⟩
    · exact Or.inl he
    · refine Or.inr ⟨RR, spine_replace_molecule hsR (fun T p q ht => hv T p q (hRR _ ht)), ?_⟩
      intro t ht
      exact hsel t (hRR t ht) (atoms_ne_skipped sk hsR hiR ht)

end WaveTurbulence.GammaLow.Famc.VineA
