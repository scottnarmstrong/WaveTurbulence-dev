/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceUnits` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRes3
public import WaveTurbulence.Foundations.FinalCount.RedSpliceExt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits


/-!
# REDSPLICE-DEF (S2a), A4: the splice units of a group

`GroupUnits γ G S`: the (CL) blocks spliced out of the group `S` of `𝒞` (TARGET L1934-L1955): the runs of
ingredients of `𝒱` on both sides of the skipped ingredient (`skip`, with its runs `L0`, `R0`), or the whole
group.  `exists_groupUnits`: every group of `maximalGroupsG γ` has such a decomposition (HV and DV groups: none).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

theorem Spine.mem_iff {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine γ M L U a b) (v : V) :
    v ∈ U ↔ ∃ t ∈ L, v ∈ t.1 := by
  induction h with
  | one hv => simp
  | snoc _ hT _ _ ih =>
    simp only [mem_union, ih, List.mem_append, List.mem_singleton]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, Or.inl ht, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    · rintro ⟨t, ht | ht, h⟩
      · exact Or.inl ⟨t, ht, h⟩
      · subst ht; exact Or.inr h

theorem choose_vines {α : Type*} {P : Finset α → Prop} :
    ∀ (LL : List (Finset α × α × α)), (∀ t ∈ LL, ∃ T, P T ∧ T = t.1) →
      ∃ cs : List (Finset α), (∀ c ∈ cs, P c) ∧ ∀ v, (∃ t ∈ LL, v ∈ t.1) ↔ ∃ c ∈ cs, v ∈ c
  | [], _ => ⟨[], by simp, by simp⟩
  | t :: LL, h => by
    obtain ⟨T, hT, hTt⟩ := h t (List.mem_cons_self ..)
    obtain ⟨cs, hcs, hv⟩ := choose_vines LL (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    refine ⟨T :: cs, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hT
      · exact hcs c hc
    · intro v
      constructor
      · rintro ⟨t', ht', hv'⟩
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact ⟨T, List.mem_cons_self .., hTt ▸ hv'⟩
        · obtain ⟨c, hc, hvc⟩ := (hv v).mp ⟨t', ht', hv'⟩
          exact ⟨c, List.mem_cons_of_mem _ hc, hvc⟩
      · rintro ⟨c, hc, hvc⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨t, List.mem_cons_self .., hTt ▸ hvc⟩
        · obtain ⟨t', ht', hv'⟩ := (hv v).mpr ⟨c, hc, hvc⟩
          exact ⟨t', List.mem_cons_of_mem _ ht', hv'⟩

/-- The skipped ingredient of a group together with the two runs around it. -/
structure SkipData (γ : ℝ) (G : Garden w) (S : Finset (GBranch G.tree)) where
  A : Finset (GBranch G.tree)
  x : GBranch G.tree
  y : GBranch G.tree
  a : GBranch G.tree
  b : GBranch G.tree
  L0 : Finset (GBranch G.tree)
  R0 : Finset (GBranch G.tree)
  vine : Src.IsSomeVine γ G.molecule A x y
  ingredient : IsIngredientG γ G.molecule S A
  hS : S = L0 ∪ A ∪ R0
  disj : Disjoint L0 R0
  left : L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ a ∈ L0 ∧ x ∈ L0 ∧ L0 ∩ A = {x})
  right : R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ b ∈ R0 ∧ y ∈ R0 ∧ R0 ∩ A = {y})
  /-- `some e` iff the group is an HVC with added bond `e` joining `a`, `b`. -/
  bond : Option (GardenDart G)
  kind : CNMem G (A, x, y) ∨ ((bond = none → IsRootVCG γ G S) ∧ ∃ c : CLVineG γ G, c.atoms = A ∧ IsTopIngredientG S c)
  blockM : bond = none → G.molecule.IsBlock S a b
  blockN : ∀ e, bond = some e → G.molecule.ends e = s(a, b) ∧ (eraseBond G.molecule e).IsBlock S a b
  /-- the block decomposition `S = L0 ∪ A ∪ R0`, in the molecule (VC) or its adjoint (HVC) -/
  vineN : ∀ e, bond = some e → Src.IsSomeVine γ (eraseBond G.molecule e) A x y
  skelM : bond = none → SkelDecomp G.molecule S A L0 R0 a b x y
  skelN : ∀ e, bond = some e → SkelDecomp (eraseBond G.molecule e) S A L0 R0 a b x y
  /-- (R25) the skipped vine is an ingredient of the chain `S` from `a` to `b` (of the adjoint, for an HVC) -/
  chainM : bond = none → ∃ n, ChainIngredientG γ G.molecule S a b n A x y
  chainN : ∀ e, bond = some e → ∃ n, 2 ≤ n ∧ ChainIngredientG γ (eraseBond G.molecule e) S a b n A x y

/-- The splice units of the group `S` and how they sit in it. -/
structure GroupUnits (γ : ℝ) (G : Garden w) (S : Finset (GBranch G.tree)) where
  units : List (CLBlock G)
  sub : ∀ u ∈ units, u.atoms ⊆ S
  disj : units.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)
  /-- every unit is the union of vines of `𝒱` -/
  sound : ∀ u ∈ units, ∃ cs : List (Finset (GBranch G.tree)),
    (∀ c ∈ cs, ∃ c' ∈ vinesVG γ G, c'.atoms = c ∧ IsIngredientG γ G.molecule S c) ∧ ∀ v, v ∈ u.atoms ↔ ∃ c ∈ cs, v ∈ c
  skip : Option (SkipData γ G S)
  /-- with a skipped ingredient, the units are exactly its non-empty runs -/
  skip_units : ∀ sk, skip = some sk →
    (∀ u ∈ units, (u.atoms = sk.L0 ∧ (u.upper = sk.a ∧ u.lower = sk.x ∨ u.upper = sk.x ∧ u.lower = sk.a)) ∨
      (u.atoms = sk.R0 ∧ (u.upper = sk.y ∧ u.lower = sk.b ∨ u.upper = sk.b ∧ u.lower = sk.y))) ∧
    (sk.L0 = ∅ ∨ ∃ u ∈ units, u.atoms = sk.L0) ∧ (sk.R0 = ∅ ∨ ∃ u ∈ units, u.atoms = sk.R0)
  /-- without one, the unit is the whole group (or there is none) -/
  noskip_units : skip = none → ∀ u ∈ units, u.atoms = S
  /-- every unit has a joint carrying an out-dart and an in-dart external to it (the hinge pair, TARGET L2050) -/
  ext : ∀ u ∈ units, ∃ j, (j = u.upper ∨ j = u.lower) ∧ HasExtPair G.molecule u.atoms j
  /-- (R25) a whole-group unit means that the group is a VC -/
  whole_vc : skip = none → units ≠ [] → ∃ a b, Src.IsVC γ G.molecule S a b
  /-- an HV group is not spliced -/
  hv_empty : (∃ a b, Src.IsHV γ G.molecule S a b) → ¬ (∃ a b, Src.IsHVC γ G.molecule S a b) →
    units = []
  /-- every vine of `𝒱` that is an ingredient of the group lies in a unit (the cover property, TARGET L1936) -/
  cover : G.molecule.IsMolecule → S ∈ maximalGroupsG γ G.molecule → ∀ c : CLVineG γ G, c ∈ vinesVG γ G →
    IsIngredientG γ G.molecule S c.atoms → ∃ u ∈ units, c.atoms ⊆ u.atoms
  /-- SUBPRO amendment A1: a VC or HVC group is either (partly) spliced or has a skipped ingredient, i.e. it
  contributes a unit or an object of `C_1` (TARGET `subpro` (4) needs this: the SG root (CL) vine must be in `C_1`) -/
  vl : G.molecule.IsMolecule → S ∈ maximalGroupsG γ G.molecule →
    (∃ a b, Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) →
    units ≠ [] ∨ ∃ sk, skip = some sk

end WaveTurbulence.GammaLow.Fama
