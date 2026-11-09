/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceDesig` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickSpec
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceDesig
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport


/-!
# R83 successor copy: normalized designations and sigma-independent gap pairs

Source: pinned/r83-RedSpliceDesig.lean, with hash in COPIED-SHA256SUMS.
The HV triple uses hvGroupPick; pure DV uses dvGroupPick γ and exactly its type-V constituent.
Other designation clauses and the internal/hinge pair rules retain their original meaning.

* `groupJoint γ G S`: the first joint of a group (the skip data's `a` when the group has a skipped vine, a joint of
  the VC when the group has a whole-group unit, otherwise a joint of any of its kinds).
* `IsDesig γ G S a O` / `designatedObject γ G S`: the CANONICAL designated object of the group `S` (R6, R25(a)): the
  whole-group `vc ⟨S, a, b⟩` for a VC group, the whole-group hyper object with the cut bond for an HVC group;
  never a sub-block.  (For the remaining groups, HV and DV, an object of the group at its joint.)
* `intPairOrig γ G S`: an out/in pair of darts of the ORIGINAL garden `G` inside the designated object at the first
  joint.  `hingeOrigPair γ G S`: the pair used when the first joint is merged into a spliced unit (a pair of the
  skipped vine at its joint, or the external pair at a degree-four joint of the whole-group unit).
  Both pairs are chosen once, with no reference to `σ`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem chain_ofVine {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : Src.Chain γ M S a b n := by
  induction h with
  | single h => exact .single h
  | append h hV hI hne ih => exact .append ih hV hI hne

theorem group_object_at {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b ∨ Src.IsDV γ G.molecule S a b) :
    ∃ O : Src.Object γ G.molecule, O.atoms ⊆ S ∧ a = O.upper ∧ a ∈ S := by
  rcases h with ⟨e, he, hX⟩ | h | ⟨e, he, hb, n, _, hn⟩ | ⟨-, A, B, hA, hB, _, hS⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨(Src.isBlock_of_isSomeVine hX), 1, Src.Chain.single hX⟩⟩⟩, subset_refl _, rfl, (Src.isBlock_of_isSomeVine hX).2.1⟩
  · exact ⟨⟨S, a, b, .vc h⟩, subset_refl _, rfl, h.1.2.1⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, subset_refl _, rfl, hb.2.1⟩
  · exact ⟨⟨A, a, b, .vc ⟨Src.isBlock_of_isSomeVine hA, 1, Src.Chain.single hA⟩⟩, by rw [hS]; exact subset_union_left,
      rfl, by rw [hS]; exact mem_union_left _ (Src.isBlock_of_isSomeVine hA).2.1⟩

/-- The first joint of a group: see the module docstring.  (R28) For an HV group that is not an HVC the joint is that of the
canonical triple `hvGroupPick`; for a group having a joint of the kind HV, VC or HVC the kind is not DV. -/
@[expose] def IsGroupJoint (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ sk, (groupUnitsOf γ G S).skip = some sk → a = sk.a) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units ≠ [] → ∃ b, Src.IsVC γ G.molecule S a b) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    ∃ b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b ∨ Src.IsDV γ G.molecule S a b) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (∃ a b, Src.IsHV γ G.molecule S a b) → ¬ (∃ a b, Src.IsHVC γ G.molecule S a b) → ∃ b e, hvGroupPick γ G S = some (a, b, e)) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) →
    ∃ b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (¬ ∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) →
    ∃ A b, dvGroupPick γ G S = some (A, a, b))

/-- The first joint of a group of `𝒞` (`none` for anything else). -/
@[expose] noncomputable def groupJoint (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G) := ∅) :
    Option (GBranch G.tree) := by
  classical exact if markedGroup γ G Mk S then none else if h : ∃ a, IsGroupJoint γ G S a then some h.choose else none

theorem exists_groupJoint {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ a, IsGroupJoint γ G S a := by
  classical
  rcases hsk : (groupUnitsOf γ G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf γ G S).units = []
    · by_cases hv : (∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ (∃ a b, Src.IsHVC γ G.molecule S a b)
      · obtain ⟨a0, b0, e0, hpk, hends, hvine⟩ := hvGroupPick_some ⟨hS, hv⟩
        have hh : Src.IsHV γ G.molecule S a0 b0 := ⟨e0, hends, hvine⟩
        exact ⟨a0, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
          (fun _ _ => ⟨b0, Or.inl hh⟩), (fun _ _ _ _ => ⟨b0, e0, hpk⟩),
          (fun _ _ _ => ⟨b0, Or.inl hh⟩), (fun _ _ hn => (hn ⟨a0, b0, Or.inl hh⟩).elim)⟩
      · by_cases hvl : ∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b
        · obtain ⟨a, b, hb⟩ := hvl
          have hb4 : Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b ∨ Src.IsDV γ G.molecule S a b := by
            rcases hb with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
          exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ => ⟨b, hb4⟩), (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ _ => ⟨b, hb⟩),
            (fun _ _ hn => (hn ⟨a, b, hb⟩).elim)⟩
        · have hdv : ∃ a b, Src.IsDV γ G.molecule S a b := by
            obtain ⟨a, b, hb⟩ := hS.1
            rcases hb with h | h | h | h
            · exact (hvl ⟨a, b, Or.inl h⟩).elim
            · exact (hvl ⟨a, b, Or.inr (Or.inl h)⟩).elim
            · exact (hvl ⟨a, b, Or.inr (Or.inr h)⟩).elim
            · exact ⟨a, b, h⟩
          obtain ⟨A, a, b, hpk, hσ, B, hA, hB, hI, hU⟩ := dvGroupPick_some ⟨hS, hdv, hvl⟩
          have hd : Src.IsDV γ G.molecule S a b := ⟨hσ, A, B, hA, hB, hI, hU⟩
          exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ => ⟨b, Or.inr (Or.inr (Or.inr hd))⟩), (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv),
            (fun _ _ h => absurd h hvl), (fun _ _ _ => ⟨A, b, hpk⟩)⟩
    · obtain ⟨a, b, hvc⟩ := (groupUnitsOf γ G S).whole_vc hsk hu
      exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ _ => ⟨b, hvc⟩), (fun _ h => absurd h hu),
        (fun _ h => absurd h hu), (fun _ h => absurd h hu), (fun _ h => absurd h hu)⟩
  · exact ⟨sk.a, (fun sk' h => by rw [hsk] at h; cases h; rfl), (fun h => by rw [hsk] at h; cases h),
      (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h),
      (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h)⟩

theorem exists_groupJoint_eq {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ a, groupJoint γ G S = some a := by
  classical
  have h := exists_groupJoint hS
  refine ⟨h.choose, ?_⟩
  unfold groupJoint
  simp only [not_markedGroup_empty G S, ↓reduceIte]
  rw [dite_eq_left h]

theorem groupJoint_spec {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint γ G S = some a) :
    IsGroupJoint γ G S a := by
  classical
  unfold groupJoint at h
  simp only [not_markedGroup_empty G S, ↓reduceIte] at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h
    exact h ▸ hex.choose_spec



/-- The first joint of a group is a joint of one of its kinds. -/
theorem groupJoint_kind {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint γ G S = some a) :
    a ∈ S ∧ ∃ b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b ∨ Src.IsDV γ G.molecule S a b := by
  have hs := groupJoint_spec h
  rcases hsk : (groupUnitsOf γ G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf γ G S).units = []
    · obtain ⟨b, hb⟩ := hs.2.2.1 hsk hu
      obtain ⟨_, _, _, ha⟩ := group_object_at hb
      exact ⟨ha, b, hb⟩
    · obtain ⟨b, hb⟩ := hs.2.1 hsk hu
      obtain ⟨_, _, _, ha⟩ := group_object_at (Or.inr (Or.inl hb))
      exact ⟨ha, b, Or.inr (Or.inl hb)⟩
  · have ha : a = sk.a := hs.1 sk hsk
    subst ha
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have hv : Src.IsVC γ G.molecule S sk.a sk.b := ⟨sk.blockM hb, n, (chain_ofVine (chainIngredientG_spec hI).1)⟩
      exact ⟨(sk.blockM hb).2.1, sk.b, Or.inr (Or.inl hv)⟩
    · obtain ⟨n, hn, hI⟩ := sk.chainN e hb
      have hv : Src.IsHVC γ G.molecule S sk.a sk.b :=
        ⟨e, (sk.blockN e hb).1, (sk.blockN e hb).2, n, hn, (chain_ofVine (chainIngredientG_spec hI).1)⟩
      exact ⟨(sk.blockN e hb).2.2.1, sk.b, Or.inr (Or.inr (Or.inl hv))⟩

/-- **The designated object** (R6, R25(a)): `O` is an object of `S` with `a` one of its joints, the whole-group object
(`atoms = S`) of the shape that the cut of the group uses, never a sub-block. -/
@[expose] def IsDesig (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree) (O : Src.Object γ G.molecule) : Prop :=
  a = O.upper ∧ O.atoms ⊆ S ∧
  (∀ sk, (groupUnitsOf γ G S).skip = some sk → sk.bond = none →
    O.atoms = S ∧ ∃ hv : Src.IsVC γ G.molecule O.atoms O.upper O.lower, O.shape = Src.VineLikeObject.vc hv) ∧
  (∀ sk e, (groupUnitsOf γ G S).skip = some sk → sk.bond = some e →
    O.atoms = S ∧ ∃ R : Src.HyperLikeRealization γ G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ R.added = e) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units ≠ [] →
    O.atoms = S ∧ ∃ hv : Src.IsVC γ G.molecule O.atoms O.upper O.lower, O.shape = Src.VineLikeObject.vc hv) ∧
  -- (R28) an HV group that is not an HVC: the hyper object of the canonical triple `hvGroupPick`
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (∃ a b, Src.IsHV γ G.molecule S a b) → ¬ (∃ a b, Src.IsHVC γ G.molecule S a b) →
    ∃ b e, hvGroupPick γ G S = some (a, b, e) ∧ O.atoms = S ∧ O.lower = b ∧
      ∃ R : Src.HyperLikeRealization γ G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ R.added = e) ∧
  -- (R28) a group having a joint of the kind HV, VC or HVC is represented by its whole atom set
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) → O.atoms = S) ∧
  ((groupUnitsOf γ G S).skip = none → (groupUnitsOf γ G S).units = [] →
    (¬ ∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) →
    ∃ A b, dvGroupPick γ G S = some (A, a, b) ∧ O.atoms = A ∧ O.lower = b ∧
      ∃ hv : Src.IsSomeVine γ G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.vc ⟨Src.isBlock_of_isSomeVine hv, 1, Src.Chain.single hv⟩)

/-- The whole-group hyper object of a canonical HV triple. -/
theorem hv_object_orig {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {e : GardenDart G}
    (hends : G.molecule.ends e = s(a, b)) (hvine : Src.IsSomeVine γ (Molecule.eraseBond G.molecule e) S a b) :
    ∃ O : Src.Object γ G.molecule, O.atoms = S ∧ O.upper = a ∧ O.lower = b ∧
      ∃ R : Src.HyperLikeRealization γ G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ R.added = e := by
  have hX := hvine
  exact ⟨⟨S, a, b, .hyper ⟨e, hends, ⟨(Src.isBlock_of_isSomeVine hX), 1, Src.Chain.single hX⟩⟩⟩, rfl, rfl, rfl, _, rfl, rfl⟩

/-- A group with a joint of the kind HV, VC or HVC at `a` has a whole-group object at `a`. -/
theorem vl_object_orig {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b) :
    ∃ O : Src.Object γ G.molecule, O.atoms = S ∧ a = O.upper := by
  rcases h with ⟨e, he, hX⟩ | h | ⟨e, he, hb, n, _, hn⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨(Src.isBlock_of_isSomeVine hX), 1, Src.Chain.single hX⟩⟩⟩, rfl, rfl⟩
  · exact ⟨⟨S, a, b, .vc h⟩, rfl, rfl⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, rfl, rfl⟩

theorem exists_isDesig {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint γ G S = some a) :
    ∃ O : Src.Object γ G.molecule, IsDesig γ G S a O := by
  have hs := groupJoint_spec h
  rcases hsk : (groupUnitsOf γ G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf γ G S).units = []
    · by_cases hv : (∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ (∃ a b, Src.IsHVC γ G.molecule S a b)
      · obtain ⟨b0, e0, hpk⟩ := hs.2.2.2.1 hsk hu hv.1 hv.2
        obtain ⟨hends, hvine⟩ := hvGroupPick_valid hpk
        obtain ⟨O, hOa, hOu, hOl, R, hR, hRe⟩ := hv_object_orig hends hvine
        refine ⟨O, hOu.symm, hOa ▸ subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
          (fun sk e h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h), ?_, ?_, ?_⟩
        · intro _ _ _ _
          exact ⟨b0, e0, hpk, hOa, hOl, R, hR, hRe⟩
        · intro _ _ _; exact hOa
        · intro _ _ hn
          obtain ⟨a1, b1, hh⟩ := hv.1
          exact (hn ⟨a1, b1, Or.inl hh⟩).elim
      · by_cases hvl : ∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b
        · obtain ⟨b, hb⟩ := hs.2.2.2.2.1 hsk hu hvl
          obtain ⟨O, hOa, hOu⟩ := vl_object_orig hb
          exact ⟨O, hOu, hOa ▸ subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
            (fun sk e h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ _ => hOa), (fun _ _ hn => (hn hvl).elim)⟩
        · obtain ⟨A, b, hpk⟩ := hs.2.2.2.2.2 hsk hu hvl
          obtain ⟨hσ, B, hA, hB, hI, hU⟩ := dvGroupPick_valid hpk
          let hvA : Src.IsVC γ G.molecule A a b := ⟨Src.isBlock_of_isSomeVine hA, 1, Src.Chain.single hA⟩
          refine ⟨⟨A, a, b, .vc hvA⟩, rfl, ?_,
            (fun sk h => by rw [hsk] at h; cases h),
            (fun sk e h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ h => absurd h hvl),
            (fun _ _ _ => ⟨A, b, hpk, rfl, rfl, hA, rfl⟩)⟩
          rw [hU]
          exact subset_union_left
    · obtain ⟨b, hb⟩ := hs.2.1 hsk hu
      exact ⟨⟨S, a, b, .vc hb⟩, rfl, subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
        (fun sk e h => by rw [hsk] at h; cases h), (fun _ _ => ⟨rfl, hb, rfl⟩),
        (fun _ h => absurd h hu), (fun _ h => absurd h hu), (fun _ h => absurd h hu)⟩
  · have ha : a = sk.a := hs.1 sk hsk
    subst ha
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have hv : Src.IsVC γ G.molecule S sk.a sk.b := ⟨sk.blockM hb, n, (chain_ofVine (chainIngredientG_spec hI).1)⟩
      refine ⟨⟨S, sk.a, sk.b, .vc hv⟩, rfl, subset_refl _, ?_, ?_, (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h)⟩
      · intro sk' h _
        rw [hsk] at h; cases h
        exact ⟨rfl, hv, rfl⟩
      · intro sk' e' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
    · obtain ⟨n, hn, hI⟩ := sk.chainN e hb
      let R : Src.HyperLikeRealization γ G.molecule S sk.a sk.b :=
        ⟨e, (sk.blockN e hb).1, ⟨(sk.blockN e hb).2, n, (chain_ofVine (chainIngredientG_spec hI).1)⟩⟩
      refine ⟨⟨S, sk.a, sk.b, .hyper R⟩, rfl, subset_refl _, ?_, ?_, (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h)⟩
      · intro sk' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
      · intro sk' e' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
        exact ⟨rfl, R, rfl, rfl⟩

/-- **The designated object of a group** (a function of the original garden and the group only). -/
@[expose] noncomputable def designatedObject (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G) := ∅) :
    Option (Src.Object γ G.molecule) := by
  classical
  exact if h : ∃ a, groupJoint γ G S Mk = some a ∧ ∃ O, IsDesig γ G S a O then some h.choose_spec.2.choose else none

theorem designatedObject_spec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ a O, groupJoint γ G S = some a ∧ designatedObject γ G S = some O ∧ IsDesig γ G S a O := by
  classical
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  have h : ∃ a, groupJoint γ G S = some a ∧ ∃ O, IsDesig γ G S a O := ⟨a, ha, exists_isDesig ha⟩
  refine ⟨h.choose, h.choose_spec.2.choose, h.choose_spec.1, ?_, h.choose_spec.2.choose_spec⟩
  unfold designatedObject
  rw [dite_eq_left h]

/-- B1b (Mk-general form of `designatedObject_isDesig`). -/
theorem designatedObject_isDesigMk {S : Finset (GBranch G.tree)} {O : Src.Object γ G.molecule}
    {Mk : Set (CLVineG γ _)} (h : designatedObject γ (Mk := Mk) G S = some O) : ∃ a, groupJoint γ (Mk := Mk) G S = some a ∧ IsDesig γ G S a O := by
  classical
  unfold designatedObject at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h
    exact ⟨hex.choose, hex.choose_spec.1, h ▸ hex.choose_spec.2.choose_spec⟩

theorem designatedObject_isDesig {S : Finset (GBranch G.tree)} {O : Src.Object γ G.molecule}
    (h : designatedObject γ G S = some O) : ∃ a, groupJoint γ G S = some a ∧ IsDesig γ G S a O := designatedObject_isDesigMk (Mk := ∅) h

/-! ### The pair inside the designated object (non-hinge entries) -/

/-- An out/in pair of darts of the original garden inside the designated object, at its first joint. -/
@[expose] def IntSpec (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (p : GardenDart G × GardenDart G)
    (Mk : Set (CLVineG γ G) := ∅) : Prop :=
  ∃ a O, groupJoint γ G S Mk = some a ∧ designatedObject γ G S Mk = some O ∧ (a = O.upper ∨ a = O.lower) ∧
    TripleAt G a p.1 p.2 ∧ O.ContainsDart p.1 ∧ O.ContainsDart p.2

theorem exists_intSpec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ p, IntSpec γ G S p := by
  obtain ⟨a, O, ha, hO, hd⟩ := designatedObject_spec hS
  obtain ⟨x, y, hT, hx, hy⟩ := objectJoint_pair O (Or.inl hd.1)
  exact ⟨(x, y), a, O, ha, hO, Or.inl hd.1, hT, hx, hy⟩

/-- **The pair of the group in the original garden, chosen once and independently of `σ`.** -/
@[expose] noncomputable def intPairOrig (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G) := ∅) :
    Option (GardenDart G × GardenDart G) := by
  classical exact if h : ∃ p, IntSpec γ G S p Mk then some h.choose else none

theorem intPairOrig_spec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ p, intPairOrig γ G S = some p ∧ IntSpec γ G S p := by
  classical
  have h := exists_intSpec hS
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold intPairOrig
  rw [dite_eq_left h]

/-! ### The pair at a merged first joint (hinge entries) -/

section run
variable {V D' : Type} [DecidableEq V] [Fintype D'] [DecidableEq D'] {N : Molecule V D'}


end run

/-- The pair used when the first joint of the group is merged into a spliced unit `u`: an out/in pair of the
original garden at an atom `j` of `u`, external to `u`; for a skipped vine it lies in the skipped vine `A`
(and is not the cut bond), for a whole-group unit `j` is a joint of the unit. -/
@[expose] def HingeSpec (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (p : GardenDart G × GardenDart G) : Prop :=
  ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms ∧ ∃ j ∈ u.atoms,
    TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
    (∀ sk, (groupUnitsOf γ G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
      G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
      ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
    ((groupUnitsOf γ G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower))


theorem hingeSpec_of_run {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    {u : CLBlock G} (hu : u ∈ (groupUnitsOf γ G S).units) (hau : a ∈ u.atoms)
    {sk : SkipData γ G S} (hsk : (groupUnitsOf γ G S).skip = some sk) {j : GBranch G.tree} (hjx : j = sk.x ∨ j = sk.y)
    (hjU : j ∈ u.atoms) (x y : GardenDart G) (hx : G.molecule.atom x = j) (hy : G.molecule.atom y = j)
    (hxo : G.molecule.out x = true) (hyo : G.molecule.out y = false) (hne : y ≠ G.molecule.mate x)
    (hxA : G.molecule.atom (G.molecule.mate x) ∈ sk.A) (hyA : G.molecule.atom (G.molecule.mate y) ∈ sk.A)
    (hxn : G.molecule.atom (G.molecule.mate x) ∉ u.atoms) (hyn : G.molecule.atom (G.molecule.mate y) ∉ u.atoms)
    (he : ∀ e, sk.bond = some e → x ≠ e ∧ x ≠ G.molecule.mate e ∧ y ≠ e ∧ y ≠ G.molecule.mate e) :
    ∃ p, HingeSpec γ G S a p := by
  refine ⟨(x, y), u, hu, hau, j, hjU, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_, ?_, ?_⟩
  · intro h; exact hxn h.2
  · intro h; exact hyn h.2
  · intro sk' h
    rw [hsk] at h; cases h
    exact ⟨hjx, hxA, hyA, fun e hb => he e hb⟩
  · intro h; rw [hsk] at h; cases h

/-- **Existence of the hinge pair.** -/
theorem exists_hingeSpec {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) : ∃ p, HingeSpec γ G S a p := by
  obtain ⟨u, hu, hau⟩ := hu
  rcases hsk : (groupUnitsOf γ G S).skip with _ | sk
  · have hS := (groupUnitsOf γ G S).noskip_units hsk u hu
    obtain ⟨j, hj, d1, d2, h1, h2, n1, n2, o1, o2⟩ := (groupUnitsOf γ G S).ext u hu
    have hjU : j ∈ u.atoms := by rcases hj with rfl | rfl; exact u.isBlock.2.1; exact u.isBlock.2.2.1
    have hne : d2 ≠ G.molecule.mate d1 := by
      intro h
      apply n1
      exact ⟨h1 ▸ hjU, by rw [← h, h2]; exact hjU⟩
    refine ⟨(d1, d2), u, hu, hau, j, hjU, ⟨h1, h2, hne, by rw [o1, o2]; simp⟩, n1, n2, ?_, ?_⟩
    · intro sk' h; rw [hsk] at h; cases h
    · intro _; exact ⟨hS, hj⟩
  · have hsu := (groupUnitsOf γ G S).skip_units sk hsk
    rcases hsu.1 u hu with ⟨hL, _⟩ | ⟨hR, _⟩
    · -- the left run
      rcases hb : sk.bond with _ | e
      · have H := sk.skelM hb
        rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hLA⟩
        · rw [hL, h0] at hau; exact absurd hau (by simp)
        · obtain ⟨x, y, hx, hy, hxo, hyo, hne, hxA, hyA, hxn, hyn⟩ := ext_pair_run' H.hA hLA
          have hjL : sk.x ∈ u.atoms := by
            rw [hL]; exact (mem_inter.mp (by rw [hLA]; exact mem_singleton_self _ : sk.x ∈ sk.L0 ∩ sk.A)).1
          exact hingeSpec_of_run hu hau hsk (Or.inl rfl) hjL x y hx hy hxo hyo hne hxA hyA (hL ▸ hxn) (hL ▸ hyn)
            (fun e he => by rw [hb] at he; cases he)
      · have H := sk.skelN e hb
        rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hLA⟩
        · rw [hL, h0] at hau; exact absurd hau (by simp)
        · obtain ⟨x, y, hx, hy, hxo, hyo, hne, hxA, hyA, hxn, hyn, h1, h2, h3, h4⟩ := run_pair_erase G.molecule e H.hA hLA
          have hjL : sk.x ∈ u.atoms := by
            rw [hL]; exact (mem_inter.mp (by rw [hLA]; exact mem_singleton_self _ : sk.x ∈ sk.L0 ∩ sk.A)).1
          exact hingeSpec_of_run hu hau hsk (Or.inl rfl) hjL x y hx hy hxo hyo hne hxA hyA (hL ▸ hxn) (hL ▸ hyn)
            (fun e' he' => by rw [hb] at he'; cases he'; exact ⟨h1, h2, h3, h4⟩)
    · -- the right run
      rcases hb : sk.bond with _ | e
      · have H := sk.skelM hb
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hRA⟩
        · rw [hR, h0] at hau; exact absurd hau (by simp)
        · obtain ⟨x, y, hx, hy, hxo, hyo, hne, hxA, hyA, hxn, hyn⟩ :=
            ext_pair_run' (block_swap_joints _ H.hA) hRA
          have hjL : sk.y ∈ u.atoms := by
            rw [hR]; exact (mem_inter.mp (by rw [hRA]; exact mem_singleton_self _ : sk.y ∈ sk.R0 ∩ sk.A)).1
          exact hingeSpec_of_run hu hau hsk (Or.inr rfl) hjL x y hx hy hxo hyo hne hxA hyA (hR ▸ hxn) (hR ▸ hyn)
            (fun e he => by rw [hb] at he; cases he)
      · have H := sk.skelN e hb
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hRA⟩
        · rw [hR, h0] at hau; exact absurd hau (by simp)
        · obtain ⟨x, y, hx, hy, hxo, hyo, hne, hxA, hyA, hxn, hyn, h1, h2, h3, h4⟩ :=
            run_pair_erase G.molecule e (block_swap_joints _ H.hA) hRA
          have hjL : sk.y ∈ u.atoms := by
            rw [hR]; exact (mem_inter.mp (by rw [hRA]; exact mem_singleton_self _ : sk.y ∈ sk.R0 ∩ sk.A)).1
          exact hingeSpec_of_run hu hau hsk (Or.inr rfl) hjL x y hx hy hxo hyo hne hxA hyA (hR ▸ hxn) (hR ▸ hyn)
            (fun e' he' => by rw [hb] at he'; cases he'; exact ⟨h1, h2, h3, h4⟩)


/-- (R37) Tier 2 of the triple-bond rule: both bonds of the pair lead into the same unit of some group of `𝒞`
(so that they lead to one atom of `G_sb` as soon as that unit is spliced). -/
@[expose] def PairSameUnit (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ S' ∈ maximalGroupsG γ G.molecule, ∃ u' ∈ (groupUnitsOf γ G S').units,
    G.molecule.atom (G.molecule.mate p.1) ∈ u'.atoms ∧ G.molecule.atom (G.molecule.mate p.2) ∈ u'.atoms

/-- (R37) **The chosen hinge pair**: a `HingeSpec` pair that prefers (tier 1) a pair whose two bonds lead to one atom, then
(tier 2) a pair whose two bonds lead into one unit.  Both criteria refer to the ORIGINAL garden only (no `σ`). -/
@[expose] def HingeBest (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (p : GardenDart G × GardenDart G) : Prop :=
  HingeSpec γ G S a p ∧
    ((∃ p', HingeSpec γ G S a p' ∧ PairSameAtom G p') → PairSameAtom G p) ∧
    ((∃ p', HingeSpec γ G S a p' ∧ PairSameUnit γ G p') → PairSameAtom G p ∨ PairSameUnit γ G p)

theorem exists_hingeBest {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) : ∃ p, HingeBest γ G S a p := by
  classical
  obtain ⟨p0, hp0⟩ := exists_hingeSpec hu
  by_cases h1 : ∃ p', HingeSpec γ G S a p' ∧ PairSameAtom G p'
  · obtain ⟨p', hp', ht⟩ := h1
    exact ⟨p', hp', fun _ => ht, fun _ => Or.inl ht⟩
  · by_cases h2 : ∃ p', HingeSpec γ G S a p' ∧ PairSameUnit γ G p'
    · obtain ⟨p', hp', ht⟩ := h2
      exact ⟨p', hp', fun h => absurd h h1, fun _ => Or.inr ht⟩
    · exact ⟨p0, hp0, fun h => absurd h h1, fun h => absurd h h2⟩

/-- **The pair of the group at a merged first joint, chosen once and independently of `σ`** (R37: `HingeBest`, so that when
a hinge has a triple bond the chosen joint is the one whose external pair lies in the triple bond). -/
@[expose] noncomputable def hingeOrigPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G) := ∅) :
    Option (GardenDart G × GardenDart G) := by
  classical exact if h : ∃ p a, groupJoint γ G S Mk = some a ∧ HingeBest γ G S a p then some h.choose else none

/-- B1b (Mk-general form of `hingeOrigPair_best`). -/
theorem hingeOrigPair_bestMk {S : Finset (GBranch G.tree)} {a : GBranch G.tree} {Mk : Set (CLVineG γ _)} (ha : groupJoint γ (Mk := Mk) G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair γ (Mk := Mk) G S = some p ∧ HingeBest γ G S a p := by
  classical
  obtain ⟨p0, hp0⟩ := exists_hingeBest hu
  have h : ∃ p a, groupJoint γ (Mk := Mk) G S = some a ∧ HingeBest γ G S a p := ⟨p0, a, ha, hp0⟩
  refine ⟨h.choose, ?_, ?_⟩
  · unfold hingeOrigPair; rw [dite_eq_left h]
  · obtain ⟨a', ha', hs⟩ := h.choose_spec
    rw [ha] at ha'
    cases ha'
    exact hs

theorem hingeOrigPair_best {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (ha : groupJoint γ G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair γ G S = some p ∧ HingeBest γ G S a p := hingeOrigPair_bestMk (Mk := ∅) ha hu

/-- B1b (Mk-general form of `hingeOrigPair_spec`). -/
theorem hingeOrigPair_specMk {S : Finset (GBranch G.tree)} {a : GBranch G.tree} {Mk : Set (CLVineG γ _)} (ha : groupJoint γ (Mk := Mk) G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair γ (Mk := Mk) G S = some p ∧ HingeSpec γ G S a p := by
  obtain ⟨p, hp, hb⟩ := hingeOrigPair_bestMk (Mk := Mk) ha hu
  exact ⟨p, hp, hb.1⟩

theorem hingeOrigPair_spec {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (ha : groupJoint γ G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf γ G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair γ G S = some p ∧ HingeSpec γ G S a p := hingeOrigPair_specMk (Mk := ∅) ha hu

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
