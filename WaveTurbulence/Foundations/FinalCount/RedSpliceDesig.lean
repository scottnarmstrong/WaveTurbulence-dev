/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePairs
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R25: the designated object of a group and the sigma-independent gap pairs

* `groupJoint G S`: the first joint of a group (the skip data's `a` when the group has a skipped vine, a joint of
  the VC when the group has a whole-group unit, otherwise a joint of any of its kinds).
* `IsDesig G S a O` / `designatedObject G S`: the CANONICAL designated object of the group `S` (R6, R25(a)): the
  whole-group `vc ⟨S, a, b⟩` for a VC group, the whole-group hyper object with the cut bond for an HVC group;
  never a sub-block.  (For the remaining groups, HV and DV, an object of the group at its joint.)
* `intPairOrig G S`: an out/in pair of darts of the ORIGINAL garden `G` inside the designated object at the first
  joint.  `hingeOrigPair G S`: the pair used when the first joint is merged into a spliced unit (a pair of the
  skipped vine at its joint, or the external pair at a degree-four joint of the whole-group unit).
  Both pairs are chosen once, with no reference to `σ`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem chain_ofVine {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {S : Finset V} {a b : V} {n : ℕ} (h : Vine.Chain M S a b n) : LGSpine.SourceVine.Chain M S a b n := by
  induction h with
  | single h => exact .single h
  | append h hV hI hne ih => exact .append ih hV hI hne

theorem group_object_at {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b ∨ IsDV G.molecule S a b) :
    ∃ O : Object G.molecule, O.atoms ⊆ S ∧ a = O.upper ∧ a ∈ S := by
  rcases h with ⟨e, he, X, hX⟩ | h | ⟨e, he, hb, n, _, hn⟩ | ⟨A, B, hA, hB, _, hS⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩⟩, subset_refl _, rfl, hX.1.2.1⟩
  · exact ⟨⟨S, a, b, .vc h⟩, subset_refl _, rfl, h.1.2.1⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, subset_refl _, rfl, hb.2.1⟩
  · exact ⟨⟨A, a, b, .vc ⟨hA.1, 1, Chain.single ⟨.V, hA⟩⟩⟩, by rw [hS]; exact subset_union_left, rfl,
      by rw [hS]; exact mem_union_left _ hA.1.2.1⟩

/-- The first joint of a group: see the module docstring.  (R28) For an HV group that is not an HVC the joint is that of the
canonical triple `hvPick`; for a group having a joint of the kind HV, VC or HVC the kind is not DV. -/
@[expose] def IsGroupJoint (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ sk, (groupUnitsOf G S).skip = some sk → a = sk.a) ∧
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units ≠ [] → ∃ b, IsVC G.molecule S a b) ∧
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units = [] →
    ∃ b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b ∨ IsDV G.molecule S a b) ∧
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units = [] →
    (∃ a b, IsHV G.molecule S a b) → ¬ (∃ a b, IsHVC G.molecule S a b) → ∃ b e, hvPick G S = some (a, b, e)) ∧
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units = [] →
    (∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b) →
    ∃ b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b)

/-- The first joint of a group of `𝒞` (`none` for anything else). -/
@[expose] noncomputable def groupJoint (G : Garden w) (S : Finset (GBranch G.tree)) : Option (GBranch G.tree) := by
  classical exact if h : ∃ a, IsGroupJoint G S a then some h.choose else none

theorem exists_groupJoint {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ a, IsGroupJoint G S a := by
  classical
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf G S).units = []
    · by_cases hv : (∃ a b, IsHV G.molecule S a b) ∧ ¬ (∃ a b, IsHVC G.molecule S a b)
      · obtain ⟨a0, b0, e0, hpk, hends, hvine⟩ := hvPick_some hv.1
        exact ⟨a0, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
          (fun _ _ => ⟨b0, Or.inl ⟨e0, hends, hvine⟩⟩), (fun _ _ _ _ => ⟨b0, e0, hpk⟩),
          (fun _ _ _ => ⟨b0, Or.inl ⟨e0, hends, hvine⟩⟩)⟩
      · by_cases hvl : ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b
        · obtain ⟨a, b, hb⟩ := hvl
          have hb4 : IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b ∨ IsDV G.molecule S a b := by
            rcases hb with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
          exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ => ⟨b, hb4⟩), (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ _ => ⟨b, hb⟩)⟩
        · obtain ⟨a, b, hb⟩ := hS.1
          exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h), (fun _ _ => ⟨b, hb⟩),
            (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv),
            (fun _ _ h => absurd h hvl)⟩
    · obtain ⟨a, b, hvc⟩ := (groupUnitsOf G S).whole_vc hsk hu
      exact ⟨a, (fun sk h => by rw [hsk] at h; cases h), (fun _ _ => ⟨b, hvc⟩), (fun _ h => absurd h hu),
        (fun _ h => absurd h hu), (fun _ h => absurd h hu)⟩
  · exact ⟨sk.a, (fun sk' h => by rw [hsk] at h; cases h; rfl), (fun h => by rw [hsk] at h; cases h),
      (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h),
      (fun h => by rw [hsk] at h; cases h)⟩

theorem exists_groupJoint_eq {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ a, groupJoint G S = some a := by
  classical
  have h := exists_groupJoint hS
  refine ⟨h.choose, ?_⟩
  unfold groupJoint
  rw [dif_pos h]

theorem groupJoint_spec {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint G S = some a) :
    IsGroupJoint G S a := by
  classical
  unfold groupJoint at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h
    exact h ▸ hex.choose_spec

/-- The first joint of a group is a joint of one of its kinds. -/
theorem groupJoint_kind {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint G S = some a) :
    a ∈ S ∧ ∃ b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b ∨ IsDV G.molecule S a b := by
  have hs := groupJoint_spec h
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf G S).units = []
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
      have hv : IsVC G.molecule S sk.a sk.b := ⟨sk.blockM hb, n, (chain_ofVine (Vine.chainIngredient_spec hI).1)⟩
      exact ⟨(sk.blockM hb).2.1, sk.b, Or.inr (Or.inl hv)⟩
    · obtain ⟨n, hn, hI⟩ := sk.chainN e hb
      have hv : IsHVC G.molecule S sk.a sk.b :=
        ⟨e, (sk.blockN e hb).1, (sk.blockN e hb).2, n, hn, (chain_ofVine (Vine.chainIngredient_spec hI).1)⟩
      exact ⟨(sk.blockN e hb).2.2.1, sk.b, Or.inr (Or.inr (Or.inl hv))⟩

/-- **The designated object** (R6, R25(a)): `O` is an object of `S` with `a` one of its joints, the whole-group object
(`atoms = S`) of the shape that the cut of the group uses, never a sub-block. -/
@[expose] def IsDesig (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree) (O : Object G.molecule) : Prop :=
  a = O.upper ∧ O.atoms ⊆ S ∧
  (∀ sk, (groupUnitsOf G S).skip = some sk → sk.bond = none →
    O.atoms = S ∧ ∃ hv : IsVC G.molecule O.atoms O.upper O.lower, O.shape = VineLikeObject.vc hv) ∧
  (∀ sk e, (groupUnitsOf G S).skip = some sk → sk.bond = some e →
    O.atoms = S ∧ ∃ R : HyperLikeRealization G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ R.added = e) ∧
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units ≠ [] →
    O.atoms = S ∧ ∃ hv : IsVC G.molecule O.atoms O.upper O.lower, O.shape = VineLikeObject.vc hv) ∧
  -- (R28) an HV group that is not an HVC: the hyper object of the canonical triple `hvPick`
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units = [] →
    (∃ a b, IsHV G.molecule S a b) → ¬ (∃ a b, IsHVC G.molecule S a b) →
    ∃ b e, hvPick G S = some (a, b, e) ∧ O.atoms = S ∧ O.lower = b ∧
      ∃ R : HyperLikeRealization G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ R.added = e) ∧
  -- (R28) a group having a joint of the kind HV, VC or HVC is represented by its whole atom set
  ((groupUnitsOf G S).skip = none → (groupUnitsOf G S).units = [] →
    (∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b) → O.atoms = S)

/-- The whole-group hyper object of a canonical HV triple. -/
theorem hv_object_orig {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {e : GardenDart G}
    (hends : G.molecule.ends e = s(a, b)) (hvine : IsSomeVine (Molecule.eraseBond G.molecule e) S a b) :
    ∃ O : Object G.molecule, O.atoms = S ∧ O.upper = a ∧ O.lower = b ∧
      ∃ R : HyperLikeRealization G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ R.added = e := by
  obtain ⟨X, hX⟩ := hvine
  exact ⟨⟨S, a, b, .hyper ⟨e, hends, ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩⟩, rfl, rfl, rfl, _, rfl, rfl⟩

/-- A group with a joint of the kind HV, VC or HVC at `a` has a whole-group object at `a`. -/
theorem vl_object_orig {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b) :
    ∃ O : Object G.molecule, O.atoms = S ∧ a = O.upper := by
  rcases h with ⟨e, he, X, hX⟩ | h | ⟨e, he, hb, n, _, hn⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩⟩, rfl, rfl⟩
  · exact ⟨⟨S, a, b, .vc h⟩, rfl, rfl⟩
  · exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, rfl, rfl⟩

theorem exists_isDesig {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (h : groupJoint G S = some a) :
    ∃ O : Object G.molecule, IsDesig G S a O := by
  have hs := groupJoint_spec h
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf G S).units = []
    · by_cases hv : (∃ a b, IsHV G.molecule S a b) ∧ ¬ (∃ a b, IsHVC G.molecule S a b)
      · obtain ⟨b0, e0, hpk⟩ := hs.2.2.2.1 hsk hu hv.1 hv.2
        obtain ⟨hends, hvine⟩ := hvPick_spec hpk
        obtain ⟨O, hOa, hOu, hOl, R, hR, hRe⟩ := hv_object_orig hends hvine
        refine ⟨O, hOu.symm, hOa ▸ subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
          (fun sk e h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h), ?_, ?_⟩
        · intro _ _ _ _
          exact ⟨b0, e0, hpk, hOa, hOl, R, hR, hRe⟩
        · intro _ _ _; exact hOa
      · by_cases hvl : ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b
        · obtain ⟨b, hb⟩ := hs.2.2.2.2 hsk hu hvl
          obtain ⟨O, hOa, hOu⟩ := vl_object_orig hb
          exact ⟨O, hOu, hOa ▸ subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
            (fun sk e h => by rw [hsk] at h; cases h), (fun _ h => absurd hu h),
            (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ _ => hOa)⟩
        · obtain ⟨b, hb⟩ := hs.2.2.1 hsk hu
          obtain ⟨O, hO1, hO2, _⟩ := group_object_at hb
          exact ⟨O, hO2, hO1, (fun sk h => by rw [hsk] at h; cases h), (fun sk e h => by rw [hsk] at h; cases h),
            (fun _ h => absurd hu h), (fun _ _ hh hn => absurd ⟨hh, hn⟩ hv), (fun _ _ h => absurd h hvl)⟩
    · obtain ⟨b, hb⟩ := hs.2.1 hsk hu
      exact ⟨⟨S, a, b, .vc hb⟩, rfl, subset_refl _, (fun sk h => by rw [hsk] at h; cases h),
        (fun sk e h => by rw [hsk] at h; cases h), (fun _ _ => ⟨rfl, hb, rfl⟩),
        (fun _ h => absurd h hu), (fun _ h => absurd h hu)⟩
  · have ha : a = sk.a := hs.1 sk hsk
    subst ha
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have hv : IsVC G.molecule S sk.a sk.b := ⟨sk.blockM hb, n, (chain_ofVine (Vine.chainIngredient_spec hI).1)⟩
      refine ⟨⟨S, sk.a, sk.b, .vc hv⟩, rfl, subset_refl _, ?_, ?_, (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h)⟩
      · intro sk' h _
        rw [hsk] at h; cases h
        exact ⟨rfl, hv, rfl⟩
      · intro sk' e' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
    · obtain ⟨n, hn, hI⟩ := sk.chainN e hb
      let R : HyperLikeRealization G.molecule S sk.a sk.b :=
        ⟨e, (sk.blockN e hb).1, ⟨(sk.blockN e hb).2, n, (chain_ofVine (Vine.chainIngredient_spec hI).1)⟩⟩
      refine ⟨⟨S, sk.a, sk.b, .hyper R⟩, rfl, subset_refl _, ?_, ?_, (fun h => by rw [hsk] at h; cases h),
        (fun h => by rw [hsk] at h; cases h), (fun h => by rw [hsk] at h; cases h)⟩
      · intro sk' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
      · intro sk' e' h he'
        rw [hsk] at h; cases h
        rw [hb] at he'; cases he'
        exact ⟨rfl, R, rfl, rfl⟩

/-- **The designated object of a group** (a function of the original garden and the group only). -/
@[expose] noncomputable def designatedObject (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (Object G.molecule) := by
  classical
  exact if h : ∃ a, groupJoint G S = some a ∧ ∃ O, IsDesig G S a O then some h.choose_spec.2.choose else none

theorem designatedObject_spec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧ IsDesig G S a O := by
  classical
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  have h : ∃ a, groupJoint G S = some a ∧ ∃ O, IsDesig G S a O := ⟨a, ha, exists_isDesig ha⟩
  refine ⟨h.choose, h.choose_spec.2.choose, h.choose_spec.1, ?_, h.choose_spec.2.choose_spec⟩
  unfold designatedObject
  rw [dif_pos h]

theorem designatedObject_isDesig {S : Finset (GBranch G.tree)} {O : Object G.molecule}
    (h : designatedObject G S = some O) : ∃ a, groupJoint G S = some a ∧ IsDesig G S a O := by
  classical
  unfold designatedObject at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h
    exact ⟨hex.choose, hex.choose_spec.1, h ▸ hex.choose_spec.2.choose_spec⟩

/-! ### The pair inside the designated object (non-hinge entries) -/

/-- An out/in pair of darts of the original garden inside the designated object, at its first joint. -/
@[expose] def IntSpec (G : Garden w) (S : Finset (GBranch G.tree)) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧ (a = O.upper ∨ a = O.lower) ∧
    TripleAt G a p.1 p.2 ∧ O.ContainsDart p.1 ∧ O.ContainsDart p.2

theorem exists_intSpec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ p, IntSpec G S p := by
  obtain ⟨a, O, ha, hO, hd⟩ := designatedObject_spec hS
  obtain ⟨x, y, hT, hx, hy⟩ := objectJoint_pair O (Or.inl hd.1)
  exact ⟨(x, y), a, O, ha, hO, Or.inl hd.1, hT, hx, hy⟩

/-- **The pair of the group in the original garden, chosen once and independently of `σ`.** -/
@[expose] noncomputable def intPairOrig (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GardenDart G × GardenDart G) := by
  classical exact if h : ∃ p, IntSpec G S p then some h.choose else none

theorem intPairOrig_spec {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ p, intPairOrig G S = some p ∧ IntSpec G S p := by
  classical
  have h := exists_intSpec hS
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold intPairOrig
  rw [dif_pos h]

/-! ### The pair at a merged first joint (hinge entries) -/

section run
variable {V D' : Type*} [DecidableEq V] [Fintype D'] [DecidableEq D'] {N : Molecule V D'}

/-- `ext_pair_run` together with `y ≠ mate x`. -/
theorem ext_pair_run' {A L0 : Finset V} {j j' : V} (hAB : N.IsBlock A j j') (hL : L0 ∩ A = {j}) :
    ∃ x y : D', N.atom x = j ∧ N.atom y = j ∧ N.out x = true ∧ N.out y = false ∧ y ≠ N.mate x ∧
      N.atom (N.mate x) ∈ A ∧ N.atom (N.mate y) ∈ A ∧
      N.atom (N.mate x) ∉ L0 ∧ N.atom (N.mate y) ∉ L0 := by
  obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair hAB
  have hc : Mole.GroupConnected N A := WaveTurbulence.LGSpine.groupConnected_of_block hAB
  have hdeg := (block_joint_degrees N hAB).1
  have hnl : ∀ z : D', N.atom z = j → N.InGroup A z → N.atom (N.mate z) ∉ L0 := by
    intro z hz hzA hzL
    have hmem : N.atom (N.mate z) ∈ L0 ∩ A := mem_inter.mpr ⟨hzL, hzA.2⟩
    rw [hL, mem_singleton] at hmem
    exact connected_degree_two_no_loop N hc hAB.2.1 hAB.2.2.1 (Ne.symm hAB.2.2.2.1) hdeg hz hmem
  exact ⟨x, y, hx, hy, hxo, hyo, hne, hxA.2, hyA.2, hnl x hx hxA, hnl y hy hyA⟩

end run

/-- The pair used when the first joint of the group is merged into a spliced unit `u`: an out/in pair of the
original garden at an atom `j` of `u`, external to `u`; for a skipped vine it lies in the skipped vine `A`
(and is not the cut bond), for a whole-group unit `j` is a joint of the unit. -/
@[expose] def HingeSpec (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (p : GardenDart G × GardenDart G) : Prop :=
  ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms ∧ ∃ j ∈ u.atoms,
    TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
    (∀ sk, (groupUnitsOf G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
      G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
      ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
    ((groupUnitsOf G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower))

/-- The pair of the skipped vine in an adjoint, transferred to the molecule. -/
theorem run_pair_erase {V D' : Type*} [DecidableEq V] [Fintype D'] [DecidableEq D'] (M : Molecule V D') (e : D')
    {A R : Finset V} {j j' : V} (hAB : (eraseBond M e).IsBlock A j j') (hR : R ∩ A = {j}) :
    ∃ x y : D', M.atom x = j ∧ M.atom y = j ∧ M.out x = true ∧ M.out y = false ∧ y ≠ M.mate x ∧
      M.atom (M.mate x) ∈ A ∧ M.atom (M.mate y) ∈ A ∧ M.atom (M.mate x) ∉ R ∧ M.atom (M.mate y) ∉ R ∧
      x ≠ e ∧ x ≠ M.mate e ∧ y ≠ e ∧ y ≠ M.mate e := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hne, hxA, hyA, hxn, hyn⟩ := ext_pair_run' hAB hR
  refine ⟨x.1, y.1, hx, hy, hxo, hyo, fun h => hne (Subtype.ext h), hxA, hyA, hxn, hyn, x.2.1, x.2.2, y.2.1, y.2.2⟩

theorem hingeSpec_of_run {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    {u : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) (hau : a ∈ u.atoms)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {j : GBranch G.tree} (hjx : j = sk.x ∨ j = sk.y)
    (hjU : j ∈ u.atoms) (x y : GardenDart G) (hx : G.molecule.atom x = j) (hy : G.molecule.atom y = j)
    (hxo : G.molecule.out x = true) (hyo : G.molecule.out y = false) (hne : y ≠ G.molecule.mate x)
    (hxA : G.molecule.atom (G.molecule.mate x) ∈ sk.A) (hyA : G.molecule.atom (G.molecule.mate y) ∈ sk.A)
    (hxn : G.molecule.atom (G.molecule.mate x) ∉ u.atoms) (hyn : G.molecule.atom (G.molecule.mate y) ∉ u.atoms)
    (he : ∀ e, sk.bond = some e → x ≠ e ∧ x ≠ G.molecule.mate e ∧ y ≠ e ∧ y ≠ G.molecule.mate e) :
    ∃ p, HingeSpec G S a p := by
  refine ⟨(x, y), u, hu, hau, j, hjU, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_, ?_, ?_⟩
  · intro h; exact hxn h.2
  · intro h; exact hyn h.2
  · intro sk' h
    rw [hsk] at h; cases h
    exact ⟨hjx, hxA, hyA, fun e hb => he e hb⟩
  · intro h; rw [hsk] at h; cases h

/-- **Existence of the hinge pair.** -/
theorem exists_hingeSpec {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hu : ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms) : ∃ p, HingeSpec G S a p := by
  obtain ⟨u, hu, hau⟩ := hu
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · have hS := (groupUnitsOf G S).noskip_units hsk u hu
    obtain ⟨j, hj, d1, d2, h1, h2, n1, n2, o1, o2⟩ := (groupUnitsOf G S).ext u hu
    have hjU : j ∈ u.atoms := by rcases hj with rfl | rfl; exact u.isBlock.2.1; exact u.isBlock.2.2.1
    have hne : d2 ≠ G.molecule.mate d1 := by
      intro h
      apply n1
      exact ⟨h1 ▸ hjU, by rw [← h, h2]; exact hjU⟩
    refine ⟨(d1, d2), u, hu, hau, j, hjU, ⟨h1, h2, hne, by rw [o1, o2]; simp⟩, n1, n2, ?_, ?_⟩
    · intro sk' h; rw [hsk] at h; cases h
    · intro _; exact ⟨hS, hj⟩
  · have hsu := (groupUnitsOf G S).skip_units sk hsk
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

/-- (R37) Tier 1 of the triple-bond rule: both bonds of the pair lead to the same atom of the original garden. -/
@[expose] def PairSameAtom (G : Garden w) (p : GardenDart G × GardenDart G) : Prop :=
  G.molecule.atom (G.molecule.mate p.1) = G.molecule.atom (G.molecule.mate p.2)

/-- (R37) Tier 2 of the triple-bond rule: both bonds of the pair lead into the same unit of some group of `𝒞`
(so that they lead to one atom of `G_sb` as soon as that unit is spliced). -/
@[expose] def PairSameUnit (G : Garden w) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ S' ∈ maximalGroups G.molecule, ∃ u' ∈ (groupUnitsOf G S').units,
    G.molecule.atom (G.molecule.mate p.1) ∈ u'.atoms ∧ G.molecule.atom (G.molecule.mate p.2) ∈ u'.atoms

/-- (R37) **The chosen hinge pair**: a `HingeSpec` pair that prefers (tier 1) a pair whose two bonds lead to one atom, then
(tier 2) a pair whose two bonds lead into one unit.  Both criteria refer to the ORIGINAL garden only (no `σ`). -/
@[expose] def HingeBest (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (p : GardenDart G × GardenDart G) : Prop :=
  HingeSpec G S a p ∧
    ((∃ p', HingeSpec G S a p' ∧ PairSameAtom G p') → PairSameAtom G p) ∧
    ((∃ p', HingeSpec G S a p' ∧ PairSameUnit G p') → PairSameAtom G p ∨ PairSameUnit G p)

theorem exists_hingeBest {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hu : ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms) : ∃ p, HingeBest G S a p := by
  classical
  obtain ⟨p0, hp0⟩ := exists_hingeSpec hu
  by_cases h1 : ∃ p', HingeSpec G S a p' ∧ PairSameAtom G p'
  · obtain ⟨p', hp', ht⟩ := h1
    exact ⟨p', hp', fun _ => ht, fun _ => Or.inl ht⟩
  · by_cases h2 : ∃ p', HingeSpec G S a p' ∧ PairSameUnit G p'
    · obtain ⟨p', hp', ht⟩ := h2
      exact ⟨p', hp', fun h => absurd h h1, fun _ => Or.inr ht⟩
    · exact ⟨p0, hp0, fun h => absurd h h1, fun h => absurd h h2⟩

/-- **The pair of the group at a merged first joint, chosen once and independently of `σ`** (R37: `HingeBest`, so that when
a hinge has a triple bond the chosen joint is the one whose external pair lies in the triple bond). -/
@[expose] noncomputable def hingeOrigPair (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GardenDart G × GardenDart G) := by
  classical exact if h : ∃ p a, groupJoint G S = some a ∧ HingeBest G S a p then some h.choose else none

theorem hingeOrigPair_best {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (ha : groupJoint G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair G S = some p ∧ HingeBest G S a p := by
  classical
  obtain ⟨p0, hp0⟩ := exists_hingeBest hu
  have h : ∃ p a, groupJoint G S = some a ∧ HingeBest G S a p := ⟨p0, a, ha, hp0⟩
  refine ⟨h.choose, ?_, ?_⟩
  · unfold hingeOrigPair; rw [dif_pos h]
  · obtain ⟨a', ha', hs⟩ := h.choose_spec
    rw [ha] at ha'
    cases ha'
    exact hs

theorem hingeOrigPair_spec {S : Finset (GBranch G.tree)} {a : GBranch G.tree} (ha : groupJoint G S = some a)
    (hu : ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms) :
    ∃ p, hingeOrigPair G S = some p ∧ HingeSpec G S a p := by
  obtain ⟨p, hp, hb⟩ := hingeOrigPair_best ha hu
  exact ⟨p, hp, hb.1⟩

end WaveTurbulence.RedSplice
