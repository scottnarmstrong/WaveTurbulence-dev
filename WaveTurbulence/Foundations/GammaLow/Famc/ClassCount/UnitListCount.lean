/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitListCount` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitListCount
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit


/-!
# B2d CLASSCOUNT-MK: the number of unit lists of a skeleton

At a marking `Mk` the units of a marked group are its runs, chosen by `Classical.choice`, so the list
`Fama.unitBlocks γ G σ Mk` is not a function of `σ` and of the marked ingredients alone.  It is nevertheless one of few lists:
every unit of every `Fama.unitBlocks γ G σ Mk` is the union of a segment of a fixed spine of its group (`groupSpine`, by the
walk lemma `Fama.Spine.walkMK`), so it is determined by its two Fama.joints and the position and length of that segment
(`unitCode`, injective on units: `eq_of_unitCode_eq`).  Hence (`card_unitBlockLists_le`) the lists `Fama.unitBlocks γ G σ Mk` of
length `≤ r` (over all `σ` and `Mk`) number at most `(r + 1) (n + 2)^{4r}`, `n` the number of atoms.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount

section spine
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- A spine has fewer members than atoms. -/
theorem spine_length_lt_card {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Fama.Spine γ M L U a b) :
    L.length < U.card := by
  induction h with
  | @one T a b hv =>
    obtain ⟨ha, hb, hab⟩ := (Fama.Spine.one hv).ends
    have : ({a, b} : Finset V) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hab] at h2
    simp only [List.length_singleton]
    omega
  | @snoc L U T a b c hL hT hi hne ih =>
    obtain ⟨hb, hc, hbc⟩ := (Fama.Spine.one hT).ends
    have hcU : c ∉ U := by
      intro hcU
      have : c ∈ U ∩ T := Finset.mem_inter.mpr ⟨hcU, hc⟩
      rw [hi, Finset.mem_singleton] at this
      exact hbc this.symm
    have hsub : insert c U ⊆ U ∪ T := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ hc
      · exact Finset.mem_union_left _ hx
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hcU] at h2
    simp only [List.length_append, List.length_singleton]
    omega

end spine

/-- Two decompositions `P ++ R ++ Q` of one list with the same lengths of `P` and of `R` have the same `R`. -/
theorem list_eq_of_map_eq {α β : Type*} (f : α → β) :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, ∀ b ∈ l2, f a = f b → a = b) → l1.map f = l2.map f → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l1, b :: l2, hf, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a (by simp) b (by simp) h.1,
      list_eq_of_map_eq f (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])) h.2]

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- A CL block is determined by its atoms and its two Fama.joints. -/
def GroupSpine (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree))
    (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) : Prop :=
  (∃ (D' : Type) (_ : Fintype D') (_ : DecidableEq D') (N : Molecule (GBranch G.tree) D') (a b : GBranch G.tree),
    Fama.Spine γ N L S a b) ∧
  ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L

/-- A group with an ingredient (a VC or an HVC) has a spine listing all its ingredients. -/
theorem exists_groupSpine {G : Garden w} {S X : Finset (GBranch G.tree)} (hX : IsIngredientG γ G.molecule S X) :
    ∃ L, GroupSpine γ G S L := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  rcases hX with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · obtain ⟨L, hs⟩ := Fama.Spine.of_chain (chainIngredientG_spec hI).1
    exact ⟨L, ⟨_, inferInstance, inferInstance, G.molecule, a, b, hs⟩, fun T hT => Fama.isIngredient_vc hM hB hs hT⟩
  · obtain ⟨L, hs, hlen⟩ := Fama.Spine.of_chain_len (chainIngredientG_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    exact ⟨L, ⟨_, inferInstance, inferInstance, _, a, b, hs⟩,
      fun T hT => Fama.isIngredient_hvc hM hends hBe hs hlen2 hT⟩

/-- The fixed spine of a group (empty if the group has no spine). -/
noncomputable def groupSpine (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) :
    List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if h : ∃ L, GroupSpine γ G S L then h.choose else []

theorem groupSpine_spec {G : Garden w} {S : Finset (GBranch G.tree)} (h : ∃ L, GroupSpine γ G S L) :
    GroupSpine γ G S (groupSpine γ G S) := by
  classical
  unfold groupSpine
  rw [dif_pos h]
  exact h.choose_spec

/-- The fixed spine of a group has fewer members than atoms. -/
theorem groupSpine_length_lt {G : Garden w} {S : Finset (GBranch G.tree)} (h : ∃ L, GroupSpine γ G S L) :
    (groupSpine γ G S).length < S.card := by
  obtain ⟨⟨D', _, _, N, a, b, hs⟩, -⟩ := groupSpine_spec h
  exact spine_length_lt_card hs

/-- `u` is the union of the segment of the fixed spine of its group at position `k` and of length `m`. -/
def SegCode (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (u : CLBlock G) (k m : ℕ) : Prop :=
  ∃ S ∈ maximalGroupsG γ G.molecule, u.upper ∈ S ∧ ∃ P R Q, groupSpine γ G S = P ++ R ++ Q ∧ P.length = k ∧
    R.length = m ∧ ∀ v, v ∈ u.atoms ↔ ∃ t ∈ R, v ∈ t.1

/-- **Every unit of every `Fama.unitBlocks γ G σ Mk` is a segment of the fixed spine of its group.** -/
theorem segCode_of_mem {G : Garden w} {σ : Prescription G} {Mk : Set (CLVineG γ G)} {u : CLBlock G}
    (hu : u ∈ Fama.unitBlocks γ G σ Mk) :
    ∃ k m, k < Fintype.card (GBranch G.tree) + 1 ∧ m < Fintype.card (GBranch G.tree) + 1 ∧ SegCode γ G u k m := by
  classical
  obtain ⟨S, hS, -, hum⟩ := Fama.mem_unitBlocksMk.mp hu
  obtain ⟨Lu, hsu, hsel⟩ := VineA.groupUnitsMk_selected_spine hS hum
  have hsub : u.atoms ⊆ S := Fama.groupUnitsMk_sub hum
  -- the group has an ingredient (a member of the unit's spine), hence a fixed spine
  have hLu : Lu ≠ [] := by
    rcases hsu.inv with ⟨T, h0, -⟩ | ⟨L', U', T, b, h0, -⟩ <;> simp [h0]
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil Lu hLu
  obtain ⟨c0, -, -, hc0, -⟩ := hsel t0 ht0
  have hex : ∃ L, GroupSpine γ G S L := exists_groupSpine hc0
  obtain ⟨⟨D', _, _, N, a, b, hs⟩, hmemb⟩ := groupSpine_spec hex
  have hmem : ∀ t ∈ Lu, ∃ t0 ∈ groupSpine γ G S, t0.1 = t.1 := by
    intro t ht
    obtain ⟨c, -, -, hci, hct⟩ := hsel t ht
    obtain ⟨p, q, h | h⟩ := hmemb _ hci
    · exact ⟨_, h, hct⟩
    · exact ⟨_, h, hct⟩
  obtain ⟨P, R, Q, hL, -, hiff, -⟩ := (SpineG.walkMK hs) hsu hmem
  have hlen := groupSpine_length_lt hex
  have hcard : S.card ≤ Fintype.card (GBranch G.tree) := Finset.card_le_univ S
  have hPR : P.length + R.length ≤ (groupSpine γ G S).length := by
    rw [hL]; simp only [List.length_append]; omega
  refine ⟨P.length, R.length, by omega, by omega, S, hS, hsub u.isBlock.2.1, P, R, Q, hL, rfl, rfl, hiff⟩

/-- **Units with the same code are equal.** -/
theorem eq_of_segCode {G : Garden w} {u u' : CLBlock G} {k m : ℕ} (h : SegCode γ G u k m) (h' : SegCode γ G u' k m)
    (hup : u.upper = u'.upper) (hlo : u.lower = u'.lower) : u = u' := by
  obtain ⟨S, hS, huS, P, R, Q, hL, hP, hR, hiff⟩ := h
  obtain ⟨S', hS', huS', P', R', Q', hL', hP', hR', hiff'⟩ := h'
  have hSS : S = S' := by
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.groups_disjoint' (Mole.garden_isMolecule G) hS hS' hne) huS (hup ▸ huS')
  subst hSS
  have hRR : R = R' := mid_eq_of_length_eq (hL.symm.trans hL') (hP.trans hP'.symm) (hR.trans hR'.symm)
  subst hRR
  refine clBlock_ext ?_ hup hlo
  ext v
  rw [hiff v, hiff' v]

/-- The code of a unit: its Fama.joints and the position and length of its segment. -/
noncomputable def unitCode (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (u : CLBlock G) :
    GBranch G.tree × GBranch G.tree × Fin (Fintype.card (GBranch G.tree) + 1) ×
      Fin (Fintype.card (GBranch G.tree) + 1) := by
  classical
  exact if h : ∃ km : Fin (Fintype.card (GBranch G.tree) + 1) × Fin (Fintype.card (GBranch G.tree) + 1),
      SegCode γ G u km.1 km.2 then (u.upper, u.lower, h.choose) else (u.upper, u.lower, 0, 0)

theorem unitCode_spec {G : Garden w} {σ : Prescription G} {Mk : Set (CLVineG γ G)} {u : CLBlock G}
    (hu : u ∈ Fama.unitBlocks γ G σ Mk) :
    (unitCode γ G u).1 = u.upper ∧ (unitCode γ G u).2.1 = u.lower ∧
      SegCode γ G u (unitCode γ G u).2.2.1 (unitCode γ G u).2.2.2 := by
  classical
  obtain ⟨k, m, hk, hm, hc⟩ := segCode_of_mem hu
  have h : ∃ km : Fin (Fintype.card (GBranch G.tree) + 1) × Fin (Fintype.card (GBranch G.tree) + 1),
      SegCode γ G u km.1 km.2 := ⟨(⟨k, hk⟩, ⟨m, hm⟩), hc⟩
  unfold unitCode
  rw [dif_pos h]
  exact ⟨rfl, rfl, h.choose_spec⟩

/-- **The code is injective on units.** -/
theorem eq_of_unitCode_eq {G : Garden w} {σ σ' : Prescription G} {Mk Mk' : Set (CLVineG γ G)} {u u' : CLBlock G}
    (hu : u ∈ Fama.unitBlocks γ G σ Mk) (hu' : u' ∈ Fama.unitBlocks γ G σ' Mk') (h : unitCode γ G u = unitCode γ G u') : u = u' := by
  obtain ⟨h1, h2, h3⟩ := unitCode_spec hu
  obtain ⟨h1', h2', h3'⟩ := unitCode_spec hu'
  rw [h] at h1 h2 h3
  exact eq_of_segCode h3 h3' (h1.symm.trans h1') (h2.symm.trans h2')

/-- Lists of length `≤ r` over a finite type, as a finset. -/


theorem card_codeListsLe_le (K : Type*) [Fintype K] (r : ℕ) :
    (codeListsLe K r).card ≤ (r + 1) * (Fintype.card K + 1) ^ r := by
  classical
  unfold codeListsLe
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ Finset.range (r + 1), ((Finset.univ : Finset (Fin k → K)).image List.ofFn).card
      ≤ ∑ k ∈ Finset.range (r + 1), (Fintype.card K + 1) ^ r := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        calc Fintype.card K ^ k ≤ (Fintype.card K + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
          _ ≤ (Fintype.card K + 1) ^ r :=
              Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (r + 1) * (Fintype.card K + 1) ^ r := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The number of unit lists.**  A finite set of lists, each of length `≤ r` and each `Fama.unitBlocks γ G σ Mk` for some
prescription `σ` and marked set `Mk`, has at most `(r + 1) (n + 2)^{4r}` elements (`n` the number of atoms). -/
theorem card_unitBlockLists_le (G : Garden w) (r : ℕ) (X : Finset (List (CLBlock G)))
    (hX : ∀ U ∈ X, (∃ (σ : Prescription G) (Mk : Set (CLVineG γ G)), U = Fama.unitBlocks γ G σ Mk) ∧ U.length ≤ r) :
    X.card ≤ (r + 1) * (Fintype.card (GBranch G.tree) + 2) ^ (4 * r) := by
  classical
  set n := Fintype.card (GBranch G.tree) with hn
  set K := GBranch G.tree × GBranch G.tree × Fin (n + 1) × Fin (n + 1)
  have hinj : Set.InjOn (fun U : List (CLBlock G) => U.map (unitCode γ G)) X := by
    intro U hU U' hU' he
    obtain ⟨⟨σ, Mk, rfl⟩, -⟩ := hX U hU
    obtain ⟨⟨σ', Mk', rfl⟩, -⟩ := hX U' hU'
    exact list_eq_of_map_eq (unitCode γ G) (fun a ha b hb hab => eq_of_unitCode_eq ha hb hab) he
  have h1 : X.card = (X.image fun U => U.map (unitCode γ G)).card := (Finset.card_image_of_injOn hinj).symm
  have h2 : X.image (fun U => U.map (unitCode γ G)) ⊆ codeListsLe K r := by
    intro l hl
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hl
    exact mem_codeListsLe (by rw [List.length_map]; exact (hX U hU).2)
  have h3 := (Finset.card_le_card h2).trans (card_codeListsLe_le K r)
  have hK : Fintype.card K + 1 ≤ (n + 2) ^ 4 := by
    simp only [K, Fintype.card_prod, Fintype.card_fin]
    rw [← hn]
    have : n * (n * ((n + 1) * (n + 1))) + 1 ≤ (n + 2) ^ 4 := by nlinarith
    exact this
  rw [h1]
  refine h3.trans (Nat.mul_le_mul_left _ ?_)
  rw [pow_mul]
  rw [show (n + 2) ^ 4 = (n + 2) ^ 4 from rfl]
  calc (Fintype.card K + 1) ^ r ≤ ((n + 2) ^ 4) ^ r := Nat.pow_le_pow_left hK r
    _ = ((n + 2) ^ 4) ^ r := rfl

end WaveTurbulence.GammaLow.Famc.ClassCount
