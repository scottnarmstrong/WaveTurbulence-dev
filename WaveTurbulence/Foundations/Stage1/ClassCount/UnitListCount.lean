/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineUnitSelectedMK
import Mathlib.Tactic

/-!
# B2d CLASSCOUNT-MK: the number of unit lists of a skeleton

At a marking `Mk` the units of a marked group are its runs, chosen by `Classical.choice`, so the list
`unitBlocks G σ Mk` is not a function of `σ` and of the marked ingredients alone.  It is nevertheless one of few lists:
every unit of every `unitBlocks G σ Mk` is the union of a segment of a fixed spine of its group (`groupSpine`, by the
walk lemma `Spine.walkMK`), so it is determined by its two joints and the position and length of that segment
(`unitCode`, injective on units: `eq_of_unitCode_eq`).  Hence (`card_unitBlockLists_le`) the lists `unitBlocks G σ Mk` of
length `≤ r` (over all `σ` and `Mk`) number at most `(r + 1) (n + 2)^{4r}`, `n` the number of atoms.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine

section spine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A spine has fewer members than atoms. -/
theorem spine_length_lt_card {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    L.length < U.card := by
  induction h with
  | @one T a b hv =>
    obtain ⟨ha, hb, hab⟩ := (Spine.one hv).ends
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
    obtain ⟨hb, hc, hbc⟩ := (Spine.one hT).ends
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
theorem mid_eq_of_length_eq {α : Type*} {P R Q P' R' Q' : List α} (h : P ++ R ++ Q = P' ++ R' ++ Q')
    (hP : P.length = P'.length) (hR : R.length = R'.length) : R = R' := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨-, h2⟩ := List.append_inj h hP
  exact (List.append_inj h2 hR).1

/-- A list is determined by its image under a map injective on its elements. -/
theorem list_eq_of_map_eq {α β : Type*} (f : α → β) :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, ∀ b ∈ l2, f a = f b → a = b) → l1.map f = l2.map f → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l1, b :: l2, hf, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a (by simp) b (by simp) h.1,
      list_eq_of_map_eq f (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])) h.2]

variable {w : ℕ}

/-- A CL block is determined by its atoms and its two joints. -/
theorem clBlock_ext {G : Garden w} {u v : CLBlock G} (ha : u.atoms = v.atoms) (hu : u.upper = v.upper)
    (hl : u.lower = v.lower) : u = v := by
  cases u; cases v
  simp only at ha hu hl
  subst ha hu hl
  rfl

/-- `L` is a spine of the group `S` (in the garden molecule or in an adjoint) listing every ingredient of `S`. -/
def GroupSpine (G : Garden w) (S : Finset (GBranch G.tree))
    (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) : Prop :=
  (∃ (D' : Type) (_ : Fintype D') (_ : DecidableEq D') (N : Molecule (GBranch G.tree) D') (a b : GBranch G.tree),
    Spine N L S a b) ∧
  ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L

/-- A group with an ingredient (a VC or an HVC) has a spine listing all its ingredients. -/
theorem exists_groupSpine {G : Garden w} {S X : Finset (GBranch G.tree)} (hX : IsIngredient G.molecule S X) :
    ∃ L, GroupSpine G S L := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  rcases hX with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · obtain ⟨L, hs⟩ := Spine.of_chain (chainIngredient_spec hI).1
    exact ⟨L, ⟨_, inferInstance, inferInstance, G.molecule, a, b, hs⟩, fun T hT => isIngredient_vc hM hB hs hT⟩
  · obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (chainIngredient_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    exact ⟨L, ⟨_, inferInstance, inferInstance, _, a, b, hs⟩,
      fun T hT => isIngredient_hvc hM hends hBe hs hlen2 hT⟩

/-- The fixed spine of a group (empty if the group has no spine). -/
noncomputable def groupSpine (G : Garden w) (S : Finset (GBranch G.tree)) :
    List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if h : ∃ L, GroupSpine G S L then h.choose else []

theorem groupSpine_spec {G : Garden w} {S : Finset (GBranch G.tree)} (h : ∃ L, GroupSpine G S L) :
    GroupSpine G S (groupSpine G S) := by
  classical
  unfold groupSpine
  rw [dif_pos h]
  exact h.choose_spec

/-- The fixed spine of a group has fewer members than atoms. -/
theorem groupSpine_length_lt {G : Garden w} {S : Finset (GBranch G.tree)} (h : ∃ L, GroupSpine G S L) :
    (groupSpine G S).length < S.card := by
  obtain ⟨⟨D', _, _, N, a, b, hs⟩, -⟩ := groupSpine_spec h
  exact spine_length_lt_card hs

/-- `u` is the union of the segment of the fixed spine of its group at position `k` and of length `m`. -/
def SegCode (G : Garden w) (u : CLBlock G) (k m : ℕ) : Prop :=
  ∃ S ∈ maximalGroups G.molecule, u.upper ∈ S ∧ ∃ P R Q, groupSpine G S = P ++ R ++ Q ∧ P.length = k ∧
    R.length = m ∧ ∀ v, v ∈ u.atoms ↔ ∃ t ∈ R, v ∈ t.1

/-- **Every unit of every `unitBlocks G σ Mk` is a segment of the fixed spine of its group.** -/
theorem segCode_of_mem {G : Garden w} {σ : Prescription G} {Mk : Set (CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) :
    ∃ k m, k < Fintype.card (GBranch G.tree) + 1 ∧ m < Fintype.card (GBranch G.tree) + 1 ∧ SegCode G u k m := by
  classical
  obtain ⟨S, hS, -, hum⟩ := mem_unitBlocksMk.mp hu
  obtain ⟨Lu, hsu, hsel⟩ := VineA.groupUnitsMk_selected_spine hS hum
  have hsub : u.atoms ⊆ S := groupUnitsMk_sub hum
  -- the group has an ingredient (a member of the unit's spine), hence a fixed spine
  have hLu : Lu ≠ [] := by
    rcases hsu.inv with ⟨T, h0, -⟩ | ⟨L', U', T, b, h0, -⟩ <;> simp [h0]
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil Lu hLu
  obtain ⟨c0, -, -, hc0, -⟩ := hsel t0 ht0
  have hex : ∃ L, GroupSpine G S L := exists_groupSpine hc0
  obtain ⟨⟨D', _, _, N, a, b, hs⟩, hmemb⟩ := groupSpine_spec hex
  have hmem : ∀ t ∈ Lu, ∃ t0 ∈ groupSpine G S, t0.1 = t.1 := by
    intro t ht
    obtain ⟨c, -, -, hci, hct⟩ := hsel t ht
    obtain ⟨p, q, h | h⟩ := hmemb _ hci
    · exact ⟨_, h, hct⟩
    · exact ⟨_, h, hct⟩
  obtain ⟨P, R, Q, hL, -, hiff, -⟩ := hs.walkMK hsu hmem
  have hlen := groupSpine_length_lt hex
  have hcard : S.card ≤ Fintype.card (GBranch G.tree) := Finset.card_le_univ S
  have hPR : P.length + R.length ≤ (groupSpine G S).length := by
    rw [hL]; simp only [List.length_append]; omega
  refine ⟨P.length, R.length, by omega, by omega, S, hS, hsub u.isBlock.2.1, P, R, Q, hL, rfl, rfl, hiff⟩

/-- **Units with the same code are equal.** -/
theorem eq_of_segCode {G : Garden w} {u u' : CLBlock G} {k m : ℕ} (h : SegCode G u k m) (h' : SegCode G u' k m)
    (hup : u.upper = u'.upper) (hlo : u.lower = u'.lower) : u = u' := by
  obtain ⟨S, hS, huS, P, R, Q, hL, hP, hR, hiff⟩ := h
  obtain ⟨S', hS', huS', P', R', Q', hL', hP', hR', hiff'⟩ := h'
  have hSS : S = S' := by
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint' (Mole.garden_isMolecule G) hS hS' hne) huS (hup ▸ huS')
  subst hSS
  have hRR : R = R' := mid_eq_of_length_eq (hL.symm.trans hL') (hP.trans hP'.symm) (hR.trans hR'.symm)
  subst hRR
  refine clBlock_ext ?_ hup hlo
  ext v
  rw [hiff v, hiff' v]

/-- The code of a unit: its joints and the position and length of its segment. -/
noncomputable def unitCode (G : Garden w) (u : CLBlock G) :
    GBranch G.tree × GBranch G.tree × Fin (Fintype.card (GBranch G.tree) + 1) ×
      Fin (Fintype.card (GBranch G.tree) + 1) := by
  classical
  exact if h : ∃ km : Fin (Fintype.card (GBranch G.tree) + 1) × Fin (Fintype.card (GBranch G.tree) + 1),
      SegCode G u km.1 km.2 then (u.upper, u.lower, h.choose) else (u.upper, u.lower, 0, 0)

theorem unitCode_spec {G : Garden w} {σ : Prescription G} {Mk : Set (CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) :
    (unitCode G u).1 = u.upper ∧ (unitCode G u).2.1 = u.lower ∧
      SegCode G u (unitCode G u).2.2.1 (unitCode G u).2.2.2 := by
  classical
  obtain ⟨k, m, hk, hm, hc⟩ := segCode_of_mem hu
  have h : ∃ km : Fin (Fintype.card (GBranch G.tree) + 1) × Fin (Fintype.card (GBranch G.tree) + 1),
      SegCode G u km.1 km.2 := ⟨(⟨k, hk⟩, ⟨m, hm⟩), hc⟩
  unfold unitCode
  rw [dif_pos h]
  exact ⟨rfl, rfl, h.choose_spec⟩

/-- **The code is injective on units.** -/
theorem eq_of_unitCode_eq {G : Garden w} {σ σ' : Prescription G} {Mk Mk' : Set (CLVine G)} {u u' : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) (hu' : u' ∈ unitBlocks G σ' Mk') (h : unitCode G u = unitCode G u') : u = u' := by
  obtain ⟨h1, h2, h3⟩ := unitCode_spec hu
  obtain ⟨h1', h2', h3'⟩ := unitCode_spec hu'
  rw [h] at h1 h2 h3
  exact eq_of_segCode h3 h3' (h1.symm.trans h1') (h2.symm.trans h2')

/-- Lists of length `≤ r` over a finite type, as a finset. -/
noncomputable def codeListsLe (K : Type*) [Fintype K] (r : ℕ) : Finset (List K) := by
  classical
  exact (Finset.range (r + 1)).biUnion fun k => (Finset.univ : Finset (Fin k → K)).image List.ofFn

theorem mem_codeListsLe {K : Type*} [Fintype K] {r : ℕ} {l : List K} (h : l.length ≤ r) : l ∈ codeListsLe K r := by
  classical
  unfold codeListsLe
  refine Finset.mem_biUnion.mpr ⟨l.length, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

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

/-- **The number of unit lists.**  A finite set of lists, each of length `≤ r` and each `unitBlocks G σ Mk` for some
prescription `σ` and marked set `Mk`, has at most `(r + 1) (n + 2)^{4r}` elements (`n` the number of atoms). -/
theorem card_unitBlockLists_le (G : Garden w) (r : ℕ) (X : Finset (List (CLBlock G)))
    (hX : ∀ U ∈ X, (∃ (σ : Prescription G) (Mk : Set (CLVine G)), U = unitBlocks G σ Mk) ∧ U.length ≤ r) :
    X.card ≤ (r + 1) * (Fintype.card (GBranch G.tree) + 2) ^ (4 * r) := by
  classical
  set n := Fintype.card (GBranch G.tree) with hn
  set K := GBranch G.tree × GBranch G.tree × Fin (n + 1) × Fin (n + 1)
  have hinj : Set.InjOn (fun U : List (CLBlock G) => U.map (unitCode G)) X := by
    intro U hU U' hU' he
    obtain ⟨⟨σ, Mk, rfl⟩, -⟩ := hX U hU
    obtain ⟨⟨σ', Mk', rfl⟩, -⟩ := hX U' hU'
    exact list_eq_of_map_eq (unitCode G) (fun a ha b hb hab => eq_of_unitCode_eq ha hb hab) he
  have h1 : X.card = (X.image fun U => U.map (unitCode G)).card := (Finset.card_image_of_injOn hinj).symm
  have h2 : X.image (fun U => U.map (unitCode G)) ⊆ codeListsLe K r := by
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

end WaveTurbulence.ClassCount
