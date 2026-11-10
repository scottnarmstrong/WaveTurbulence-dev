/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Inst.All
public import WaveTurbulence.Foundations.TVine.Checker.SubRemove

/-!
# From a T-vine to a checked instance

* `length_genB`: the generated block has `8 + 4 (k + k')` bond copies; with the degree sum
  (`four_mul_card_eq`) a T-vine isomorphic to `genB p j` has exactly `5 + 2 (k + k')` atoms (`card_eq_of_iso`);
* `mem_pairsOf`, `mem_cparams`, `mem_jparams`, `mem_instList`: every valid parameter pair with `k + k' ≤ 4` is an
  instance;
* `exists_inst`: a T-vine whose generation parameters have `k + k' ≤ 4` is isomorphic to an instance of
  `instList` (joints to the joint names); `exists_inst_of_card` (at most 13 atoms), `exists_inst_of_del` (`D ≤ 1`);
* `checkInst_facts`, and the consequences used by the base statements (`deg ≤ 4`, ends `< 32`, no loop).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

universe u

/-! ## Lengths -/

theorem length_eraseOne {es : Edges} {x y : ℕ} (h : mult es x y ≠ 0) : (eraseOne es x y).length + 1 = es.length := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [eraseOne]
    split <;> rename_i he
    · simp
    · rw [mult_cons, if_neg he, zero_add] at h
      simp only [List.length_cons]
      have := ih h
      omega

theorem length_z1 {es : Edges} {x y : ℕ} (h : mult es x y ≠ 0) (a b : ℕ) :
    (z1 es x y a b).length = es.length + 4 := by
  have := length_eraseOne h
  simp only [z1, List.length_append, List.length_cons, List.length_nil]
  omega

theorem mult_z1_new (es : Edges) (x y a b : ℕ) : mult (z1 es x y a b) a b ≠ 0 := by
  have h : isPair a b (a, b) = true := (isPair_iff a b (a, b)).mpr (Or.inl ⟨rfl, rfl⟩)
  simp only [z1, mult_append, mult_cons, h, if_true, mult_nil]
  omega

theorem length_ladder : ∀ (k : ℕ) (es : Edges) (x y N : ℕ), mult es x y ≠ 0 →
    (ladder k es x y N).length = es.length + 4 * k
  | 0, es, x, y, N, _ => by simp [ladder]
  | k + 1, es, x, y, N, h => by
    rw [ladder, length_ladder k _ N (N + 1) (N + 4) (mult_z1_new es x y N (N + 1)), length_z1 h]
    omega

theorem length_gen1 (k : ℕ) : (gen1 k).length = 6 + 4 * k := by
  rw [gen1, length_ladder k tri 0 1 3 (by decide)]; rfl

theorem length_genC {p : CParam} (hp : p.Valid) : (genC p).length = 6 + 4 * (p.k + p.k₂) := by
  rcases p with ⟨k, _ | ⟨x, y, k'⟩⟩
  · simp [genC, CParam.k₂, length_gen1]
  · simp only [CParam.Valid] at hp
    simp only [genC, CParam.k₂]
    rw [length_ladder k' _ x y 5 hp.2.2.2.1, length_gen1]
    omega

theorem length_genB {p : CParam} (hp : p.Valid) {j : JParam} (hj : j.Valid p) :
    (genB p j).length = 8 + 4 * (p.k + p.k₂) := by
  obtain ⟨hm, -⟩ := hj
  have hC := length_genC hp
  cases j with
  | two x₁ y₁ x₂ y₂ =>
    obtain ⟨-, -, -, hm1, hm2⟩ := hm
    have e1 := length_eraseOne hm1
    have e2 := length_eraseOne hm2
    simp only [genB, placeJ, List.length_append, List.length_cons, List.length_nil]
    omega
  | one x y =>
    obtain ⟨-, hm1⟩ := hm
    have e1 := length_eraseOne hm1
    simp only [genB, placeJ, List.length_append, List.length_cons, List.length_nil]
    omega

/-! ## The degree sum -/

theorem sum_deg (es : Edges) (T : Finset ℕ) (hT : ∀ z, InEnds es z → z ∈ T) :
    ∑ z ∈ T, deg es z = 2 * es.length := by
  induction es with
  | nil => simp [deg]
  | cons e es ih =>
    have hT' : ∀ z, InEnds es z → z ∈ T := fun z hz => by
      obtain ⟨e', he', h⟩ := hz; exact hT z ⟨e', List.mem_cons_of_mem _ he', h⟩
    have h1 : e.1 ∈ T := hT e.1 ⟨e, List.mem_cons_self, Or.inl rfl⟩
    have h2 : e.2 ∈ T := hT e.2 ⟨e, List.mem_cons_self, Or.inr rfl⟩
    simp only [deg_cons, Finset.sum_add_distrib, ih hT', Finset.sum_ite_eq, h1, h2, if_true, List.length_cons]
    ring

variable {V : Type*} [DecidableEq V]

/-- The degree sum of a block isomorphic to a bond list. -/
theorem four_mul_card_eq {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {es : Edges} (φ : Iso G es) :
    4 * G.verts.card = 2 * es.length + 4 := by
  obtain ⟨hj₁, hj₂, hne, hd₁, hd₂, hd, -⟩ := hB
  have hsum : ∑ v ∈ G.verts, Core.deg G v = 2 * es.length := by
    rw [Finset.sum_congr rfl fun v hv => degU_iso φ hv,
      ← Finset.sum_image (f := deg es) (fun x hx y hy h => φ.f_injOn hx hy h)]
    exact sum_deg es _ (fun z hz => Finset.mem_image.mpr ⟨φ.g z, φ.gv z hz, φ.fg z hz⟩)
  have hsum2 : ∑ v ∈ G.verts, (Core.deg G v + (if v = j₁ then 2 else 0) + (if v = j₂ then 2 else 0)) =
      ∑ _v ∈ G.verts, 4 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h1 : v = j₁
    · subst h1; simp [hd₁, hne]
    · by_cases h2 : v = j₂
      · subst h2; simp [hd₂, h1]
      · simp [h1, h2, hd v hv h1 h2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hj₁,
    if_pos hj₂, hsum, Finset.sum_const, smul_eq_mul] at hsum2
  omega

theorem card_eq_of_iso {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {p : CParam} (hp : p.Valid)
    {j : JParam} (hj : j.Valid p) (φ : Iso G (genB p j)) : G.verts.card = 5 + 2 * (p.k + p.k₂) := by
  have := four_mul_card_eq hB φ
  rw [length_genB hp hj] at this
  omega

/-! ## Membership in the family -/

theorem mem_addPair_self (q : ℕ × ℕ) (l : List (ℕ × ℕ)) : q ∈ addPair q l := by
  unfold addPair
  split_ifs with h
  · simpa using h
  · exact List.mem_cons_self

theorem mem_addPair_of_mem {q r : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : r ∈ l) : r ∈ addPair q l := by
  unfold addPair
  split_ifs
  exacts [h, List.mem_cons_of_mem _ h]

theorem mem_pairsOf {es : Edges} {x y : ℕ} (hxy : x < y) (h : mult es x y ≠ 0) : (x, y) ∈ pairsOf es := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    unfold pairsOf at ih ⊢
    simp only [List.foldr_cons]
    rw [mult_cons] at h
    by_cases hP : isPair x y e = true
    · rcases (isPair_iff x y e).mp hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos (by omega)]
        have : e = (x, y) := Prod.ext h1 h2
        rw [this]; exact mem_addPair_self _ _
      · rw [if_neg (by omega), if_pos (by omega), h1, h2]
        exact mem_addPair_self _ _
    · rw [if_neg hP, zero_add] at h
      have := ih h
      split_ifs
      · exact mem_addPair_of_mem this
      · exact mem_addPair_of_mem this
      · exact this

theorem mem_cparams {p : CParam} (hp : p.Valid) (hK : p.k + p.k₂ ≤ 4) : p ∈ cparams := by
  rcases p with ⟨k, _ | ⟨x, y, k'⟩⟩
  · simp only [CParam.k₂] at hK
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
  · simp only [CParam.Valid] at hp
    simp only [CParam.k₂] at hK
    obtain ⟨hk, hk', hxy, hm, hm2⟩ := hp
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), ?_⟩)
    refine List.mem_flatMap.mpr ⟨k', List.mem_range.mpr (by omega), ?_⟩
    rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
    exact List.mem_map.mpr ⟨(x, y), List.mem_filter.mpr ⟨mem_pairsOf hxy hm, by simpa using hm2⟩, rfl⟩

theorem mem_jparams {p : CParam} {j : JParam} (hj : j.Valid p) : j ∈ jparams p := by
  obtain ⟨hm, hle⟩ := hj
  dsimp only [jparams]
  refine List.mem_filter.mpr ⟨?_, hle⟩
  cases j with
  | two x₁ y₁ x₂ y₂ =>
    obtain ⟨h1, h2, hlex, hm1, hm2⟩ := hm
    have hm2' : mult (genC p) x₂ y₂ ≠ 0 := fun h => by
      have := mult_le_of_sublist (eraseOne_sublist (genC p) x₁ y₁) x₂ y₂
      omega
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨(x₁, y₁), mem_pairsOf h1 hm1, ?_⟩)
    refine List.mem_filterMap.mpr ⟨(x₂, y₂), mem_pairsOf h2 hm2', ?_⟩
    rw [if_pos]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨hlex, hm2⟩
  | one x y =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨(x, y), mem_pairsOf hm.1 hm.2, rfl⟩)

theorem mem_instList {p : CParam} {j : JParam} (hp : p.Valid) (hj : j.Valid p) (hK : p.k + p.k₂ ≤ 4) :
    (p, j) ∈ instList :=
  List.mem_flatMap.mpr ⟨p, mem_cparams hp hK, List.mem_map.mpr ⟨j, mem_jparams hj, rfl⟩⟩

/-! ## A T-vine as an instance -/

/-- A T-vine whose generation parameters satisfy `k + k' ≤ 4` is isomorphic to an instance. -/
theorem exists_inst {V : Type u} [DecidableEq V] {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂)
    (hK : ∀ (p : CParam) (j : JParam), p.Valid → j.Valid p → ∀ φ : Iso G (genB p j),
      JointsAt φ j₁ j₂ p.jname → p.k + p.k₂ ≤ 4) :
    ∃ q ∈ instList, ∃ φ : Iso G (genB q.1 q.2), JointsAt φ j₁ j₂ q.1.jname := by
  obtain ⟨p, j, hp, hj, φ, hJ⟩ := generation G j₁ j₂ hT
  exact ⟨(p, j), mem_instList hp hj (hK p j hp hj φ hJ), φ, hJ⟩

/-- **A T-vine with at most 13 atoms is an instance.** -/
theorem exists_inst_of_card {V : Type u} [DecidableEq V] {G : UMultigraph V} {j₁ j₂ : V}
    (hT : IsTVineU G j₁ j₂) (hcard : G.verts.card ≤ 13) :
    ∃ q ∈ instList, ∃ φ : Iso G (genB q.1 q.2), JointsAt φ j₁ j₂ q.1.jname :=
  exists_inst hT fun p j hp hj φ _ => by have := card_eq_of_iso hT.1 hp hj φ; omega

/-! ## The facts of a checked instance -/

theorem checkInst_facts {q : CParam × JParam} (h : checkInst q = true) :
    loopless (genB q.1 q.2) = true ∧ endsLt (genB q.1 q.2) = true ∧
    pieceShapeB (maskOf (genB q.1 q.2)) (genB q.1 q.2) q.1.jname (q.1.jname + 1) = true ∧
    interiorConnB (maskOf (genB q.1 q.2)) (genB q.1 q.2) q.1.jname (q.1.jname + 1) = true ∧
    jointsAvoidB (maskOf (genB q.1 q.2)) (genB q.1 q.2) q.1.jname (q.1.jname + 1) = true ∧
    subFactsB (maskOf (genB q.1 q.2)) (genB q.1 q.2) = true := by
  unfold checkInst at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem lt_of_endsLt {es : Edges} (h : endsLt es = true) {z : ℕ} (hz : InEnds es z) : z < 32 := by
  obtain ⟨e, he, h'⟩ := hz
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rcases h' with rfl | rfl
  exacts [this.1, this.2]

theorem deg_le_four {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) : ∀ v ∈ G.verts, Core.deg G v ≤ 4 := by
  obtain ⟨-, -, -, hd₁, hd₂, hd, -⟩ := hB
  intro v hv
  by_cases h1 : v = j₁
  · subst h1; omega
  · by_cases h2 : v = j₂
    · subst h2; omega
    · have := hd v hv h1 h2; omega

theorem loop_zero {G : UMultigraph V} {es : Edges} (φ : Iso G es) (h : loopless es = true) (v : V) :
    G.mult s(v, v) = 0 := by
  by_cases hv : v ∈ G.verts
  · rw [φ.mult_eq v hv v hv]; exact mult_zero_of_loopless h _
  · by_contra hne
    exact hv (G.supp _ hne v (Sym2.mem_mk_left v v))

theorem subFacts_facts {V' : ℕ} {es : Edges} (h : subFactsB V' es = true) :
    compsOKAll V' es = true ∧ (∀ C ∈ subObjects V' es, C.checkB V' es = true) ∧
      familiesB V' es (subObjects V' es) = true := by
  unfold subFactsB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, List.all_eq_true.mp h.1.2, h.2⟩

end WaveTurbulence.TVine.Checker
