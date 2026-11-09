/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SubCand

/-!
# Every sub-object of `G` is enumerated by `subObjects`

* `CandOf φ U C`: the candidate `C` of the instance is the image of the sub-object `U`;
* `isoCore`: then `U° ≅ C.core es`;
* `exists_cand`: every sub-object of a multigraph of degree ≤ 4 has a candidate in `subObjects (maskOf es) es`
  (its interior is a union of the components of `V ∖ {k₁, k₂}`, `compsOKAll` gives that they partition).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

variable {V : Type*} [DecidableEq V]

/-- `C` is the image of the sub-object `U` under `φ`. -/
structure CandOf {G : UMultigraph V} {es : Edges} (φ : Iso G es) (U : SubObj V) (C : Sub) : Prop where
  memS : ∀ z, mem z C.S = true ↔ InEnds es z ∧ φ.g z ∈ U.atoms
  joints : (C.k₁ = φ.f U.k₁ ∧ C.k₂ = φ.f U.k₂) ∨ (C.k₁ = φ.f U.k₂ ∧ C.k₂ = φ.f U.k₁)
  hyper : C.hyper = U.hyper

namespace CandOf

variable {G : UMultigraph V} {es : Edges} {φ : Iso G es} {U : SubObj V} {C : Sub}

theorem memS_of_atoms (h : CandOf φ U C) (hsub : U.atoms ⊆ G.verts) {v : V} (hv : v ∈ U.atoms) :
    mem (φ.f v) C.S = true :=
  (h.memS _).mpr ⟨φ.fv v (hsub hv), by rw [φ.gf v (hsub hv)]; exact hv⟩

theorem ind_joints (h : CandOf φ U C) (u v : ℕ) : ind u v C.k₁ C.k₂ = ind u v (φ.f U.k₁) (φ.f U.k₂) := by
  rcases h.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, ind_swap]

theorem mult_inside (h : CandOf φ U C) (hsub : U.atoms ⊆ G.verts) {u v : V} (hu : u ∈ U.atoms)
    (hv : v ∈ U.atoms) : mult (inside C.S es) (φ.f u) (φ.f v) = G.mult s(u, v) := by
  rw [mult_inside_of_mem (h.memS_of_atoms hsub hu) (h.memS_of_atoms hsub hv), φ.mult_eq u (hsub hu) v (hsub hv)]

end CandOf

/-- **The core of a sub-object is isomorphic to the core list of its candidate.** -/
def isoCore {G : UMultigraph V} {es : Edges} (φ : Iso G es) {U : SubObj V} (hU : IsSubObjU G U) {C : Sub}
    (h : CandOf φ U C) : Iso (U.core G) (C.core es) := by
  have hsub : U.atoms ⊆ G.verts := hU.1.1
  have hk : U.k₁ ∈ U.atoms ∧ U.k₂ ∈ U.atoms := by
    have := hU.2.2; rw [IsBlockU, core_verts] at this; exact ⟨this.1, this.2.1⟩
  have hmult : ∀ u ∈ (U.core G).verts, ∀ v ∈ (U.core G).verts,
      (U.core G).mult s(u, v) = mult (C.core es) (φ.f u) (φ.f v) := by
    intro u hu v hv
    rw [core_verts] at hu hv
    rw [core_mult_of_mem G U hu hv]
    unfold Sub.core
    rw [h.hyper]
    by_cases hh : U.hyper = true
    · rw [if_pos hh]
      have hne : mult (inside C.S es) C.k₁ C.k₂ ≠ 0 := by
        rcases h.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2, h.mult_inside hsub hk.1 hk.2]; exact hU.2.1 hh
        · rw [e1, e2, h.mult_inside hsub hk.2 hk.1, Sym2.eq_swap]; exact hU.2.1 hh
      have := mult_eraseOne' hne (φ.f u) (φ.f v)
      rw [h.mult_inside hsub hu hv, h.ind_joints] at this
      have e : ind (φ.f u) (φ.f v) (φ.f U.k₁) (φ.f U.k₂) = if s(u, v) = s(U.k₁, U.k₂) then 1 else 0 := by
        unfold ind
        have : s(φ.f u, φ.f v) = s(φ.f U.k₁, φ.f U.k₂) ↔ s(u, v) = s(U.k₁, U.k₂) := by
          constructor
          · intro hh'
            have := congrArg (Sym2.map φ.g) hh'
            simpa [Sym2.map_mk, φ.gf u (hsub hu), φ.gf v (hsub hv), φ.gf _ (hsub hk.1), φ.gf _ (hsub hk.2)]
              using this
          · intro hh'
            have := congrArg (Sym2.map φ.f) hh'
            simpa [Sym2.map_mk] using this
        exact ite_one_iff this
      rw [e] at this
      simp only [hh, true_and]
      split_ifs at this ⊢ <;> omega
    · rw [if_neg hh, h.mult_inside hsub hu hv]; simp [hh]
  refine Iso.restrict φ (by rw [core_verts]; exact hsub) ?_ hmult
  intro z
  constructor
  · intro hz
    have hz' : InEnds (inside C.S es) z := by
      unfold Sub.core at hz
      split_ifs at hz
      · exact inEnds_eraseOne hz
      · exact hz
    obtain ⟨e, he, hze⟩ := hz'
    have he' := (List.mem_filter.mp he).2
    simp only [Bool.and_eq_true] at he'
    have hmz : mem z C.S = true := by rcases hze with rfl | rfl; exact he'.1; exact he'.2
    rw [core_verts]
    exact (h.memS z).mp hmz
  · rintro ⟨hz, hzU⟩
    rw [core_verts] at hzU
    have hB := hU.2.2
    obtain ⟨-, -, -, d₁, d₂, d, -⟩ := hB
    have hdeg : Core.deg (U.core G) (φ.g z) ≠ 0 := by
      by_cases h1 : φ.g z = U.k₁
      · rw [h1, d₁]; omega
      by_cases h2 : φ.g z = U.k₂
      · rw [h2, d₂]; omega
      rw [d _ (by rw [core_verts]; exact hzU) h1 h2]; omega
    obtain ⟨w, hw, hzw⟩ := exists_adj_of_deg (by rw [core_verts]; exact hzU) hdeg
    rw [hmult _ (by rw [core_verts]; exact hzU) w hw, φ.fg z hz] at hzw
    exact (inEnds_of_mult_ne_zero hzw).1

theorem isoCore_f {G : UMultigraph V} {es : Edges} (φ : Iso G es) {U : SubObj V} (hU : IsSubObjU G U) {C : Sub}
    (h : CandOf φ U C) : (isoCore φ hU h).f = φ.f := rfl

/-- A set closed under the adjacency of a bond list contains everything reachable. -/
theorem rtg_closed {E : Edges} {Q : ℕ → Prop} (hQ : ∀ p q, Q p → Adj E p q → Q q) {x y : ℕ}
    (h : Relation.ReflTransGen (Adj E) x y) (hx : Q x) : Q y := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hQ _ _ ih hbc

/-- **Enumeration completeness**: every sub-object has a candidate in `subObjects`. -/
theorem exists_cand {G : UMultigraph V} {es : Edges} (φ : Iso G es) (hdeg : ∀ v ∈ G.verts, Core.deg G v ≤ 4)
    (hlt : ∀ z, InEnds es z → z < 32) (hok : compsOKAll (maskOf es) es = true) {U : SubObj V}
    (hU : IsSubObjU G U) : ∃ C ∈ subObjects (maskOf es) es, CandOf φ U C := by
  classical
  have hsub : U.atoms ⊆ G.verts := hU.1.1
  have hk : U.k₁ ∈ U.atoms ∧ U.k₂ ∈ U.atoms ∧ U.k₁ ≠ U.k₂ := by
    have := hU.2.2; rw [IsBlockU, core_verts] at this; exact ⟨this.1, this.2.1, this.2.2.1⟩
  obtain ⟨hk₁, hk₂, hne⟩ := hk
  have ea := φ.fv _ (hsub hk₁); have eb := φ.fv _ (hsub hk₂)
  have hab : φ.f U.k₁ ≠ φ.f U.k₂ := fun h => hne (φ.f_injOn (hsub hk₁) (hsub hk₂) h)
  -- the two joints of the candidate
  obtain ⟨lo, hi, hlohi, hjo⟩ : ∃ lo hi, lo < hi ∧
      ((lo = φ.f U.k₁ ∧ hi = φ.f U.k₂) ∨ (lo = φ.f U.k₂ ∧ hi = φ.f U.k₁)) := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨_, _, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h, Or.inr ⟨rfl, rfl⟩⟩
  have elo : InEnds es lo := by rcases hjo with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
  have ehi : InEnds es hi := by rcases hjo with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption
  have hlo : lo ∈ elems (maskOf es) := mem_elems.mpr ⟨hlt _ elo, mem_maskOf.mpr elo⟩
  have hhi : hi ∈ (elems (maskOf es)).filter (lo < ·) :=
    List.mem_filter.mpr ⟨mem_elems.mpr ⟨hlt _ ehi, mem_maskOf.mpr ehi⟩, by simpa using hlohi⟩
  set W := sdiff (maskOf es) (bit lo ||| bit hi) with hW
  set cs := comps 16 (inside W es) W with hcs
  have hpart : (cs.foldr (· ||| ·) 0).beq W = true ∧ pairwiseDisj cs = true := by
    have := List.all_eq_true.mp (List.all_eq_true.mp hok lo hlo) hi hhi
    simpa [Bool.and_eq_true] using this
  have hcover : cs.foldr (· ||| ·) 0 = W := by simpa using hpart.1
  -- the interior is closed
  set Q : ℕ → Prop := fun z => InEnds es z ∧ φ.g z ∈ U.inner with hQdef
  have joint_of : ∀ z, InEnds es z → (φ.g z = U.k₁ ∨ φ.g z = U.k₂) → z = lo ∨ z = hi := by
    intro z hz h
    rcases h with h | h <;> rw [← φ.fg z hz, h] <;> rcases hjo with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [e1, e2]
  have memW : ∀ z, mem z W = true ↔ InEnds es z ∧ z ≠ lo ∧ z ≠ hi := by
    intro z
    simp only [hW, mem_sdiff, mem_or, mem_bit, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not, mem_maskOf]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Ne.symm h2, Ne.symm h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Ne.symm h2, Ne.symm h3⟩
  have hQ : ∀ p q, Q p → Adj (inside W es) p q → Q q := by
    rintro p q ⟨hp, hpi⟩ hpq
    obtain ⟨-, hqW, hpq⟩ := adj_inside hpq
    have eq := (inEnds_of_mult_ne_zero hpq).2
    obtain ⟨-, hqlo, hqhi⟩ := (memW q).mp hqW
    have hG : G.mult s(φ.g p, φ.g q) ≠ 0 := by rw [φ.mult_g hp eq]; exact hpq
    have hqU := inner_closed hdeg hU hpi hG
    refine ⟨eq, ?_⟩
    simp only [SubObj.inner, Finset.mem_erase]
    refine ⟨fun h => ?_, fun h => ?_, hqU⟩
    · rcases joint_of q eq (Or.inr h) with h' | h' <;> contradiction
    · rcases joint_of q eq (Or.inl h) with h' | h' <;> contradiction
  -- components meeting the interior lie in it
  have compQ : ∀ X ∈ cs, (∃ z, mem z X = true ∧ Q z) → ∀ z, mem z X = true → Q z := by
    rintro X hX ⟨x, hx, hQx⟩ z hz
    obtain ⟨s, -, hreach⟩ := comps_conn 16 (inside W es) W hX
    have hs : Q s := rtg_closed hQ (rtg_symm (hreach x hx)) hQx
    exact rtg_closed hQ (hreach z hz) hs
  set P : ℕ → Prop := fun X => ∃ z, mem z X = true ∧ Q z
  set m := selMask P cs
  set S := bit lo ||| bit hi ||| selectComps cs m with hS
  have memS : ∀ z, mem z S = true ↔ InEnds es z ∧ φ.g z ∈ U.atoms := by
    intro z
    rw [hS, mem_or, mem_or, mem_bit, mem_bit, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, mem_selectComps]
    constructor
    · rintro ((rfl | rfl) | ⟨X, hX, hP, hz⟩)
      · refine ⟨elo, ?_⟩
        rcases hjo with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1, φ.gf _ (hsub ‹_›)] <;> assumption
      · refine ⟨ehi, ?_⟩
        rcases hjo with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2, φ.gf _ (hsub ‹_›)] <;> assumption
      · obtain ⟨hz, hzi⟩ := compQ X hX hP z hz
        exact ⟨hz, by simp only [SubObj.inner, Finset.mem_erase] at hzi; exact hzi.2.2⟩
    · rintro ⟨hz, hzU⟩
      by_cases hj : φ.g z = U.k₁ ∨ φ.g z = U.k₂
      · rcases joint_of z hz hj with h | h
        · exact Or.inl (Or.inl h.symm)
        · exact Or.inl (Or.inr h.symm)
      · rw [not_or] at hj
        have hQz : Q z := ⟨hz, by simp only [SubObj.inner, Finset.mem_erase]; exact ⟨hj.2, hj.1, hzU⟩⟩
        have hzW : mem z W = true := by
          refine (memW z).mpr ⟨hz, fun h => ?_, fun h => ?_⟩
          · rcases hjo with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [h, e1, φ.gf _ (hsub ‹_›)] at hj <;> simp at hj
          · rcases hjo with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [h, e2, φ.gf _ (hsub ‹_›)] at hj <;> simp at hj
        rw [← hcover, mem_foldr_or] at hzW
        obtain ⟨X, hX, hzX⟩ := hzW
        exact Or.inr ⟨X, hX, ⟨z, hzX, hQz⟩, hzX⟩
  have hC : CandOf φ U ⟨S, lo, hi, U.hyper⟩ :=
    ⟨memS, by rcases hjo with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [e1, e2], rfl⟩
  refine ⟨⟨S, lo, hi, U.hyper⟩, ?_, hC⟩
  -- membership in the enumeration
  have hSV : S ≠ maskOf es := by
    obtain ⟨v, hv, hvU⟩ := Finset.exists_of_ssubset hU.1
    intro h
    have := (memS (φ.f v)).mp (by rw [h]; exact mem_maskOf.mpr (φ.fv v hv))
    rw [φ.gf v hv] at this; exact hvU this.2
  have hvalid : Sub.valid ⟨S, lo, hi, U.hyper⟩ es = true := by
    unfold Sub.valid
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · cases hh : U.hyper
      · rfl
      · simp only [Bool.not_true, Bool.false_or, bne_iff_ne, ne_eq]
        rw [show lo = (lo : ℕ) from rfl]
        rcases hjo with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2, hC.mult_inside hsub hk₁ hk₂]; exact hU.2.1 hh
        · rw [e1, e2, hC.mult_inside hsub hk₂ hk₁, Sym2.eq_swap]; exact hU.2.1 hh
    · rw [List.all_eq_true]
      intro v hv
      have hvS := (mem_elems.mp hv).2
      obtain ⟨hve, hvU⟩ := (memS v).mp hvS
      have hdegv := degU_iso (isoCore φ hU hC) (v := φ.g v) (by rw [core_verts]; exact hvU)
      rw [isoCore_f, φ.fg v hve] at hdegv
      obtain ⟨-, -, -, d₁, d₂, d, -⟩ := hU.2.2
      by_cases hj : φ.g v = U.k₁ ∨ φ.g v = U.k₂
      · have hj' := joint_of v hve hj
        have : (v.beq lo || v.beq hi) = true := by
          rcases hj' with h | h <;> simp [h]
        rw [if_pos this]
        rcases hj with h | h
        · rw [h, d₁] at hdegv; simp [← hdegv]
        · rw [h, d₂] at hdegv; simp [← hdegv]
      · rw [not_or] at hj
        have : (v.beq lo || v.beq hi) = false := by
          simp only [nat_beq_eq_decide, Bool.or_eq_false_iff, decide_eq_false_iff_not]
          constructor
          · intro h; apply hj.1 ?_ |>.elim
            rcases hjo with ⟨e1, -⟩ | ⟨e1, -⟩
            · rw [h, e1, φ.gf _ (hsub hk₁)]
            · exact absurd (by rw [h, e1, φ.gf _ (hsub hk₂)]) hj.2
          · intro h; apply hj.2 ?_ |>.elim
            rcases hjo with ⟨-, e2⟩ | ⟨-, e2⟩
            · rw [h, e2, φ.gf _ (hsub hk₂)]
            · exact absurd (by rw [h, e2, φ.gf _ (hsub hk₁)]) hj.1
        rw [if_neg (by rw [this]; simp)]
        rw [d _ (by rw [core_verts]; exact hvU) hj.1 hj.2] at hdegv
        simp [← hdegv]
  unfold subObjects
  rw [List.mem_flatMap]
  refine ⟨lo, hlo, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨hi, hhi, ?_⟩
  try dsimp only
  rw [List.mem_flatMap]
  refine ⟨m, List.mem_range.mpr (selMask_lt P cs), ?_⟩
  try dsimp only
  rw [if_neg (by simpa using hSV)]
  rw [List.mem_filter]
  refine ⟨List.mem_map.mpr ⟨U.hyper, by cases U.hyper <;> simp, rfl⟩, hvalid⟩

end WaveTurbulence.TVine.Checker
