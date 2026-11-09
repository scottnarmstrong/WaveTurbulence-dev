/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SubEnum

/-!
# Sub-object facts from the candidate checks

* `allowedType_of_typeOK`: the type of a sub-object is I, VC:I+I or T (L1's `AllowedTypeU`);
* `not_gapCutAt_of_gapFreeAt`: gap freeness at a joint (L1's `GapCutAt`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

variable {V : Type*} [DecidableEq V]

theorem nodup_elems (S : ℕ) : (elems S).Nodup := (List.nodup_range).filter _

theorem mem_elems_of_cand {G : UMultigraph V} {es : Edges} {φ : Iso G es} {U : SubObj V} {C : Sub}
    (hC : CandOf φ U C) (hlt : ∀ z, InEnds es z → z < 32) (hsub : U.atoms ⊆ G.verts) {v : V}
    (hv : v ∈ U.atoms) : φ.f v ∈ elems C.S :=
  mem_elems.mpr ⟨hlt _ (φ.fv v (hsub hv)), hC.memS_of_atoms hsub hv⟩

/-- **The type of a sub-object.** -/
theorem allowedType_of_typeOK {G : UMultigraph V} {es : Edges} (φ : Iso G es)
    (hloop : ∀ v, G.mult s(v, v) = 0) (hlt : ∀ z, InEnds es z → z < 32) {U : SubObj V} (hU : IsSubObjU G U)
    {C : Sub} (hC : CandOf φ U C) (hb : C.typeOK es = true) : AllowedTypeU G U := by
  have hsub : U.atoms ⊆ G.verts := hU.1.1
  obtain ⟨hk₁, hk₂, hne, -, -, -, -⟩ := hU.2.2
  rw [core_verts] at hk₁ hk₂
  let ψ := isoCore φ hU hC
  have hψf : ψ.f = φ.f := rfl
  have cmult : ∀ u ∈ U.atoms, ∀ v ∈ U.atoms, (U.core G).mult s(u, v) = mult (C.core es) (φ.f u) (φ.f v) := by
    intro u hu v hv; rw [← hψf]; exact ψ.mult_eq u (by rw [core_verts]; exact hu) v (by rw [core_verts]; exact hv)
  have hcl : ∀ v, (U.core G).mult s(v, v) = 0 := fun v => by
    have := core_mult_le G U s(v, v); rw [hloop] at this; omega
  have fk := mem_elems_of_cand hC hlt hsub hk₁
  have fk' := mem_elems_of_cand hC hlt hsub hk₂
  have fne : φ.f U.k₁ ≠ φ.f U.k₂ := fun h => hne (φ.f_injOn (hsub hk₁) (hsub hk₂) h)
  have atoms_in : ∀ v ∈ U.atoms, φ.f v ∈ elems C.S := fun v hv => mem_elems_of_cand hC hlt hsub hv
  have back : ∀ z ∈ elems C.S, φ.g z ∈ U.atoms ∧ φ.f (φ.g z) = z := by
    intro z hz
    obtain ⟨he, hU'⟩ := (hC.memS z).mp (mem_elems.mp hz).2
    exact ⟨hU', φ.fg z he⟩
  unfold Sub.typeOK at hb
  split at hb
  · -- two atoms: a double bond
    rename_i p q hpq
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hb
    obtain ⟨hh, h2⟩ := hb
    left
    refine ⟨by rw [← hC.hyper]; exact hh, hne, ?_, ?_⟩
    · ext v
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        have h1 := atoms_in v hv
        rw [hpq] at h1 fk fk'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 fk fk'
        have : φ.f v = φ.f U.k₁ ∨ φ.f v = φ.f U.k₂ := by
          rcases h1 with h1 | h1 <;> rcases fk with h | h <;> rcases fk' with h' | h' <;>
            first | (left; rw [h1, h]; done) | (right; rw [h1, h']; done) | (exfalso; exact fne (h.trans h'.symm))
        rcases this with h | h
        · exact Or.inl (φ.f_injOn (hsub hv) (hsub hk₁) h)
        · exact Or.inr (φ.f_injOn (hsub hv) (hsub hk₂) h)
      · rintro (rfl | rfl)
        · exact hk₁
        · exact hk₂
    · have := cmult _ hk₁ _ hk₂
      rw [core_mult_of_mem G U hk₁ hk₂] at this
      have hh' : U.hyper = false := by rw [← hC.hyper]; exact hh
      simp only [hh', Bool.false_eq_true, false_and, if_false, Nat.sub_zero] at this
      rw [this]
      rcases hC.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at h2; exact h2
      · rw [e1, e2, mult_comm] at h2; exact h2
  · -- three atoms: VC:I+I
    rename_i x y z hxyz
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨h1, h2⟩ := hb
    set mid := if (x.beq C.k₁ || x.beq C.k₂) = true then (if (y.beq C.k₁ || y.beq C.k₂) = true then z else y)
      else x with hmid
    have hmidS : mid ∈ elems C.S := by
      rw [hxyz, hmid]; split_ifs <;> simp
    obtain ⟨hmU, hmf⟩ := back mid hmidS
    -- the two double bonds, in the orientation of `U`
    have d1 : mult (C.core es) (φ.f U.k₁) mid = 2 ∧ mult (C.core es) mid (φ.f U.k₂) = 2 := by
      rcases hC.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2⟩
      · rw [e1] at h1; rw [e2] at h2; rw [mult_comm] at h1 h2; exact ⟨h2, h1⟩
    have c1 : (U.core G).mult s(U.k₁, φ.g mid) = 2 := by rw [cmult _ hk₁ _ hmU, hmf]; exact d1.1
    have c2 : (U.core G).mult s(φ.g mid, U.k₂) = 2 := by rw [cmult _ hmU _ hk₂, hmf]; exact d1.2
    have n1 : U.k₁ ≠ φ.g mid := fun h => by rw [← h, hcl] at c1; omega
    have n2 : φ.g mid ≠ U.k₂ := fun h => by rw [h, hcl] at c2; omega
    right; left
    refine ⟨φ.g mid, n1, n2, hne, ?_, c1, c2⟩
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      have hnd := nodup_elems C.S
      rw [hxyz] at hnd
      have hv' := atoms_in v hv
      have mk1 : φ.f U.k₁ ≠ mid := fun h => n1 (by rw [← h, φ.gf _ (hsub hk₁)])
      have mk2 : mid ≠ φ.f U.k₂ := fun h => n2 (by rw [h, φ.gf _ (hsub hk₂)])
      rw [hxyz] at hv' fk fk' hmidS
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hv' fk fk' hmidS
      have : φ.f v = φ.f U.k₁ ∨ φ.f v = mid ∨ φ.f v = φ.f U.k₂ := by
        rcases hv' with h | h | h <;> rcases fk with a | a | a <;> rcases fk' with b | b | b <;>
          rcases hmidS with c | c | c <;> first
          | (left; rw [h, a]; done) | (right; left; rw [h, c]; done) | (right; right; rw [h, b]; done)
          | (exfalso; exact fne (a.trans b.symm)) | (exfalso; exact mk1 (a.trans c.symm))
          | (exfalso; exact mk2 (c.trans b.symm))
      rcases this with h | h | h
      · exact Or.inl (φ.f_injOn (hsub hv) (hsub hk₁) h)
      · exact Or.inr (Or.inl (by rw [← h, φ.gf v (hsub hv)]))
      · exact Or.inr (Or.inr (φ.f_injOn (hsub hv) (hsub hk₂) h))
    · rintro (rfl | rfl | rfl)
      · exact hk₁
      · exact hmU
      · exact hk₂
  · -- otherwise: a T-vine
    right; right
    simp only [Bool.and_eq_true] at hb
    apply isTVineU_of_tvineB ψ hU.2.2
    rw [hψf]
    rcases hC.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]; exact hb.1
    · rw [← e1, ← e2]; exact hb.2

/-! ## Gap freeness -/

theorem eraseOne_sublist : ∀ (es : Edges) (a b : ℕ), (eraseOne es a b).Sublist es
  | [], _, _ => List.Sublist.slnil
  | e :: es, a, b => by
    simp only [eraseOne]
    split
    · exact List.sublist_cons_self _ _
    · exact (eraseOne_sublist es a b).cons_cons _

theorem core_sublist (C : Sub) (es : Edges) : (C.core es).Sublist es := by
  unfold Sub.core inside
  split_ifs
  · exact (eraseOne_sublist _ _ _).trans List.filter_sublist
  · exact List.filter_sublist

theorem mult_le_of_sublist {l l' : Edges} (h : l.Sublist l') (a b : ℕ) : mult l a b ≤ mult l' a b :=
  (h.filter _).length_le

theorem inEnds_of_sublist {l l' : Edges} (h : l.Sublist l') {z : ℕ} (hz : InEnds l z) : InEnds l' z := by
  obtain ⟨e, he, h'⟩ := hz; exact ⟨e, h.subset he, h'⟩

/-- A path between the two sides of a set crosses it. -/
theorem rtg_cross {E : Edges} {P : ℕ → Prop} {x y : ℕ} (h : Relation.ReflTransGen (Adj E) x y) (hx : P x)
    (hy : ¬ P y) : ∃ a b, P a ∧ ¬ P b ∧ Adj E a b := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : P b
    · exact ⟨b, c, hb, hy, hbc⟩
    · exact ih hb

theorem sum_cross_single {X T : Finset V} (hXT : X ⊆ T) {u w : V} (hu : u ∈ X) (hw : w ∈ T) (hwX : w ∉ X) :
    ∑ p ∈ X, ∑ q ∈ T \ X, (if s(p, q) = s(u, w) then 1 else 0) = 1 := by
  have huw : u ≠ w := fun h => hwX (h ▸ hu)
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single w]
    · simp
    · intro q _ hq; rw [if_neg]; rw [Sym2.eq_iff]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hq h
      · exact huw h
    · intro h; exact absurd (Finset.mem_sdiff.mpr ⟨hw, hwX⟩) h
  · intro p hp hpu
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    rw [Sym2.eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hpu h1
    · rw [h1] at hp; exact hwX hp
  · intro h; exact absurd hu h

/-- **Gap freeness at a joint of a sub-object**, from `gapFreeAt`. -/
theorem sum_cross_pair {X T : Finset V} (hXT : X ⊆ T) {u w : V} (hu : u ∈ T) (hw : w ∈ T)
    (h : u ∈ X ↔ w ∉ X) : ∑ p ∈ X, ∑ q ∈ T \ X, (if s(p, q) = s(u, w) then 1 else 0) = 1 := by
  by_cases huX : u ∈ X
  · exact sum_cross_single hXT huX hw (h.mp huX)
  · have hwX : w ∈ X := by tauto
    rw [Sym2.eq_swap]
    exact sum_cross_single hXT hwX hu huX

theorem not_gapCutAt_of_gapFreeAt {G : UMultigraph V} {es : Edges} (φ : Iso G es)
    (hloop : ∀ v, G.mult s(v, v) = 0) {U : SubObj V} (hU : IsSubObjU G U) {C : Sub} (hC : CandOf φ U C)
    {k : V} (hk : k = U.k₁ ∨ k = U.k₂) (hb : C.gapFreeAt (maskOf es) es (φ.f k) = true) : ¬ GapCutAt G U k := by
  have hsub : U.atoms ⊆ G.verts := hU.1.1
  have hkU : k ∈ U.atoms := by
    obtain ⟨hk₁, hk₂, -⟩ := hU.2.2; rw [core_verts] at hk₁ hk₂
    rcases hk with rfl | rfl <;> assumption
  have hkG := hsub hkU
  let ψ := isoCore φ hU hC
  have hψf : ψ.f = φ.f := rfl
  rintro ⟨X, hX, hcut, n₁, n₂, hnb, h₁, h₂⟩
  unfold Sub.gapFreeAt at hb
  split at hb
  · rename_i x y hxy
    -- the two core bonds at `k`
    have hcore0 : mult (C.core es) (φ.f k) (φ.f k) = 0 := by
      rw [← hψf, ← ψ.mult_eq k (by rw [core_verts]; exact hkU) k (by rw [core_verts]; exact hkU)]
      have := core_mult_le G U s(k, k); rw [hloop] at this; omega
    have hxe : InEnds (C.core es) x ∧ InEnds (C.core es) y := by
      constructor <;> apply inEnds_of_mem_nbrs (a := φ.f k) <;> rw [hxy] <;> simp
    have hnbrs : Core.nbrs (U.core G) k = ({ψ.g x, ψ.g y} : Multiset V) := by
      rw [nbrsU_eq ψ (by rw [core_verts]; exact hkU) ({x, y} : Multiset ℕ)
        (fun z => by rw [hψf, hxy, ← Multiset.coe_count]; rfl) ?_ ?_]
      · simp
      · intro h
        have := List.count_pos_iff.mpr (show φ.f k ∈ nbrs (C.core es) (φ.f k) by
          rw [hxy]; simpa [hψf] using h)
        rw [count_nbrs, hcore0] at this; omega
      · intro z hz; simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
        rcases hz with rfl | rfl; exacts [hxe.1, hxe.2]
    rw [hnbrs] at hnb
    have cross : ∀ w ∈ ({ψ.g x, ψ.g y} : Multiset V), (k ∈ X ↔ w ∉ X) := by
      intro w hw
      rw [hnb] at hw
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hw
      rcases hw with rfl | rfl; exacts [h₁, h₂]
    have gxv : ψ.g x ∈ G.verts := hsub (by have := ψ.gv x hxe.1; rwa [core_verts] at this)
    have gyv : ψ.g y ∈ G.verts := hsub (by have := ψ.gv y hxe.2; rwa [core_verts] at this)
    have hgx : ψ.g x = φ.g x := rfl
    have hgy : ψ.g y = φ.g y := rfl
    rw [hgx, hgy] at cross; rw [hgx] at gxv; rw [hgy] at gyv
    have hxe' : InEnds es x := inEnds_of_sublist (core_sublist C es) hxe.1
    have hye' : InEnds es y := inEnds_of_sublist (core_sublist C es) hxe.2
    -- removability of the two copies
    have cx : List.count x (nbrs (C.core es) (φ.f k)) = 1 + (if y = x then 1 else 0) := by
      rw [hxy]; simp only [List.count_cons, List.count_nil, beq_iff_eq]; split_ifs <;> simp_all
    have cy : List.count y (nbrs (C.core es) (φ.f k)) = (if x = y then 1 else 0) + 1 := by
      rw [hxy]; simp only [List.count_cons, List.count_nil, beq_iff_eq]; split_ifs <;> simp_all
    rw [count_nbrs] at cx cy
    have mx := mult_le_of_sublist (core_sublist C es) (φ.f k) x
    have my := mult_le_of_sublist (core_sublist C es) (φ.f k) y
    have r1 : mult es (φ.f k) x ≠ 0 := by split_ifs at cx <;> omega
    have r2 : mult (eraseOne es (φ.f k) x) (φ.f k) y ≠ 0 := by
      have := mult_eraseOne' r1 (φ.f k) y
      unfold ind at this
      by_cases hyx : y = x
      · subst hyx; simp at cx; rw [if_pos rfl] at this; omega
      · have hne : ¬ s(φ.f k, y) = s(φ.f k, x) := fun h => hyx (by rw [Sym2.eq_iff] at h; omega)
        rw [if_neg hne] at this
        have hxy' : ¬ x = y := fun h => hyx h.symm
        rw [if_neg hxy'] at cy; omega
    have e1 := mult_eraseOne' r1
    have e2 := mult_eraseOne' r2
    generalize hes' : eraseOne (eraseOne es (φ.f k) x) (φ.f k) y = es' at e2 hb
    have hsub' : ∀ z, InEnds es' z → InEnds es z := fun z hz => by
      rw [← hes'] at hz; exact inEnds_eraseOne (inEnds_eraseOne hz)
    have indX : ∀ p ∈ G.verts, ∀ q ∈ G.verts, ∀ z, InEnds es z →
        ind (φ.f p) (φ.f q) (φ.f k) z = if s(p, q) = s(k, φ.g z) then 1 else 0 := by
      intro p hp q hq z hz
      unfold ind
      apply ite_one_iff
      constructor
      · intro h
        have := congrArg (Sym2.map φ.g) h
        simpa [Sym2.map_mk, φ.gf p hp, φ.gf q hq, φ.gf k hkG] using this
      · intro h
        have := congrArg (Sym2.map φ.f) h
        simpa [Sym2.map_mk, φ.fg z hz] using this
    -- no bond of `es'` crosses `X`
    have hzero : ∀ p ∈ X, ∀ q ∈ G.verts \ X, mult es' (φ.f p) (φ.f q) = 0 := by
      have e : ∀ p ∈ X, ∀ q ∈ G.verts \ X, G.mult s(p, q) = mult es' (φ.f p) (φ.f q) +
          ((if s(p, q) = s(k, φ.g y) then 1 else 0) + (if s(p, q) = s(k, φ.g x) then 1 else 0)) := by
        intro p hp q hq
        have hqG := (Finset.mem_sdiff.mp hq).1
        rw [φ.mult_eq p (hX hp) q hqG, ← indX p (hX hp) q hqG y hye', ← indX p (hX hp) q hqG x hxe']
        have := e1 (φ.f p) (φ.f q); have := e2 (φ.f p) (φ.f q); omega
      have hc : cut G X = ∑ p ∈ X, ∑ q ∈ G.verts \ X, (mult es' (φ.f p) (φ.f q) +
          ((if s(p, q) = s(k, φ.g y) then 1 else 0) + (if s(p, q) = s(k, φ.g x) then 1 else 0))) :=
        Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => e p hp q hq
      simp only [Finset.sum_add_distrib] at hc
      rw [sum_cross_pair hX hkG gyv (cross _ (by simp)), sum_cross_pair hX hkG gxv (cross _ (by simp)),
        hcut] at hc
      have h0 : ∑ p ∈ X, ∑ q ∈ G.verts \ X, mult es' (φ.f p) (φ.f q) = 0 := by omega
      intro p hp q hq
      exact Finset.sum_eq_zero_iff.mp (Finset.sum_eq_zero_iff.mp h0 p hp) q hq
    have key : ∀ a b, Adj es' a b → φ.g a ∈ X → φ.g b ∉ X → False := by
      intro a b hab ha hb'
      have hae := hsub' a (inEnds_of_mult_ne_zero hab).1
      have hbe := hsub' b (inEnds_of_mult_ne_zero hab).2
      have := hzero (φ.g a) ha (φ.g b) (Finset.mem_sdiff.mpr ⟨φ.gv b hbe, hb'⟩)
      rw [φ.fg a hae, φ.fg b hbe] at this
      exact hab this
    have path := connB_sound hb (mem_maskOf.mpr (φ.fv k hkG)) (mem_maskOf.mpr hxe')
    have hxX : k ∈ X ↔ φ.g x ∉ X := cross _ (by simp)
    by_cases hkX : k ∈ X
    · obtain ⟨a, b, ha, hb', hab⟩ := rtg_cross (P := fun z => φ.g z ∈ X) path
        (by simpa [φ.gf k hkG] using hkX) (hxX.mp hkX)
      exact key a b hab ha hb'
    · obtain ⟨a, b, ha, hb', hab⟩ := rtg_cross (P := fun z => φ.g z ∉ X) path
        (by simpa [φ.gf k hkG] using hkX) (not_not.mpr (not_not.mp (hxX.not.mp hkX)))
      exact key b a (by unfold Adj at hab ⊢; rwa [mult_comm]) (not_not.mp hb') ha
  · exact absurd hb (by simp)

end WaveTurbulence.TVine.Checker
