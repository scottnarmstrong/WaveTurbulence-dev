/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma15
public import WaveTurbulence.Foundations.TVine.Core.Bridge

/-!
# Smoothing a joint; the closure as two smoothings

`smooth G j n n'` deletes the atom `j` (of degree 2, neighbours `n, n'`) and joins `n, n'` by a bond. The closure
of a block is the smoothing of `j₁` followed by the smoothing of `j₂` (`closure_eq_smooth`, `isClosureU_smooth`),
in both cases `σ = 0` and `σ = 1`.

Neighbour multisets: `mult_of_nbrs_eq`, `nbrs_eq_of_mult`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Neighbour multisets -/

theorem mult_of_nbrs_eq {G : UMultigraph V} {v : V} {N : Multiset V} (h : nbrs G v = N) {x : V} (hx : x ≠ v) :
    G.mult s(v, x) = N.count x := by
  have := count_nbrs G v x
  rw [h] at this
  rw [this, if_neg (Ne.symm hx), add_zero]
  split_ifs with hxv
  · rfl
  · exact mult_eq_zero_of_right G hxv v

theorem loop_of_nbrs_eq {G : UMultigraph V} {v : V} {N : Multiset V} (h : nbrs G v = N) (hv : v ∈ G.verts) :
    G.mult s(v, v) + G.mult s(v, v) = N.count v := by
  have := count_nbrs G v v
  rw [h] at this
  rw [this, if_pos hv, if_pos rfl]

theorem nbrs_eq_of_mult {G : UMultigraph V} {v : V} (N : Multiset V) (hloop : G.mult s(v, v) = 0)
    (hN : ∀ x ∈ N, x ∈ G.verts ∧ x ≠ v) (hm : ∀ x, x ≠ v → G.mult s(v, x) = N.count x) : nbrs G v = N := by
  ext x
  rw [count_nbrs]
  by_cases hxv : x = v
  · subst hxv
    have : N.count x = 0 := Multiset.count_eq_zero.mpr fun hm => (hN x hm).2 rfl
    rw [this, hloop]; simp
  · rw [if_neg (Ne.symm hxv), add_zero, ← hm x hxv]
    split_ifs with hx
    · rfl
    · rw [hm x hxv]; exact (Multiset.count_eq_zero.mpr fun hm => hx (hN x hm).1).symm

theorem mem_verts_of_mem_nbrs {G : UMultigraph V} {v x : V} (hx : x ∈ nbrs G v) : x ∈ G.verts := by
  have h := Multiset.count_pos.mpr hx
  rw [count_nbrs] at h
  by_cases h1 : x ∈ G.verts
  · exact h1
  · rw [if_neg h1, zero_add] at h
    by_cases h2 : v = x
    · subst h2; rw [if_pos rfl] at h; exact G.supp _ (by omega) v (Sym2.mem_mk_left v v)
    · rw [if_neg h2] at h; omega

theorem pair_count_pos {x y z : V} (h : 0 < ({x, y} : Multiset V).count z) : z = x ∨ z = y := by
  have := Multiset.count_pos.mp h
  simpa using this

theorem pair_eq_of_mem {x y z : V} (h : z ∈ ({x, y} : Multiset V)) :
    ∃ w, ({x, y} : Multiset V) = {z, w} := by
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact ⟨y, rfl⟩
  · exact ⟨x, Multiset.pair_comm _ _⟩

theorem sym2_eq_of_pair_eq {x y x' y' : V} (h : ({x, y} : Multiset V) = {x', y'}) : s(x, y) = s(x', y') := by
  have hx : x ∈ ({x', y'} : Multiset V) := h ▸ Multiset.mem_cons_self _ _
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
    have := (Multiset.cons_inj_right _).mp h
    rw [Multiset.singleton_inj] at this
    rw [this]
  · rw [Multiset.pair_comm x' x, Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
    have := (Multiset.cons_inj_right _).mp h
    rw [Multiset.singleton_inj] at this
    rw [this, Sym2.eq_swap]

/-! ## Smoothing -/

/-- **Smoothing** the atom `j` with neighbours `n, n'`: delete `j`, join `n` and `n'`. -/
def smooth (G : UMultigraph V) (j n n' : V) : UMultigraph V := splice G j j {s(n, n')}

theorem smooth_mult (G : UMultigraph V) (j n n' : V) (e : Sym2 V) :
    (smooth G j n n').mult e = if j ∈ e then 0 else G.mult e + (if e = s(n, n') then 1 else 0) := by
  unfold smooth; rw [splice_mult, Multiset.count_singleton]; exact if_congr or_self_iff rfl rfl

theorem smooth_verts {G : UMultigraph V} {j n n' : V} (hn : n ∈ G.verts) (hn' : n' ∈ G.verts) :
    (smooth G j n n').verts = G.verts.erase j := by
  rw [smooth, splice_verts_of_subset]
  · exact Finset.erase_idem
  · intro e he x hx
    rw [Multiset.mem_singleton] at he; subst he
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

theorem smooth_mult_at (G : UMultigraph V) {j n n' v : V} (hvj : v ≠ j) (x : V) :
    (smooth G j n n').mult s(v, x) = if x = j then 0 else G.mult s(v, x) + (if s(v, x) = s(n, n') then 1 else 0) := by
  rw [smooth_mult]
  have : j ∈ s(v, x) ↔ x = j := by
    rw [Sym2.mem_iff]; exact ⟨fun h => h.resolve_left (Ne.symm hvj) |>.symm, fun h => Or.inr h.symm⟩
  by_cases hx : x = j
  · rw [if_pos (this.mpr hx), if_pos hx]
  · rw [if_neg (mt this.mp hx), if_neg hx]

theorem not_mem_nbrs_self {G : UMultigraph V} (hl : G.Loopless) (v : V) : v ∉ nbrs G v := by
  intro h
  have := Multiset.count_pos.mpr h
  rw [count_nbrs, hl v] at this
  simp at this

theorem nbrs_mem_ne {G : UMultigraph V} (hl : G.Loopless) {v x y : V} (h : nbrs G v = {x, y}) :
    x ≠ v ∧ y ≠ v := by
  have := not_mem_nbrs_self hl v
  rw [h] at this
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at this
  exact ⟨Ne.symm this.1, Ne.symm this.2⟩

theorem nbrs_mem_verts {G : UMultigraph V} {v x y : V} (h : nbrs G v = {x, y}) : x ∈ G.verts ∧ y ∈ G.verts :=
  ⟨mem_verts_of_mem_nbrs (by rw [h]; simp), mem_verts_of_mem_nbrs (by rw [h]; simp)⟩

theorem count_pair_self (x y : V) : ({x, y} : Multiset V).count x = 1 + (if x = y then 1 else 0) := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons_self, Multiset.count_singleton, add_comm]

theorem count_pair_of_ne {x y z : V} (hx : z ≠ x) : ({x, y} : Multiset V).count z = if z = y then 1 else 0 := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons_of_ne hx, Multiset.count_singleton]

/-- In a `σ = 0` situation, smoothing `j₁` does not change the bonds at `j₂`. -/
theorem nbrs_smooth_far {G : UMultigraph V} {j₁ j₂ n n' : V} (hl : G.Loopless) (hj : j₁ ≠ j₂)
    (hσ : G.mult s(j₁, j₂) = 0) (hn : j₂ ≠ n ∧ j₂ ≠ n') (hn' : n ∈ G.verts ∧ n' ∈ G.verts) {N : Multiset V}
    (h2 : nbrs G j₂ = N) (hN : ∀ x ∈ N, x ≠ j₁) : nbrs (smooth G j₁ n n') j₂ = N := by
  apply nbrs_eq_of_mult
  · rw [smooth_mult_at G (Ne.symm hj), if_neg (Ne.symm hj), hl]
    rw [if_neg]; intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    exacts [hn.1 h1, hn.2 h1]
  · intro x hx
    have hxG := mem_verts_of_mem_nbrs (h2 ▸ hx)
    have hxj : x ≠ j₂ := fun h => not_mem_nbrs_self hl j₂ (by rw [h2, ← h]; exact hx)
    rw [smooth_verts hn'.1 hn'.2]
    exact ⟨Finset.mem_erase.mpr ⟨hN x hx, hxG⟩, hxj⟩
  · intro x hx
    rw [smooth_mult_at G (Ne.symm hj), ← mult_of_nbrs_eq h2 hx]
    by_cases hxj : x = j₁
    · rw [if_pos hxj, hxj, Sym2.eq_swap, hσ]
    · rw [if_neg hxj, if_neg, add_zero]
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hn.1 h1, hn.2 h1]

/-- In a `σ = 1` situation (`nbrs j₁ = {j₂, x}`, `nbrs j₂ = {j₁, y}`), after smoothing `j₁` the neighbours of `j₂`
are `x, y`. -/
theorem nbrs_smooth_adj {G : UMultigraph V} {j₁ j₂ x y : V} (hl : G.Loopless) (hj : j₁ ≠ j₂)
    (h1 : nbrs G j₁ = {j₂, x}) (h2 : nbrs G j₂ = {j₁, y}) (hxj₂ : x ≠ j₂) (hyj₁ : y ≠ j₁) :
    nbrs (smooth G j₁ j₂ x) j₂ = {x, y} := by
  have hxj₁ := (nbrs_mem_ne hl h1).2
  have hyj₂ := (nbrs_mem_ne hl h2).2
  have hxV := (nbrs_mem_verts h1).2
  have hj₂V := (nbrs_mem_verts h1).1
  apply nbrs_eq_of_mult
  · rw [smooth_mult_at G (Ne.symm hj), if_neg (Ne.symm hj), hl, if_neg]
    rw [Sym2.congr_right]; exact Ne.symm hxj₂
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rw [smooth_verts hj₂V hxV]
    rcases hz with rfl | rfl
    · exact ⟨Finset.mem_erase.mpr ⟨hxj₁, hxV⟩, hxj₂⟩
    · exact ⟨Finset.mem_erase.mpr ⟨hyj₁, (nbrs_mem_verts h2).2⟩, hyj₂⟩
  · intro z hz
    rw [smooth_mult_at G (Ne.symm hj)]
    by_cases hzj : z = j₁
    · subst hzj; rw [if_pos rfl, count_pair_of_ne hxj₁.symm, if_neg hyj₁.symm]
    · rw [if_neg hzj, mult_of_nbrs_eq h2 hz, count_pair_of_ne hzj]
      have hiff : (s(j₂, z) = s(j₂, x)) ↔ z = x := Sym2.congr_right
      by_cases hzx : z = x
      · rw [if_pos (hiff.mpr hzx), hzx, count_pair_self, add_comm]
      · rw [if_neg (mt hiff.mp hzx), count_pair_of_ne hzx, add_zero]

/-- **The closure is two smoothings.** -/
theorem IsClosureU.eq_smooth {G C : UMultigraph V} {j₁ j₂ : V} (hl : G.Loopless) (hj : j₁ ≠ j₂)
    (hC : IsClosureU G j₁ j₂ C) :
    ∃ n1 n1' n2 n2' : V, nbrs G j₁ = {n1, n1'} ∧ nbrs (smooth G j₁ n1 n1') j₂ = {n2, n2'} ∧
      C = smooth (smooth G j₁ n1 n1') j₂ n2 n2' := by
  obtain ⟨hσ, hV, -, added, hdata, hm⟩ := hC
  rcases hdata with ⟨hσ0, a, b, c, d, h1, h2, rfl⟩ | ⟨hσ1, x, y, h1, h2, rfl⟩
  · have hab := nbrs_mem_ne hl h1
    have hcd := nbrs_mem_ne hl h2
    have habV := nbrs_mem_verts h1
    have hcdV := nbrs_mem_verts h2
    have hj₂ab : j₂ ≠ a ∧ j₂ ≠ b := by
      have := mult_of_nbrs_eq h1 (Ne.symm hj)
      rw [hσ0] at this
      have h0 := (Multiset.count_eq_zero.mp this.symm)
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at h0
      exact h0
    have hj₁cd : j₁ ≠ c ∧ j₁ ≠ d := by
      have := mult_of_nbrs_eq h2 hj
      rw [Sym2.eq_swap, hσ0] at this
      have h0 := (Multiset.count_eq_zero.mp this.symm)
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at h0
      exact h0
    have hn2 : nbrs (smooth G j₁ a b) j₂ = {c, d} :=
      nbrs_smooth_far hl hj hσ0 hj₂ab habV h2 (by
        intro z hz; simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
        rcases hz with rfl | rfl
        exacts [Ne.symm hj₁cd.1, Ne.symm hj₁cd.2])
    refine ⟨a, b, c, d, h1, hn2, ext ?_ fun e => ?_⟩
    · have hcdS := nbrs_mem_verts hn2
      rw [hV, smooth_verts hcdS.1 hcdS.2, smooth_verts habV.1 habV.2]
    · rw [hm, smooth_mult, smooth_mult, count_pair]
      by_cases h₂ : j₂ ∈ e
      · rw [if_pos h₂, if_pos (Or.inr h₂)]
        have e1 : e ≠ s(a, b) := fun h => by
          rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hj₂ab.1 h, hj₂ab.2 h]
        have e2 : e ≠ s(c, d) := fun h => by
          rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hcd.1 h.symm, hcd.2 h.symm]
        rw [if_neg e1, if_neg e2]
      · rw [if_neg h₂]
        by_cases h₁ : j₁ ∈ e
        · rw [if_pos (Or.inl h₁), if_pos h₁]
          have e1 : e ≠ s(a, b) := fun h => by
            rw [h] at h₁; rcases Sym2.mem_iff.mp h₁ with h | h; exacts [hab.1 h.symm, hab.2 h.symm]
          have e2 : e ≠ s(c, d) := fun h => by
            rw [h] at h₁; rcases Sym2.mem_iff.mp h₁ with h | h; exacts [hj₁cd.1 h, hj₁cd.2 h]
          rw [if_neg e1, if_neg e2]
        · rw [if_neg (by tauto), if_neg h₁]; ring
  · have hx := (nbrs_mem_ne hl h1).2
    have hy := (nbrs_mem_ne hl h2).2
    have hxj₂ : x ≠ j₂ := by
      intro h
      have := mult_of_nbrs_eq h1 (Ne.symm hj)
      rw [hσ1, h, count_pair_self] at this; simp at this
    have hyj₁ : y ≠ j₁ := by
      intro h
      have := mult_of_nbrs_eq h2 hj
      rw [Sym2.eq_swap, hσ1, h, count_pair_self] at this; simp at this
    have hn2 := nbrs_smooth_adj hl hj h1 h2 hxj₂ hyj₁
    refine ⟨j₂, x, x, y, h1, hn2, ext ?_ fun e => ?_⟩
    · have hS := nbrs_mem_verts hn2
      have h1V := nbrs_mem_verts h1
      rw [hV, smooth_verts hS.1 hS.2, smooth_verts h1V.1 h1V.2]
    · rw [hm, smooth_mult, smooth_mult, Multiset.count_singleton]
      by_cases h₂ : j₂ ∈ e
      · rw [if_pos h₂, if_pos (Or.inr h₂)]
        have e2 : e ≠ s(x, y) := fun h => by
          rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hxj₂ h.symm, hy h.symm]
        rw [if_neg e2]
      · rw [if_neg h₂]
        by_cases h₁ : j₁ ∈ e
        · rw [if_pos (Or.inl h₁), if_pos h₁]
        · have e1 : e ≠ s(j₂, x) := fun h => h₂ (h ▸ Sym2.mem_mk_left j₂ x)
          rw [if_neg (by tauto), if_neg h₁, if_neg e1, add_zero]

theorem not_mem_nbrs_of_loop {G : UMultigraph V} {v : V} (h : G.mult s(v, v) = 0) : v ∉ nbrs G v := by
  intro hm
  have := Multiset.count_pos.mpr hm
  rw [count_nbrs, h] at this
  simp at this

/-- Two smoothings, `σ = 0` normal form. -/
theorem smooth2_mult_σ0 (G : UMultigraph V) {j₁ j₂ n1 n1' n2 n2' : V} (hn1 : n1 ≠ j₁ ∧ n1' ≠ j₁)
    (hn1' : n1 ≠ j₂ ∧ n1' ≠ j₂) (hn2 : n2 ≠ j₁ ∧ n2' ≠ j₁) (hn2' : n2 ≠ j₂ ∧ n2' ≠ j₂) (e : Sym2 V) :
    (smooth (smooth G j₁ n1 n1') j₂ n2 n2').mult e =
      (if j₁ ∈ e ∨ j₂ ∈ e then 0 else G.mult e) + ({s(n1, n1'), s(n2, n2')} : Multiset (Sym2 V)).count e := by
  rw [smooth_mult, smooth_mult, count_pair]
  by_cases h₂ : j₂ ∈ e
  · rw [if_pos h₂, if_pos (Or.inr h₂)]
    have e1 : e ≠ s(n1, n1') := fun h => by
      rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hn1'.1 h.symm, hn1'.2 h.symm]
    have e2 : e ≠ s(n2, n2') := fun h => by
      rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hn2'.1 h.symm, hn2'.2 h.symm]
    rw [if_neg e1, if_neg e2]
  · rw [if_neg h₂]
    by_cases h₁ : j₁ ∈ e
    · rw [if_pos (Or.inl h₁), if_pos h₁]
      have e1 : e ≠ s(n1, n1') := fun h => by
        rw [h] at h₁; rcases Sym2.mem_iff.mp h₁ with h | h; exacts [hn1.1 h.symm, hn1.2 h.symm]
      have e2 : e ≠ s(n2, n2') := fun h => by
        rw [h] at h₁; rcases Sym2.mem_iff.mp h₁ with h | h; exacts [hn2.1 h.symm, hn2.2 h.symm]
      rw [if_neg e1, if_neg e2]
    · have h12 : ¬ (j₁ ∈ e ∨ j₂ ∈ e) := by tauto
      rw [if_neg h₁, if_neg h12]; ring

/-- Two smoothings, `σ = 1` normal form. -/
theorem smooth2_mult_σ1 (G : UMultigraph V) {j₁ j₂ x y : V} (hx : x ≠ j₁ ∧ x ≠ j₂) (hy : y ≠ j₁ ∧ y ≠ j₂)
    (e : Sym2 V) :
    (smooth (smooth G j₁ j₂ x) j₂ x y).mult e =
      (if j₁ ∈ e ∨ j₂ ∈ e then 0 else G.mult e) + ({s(x, y)} : Multiset (Sym2 V)).count e := by
  rw [smooth_mult, smooth_mult, Multiset.count_singleton]
  by_cases h₂ : j₂ ∈ e
  · rw [if_pos h₂, if_pos (Or.inr h₂)]
    have e2 : e ≠ s(x, y) := fun h => by
      rw [h] at h₂; rcases Sym2.mem_iff.mp h₂ with h | h; exacts [hx.2 h.symm, hy.2 h.symm]
    rw [if_neg e2]
  · rw [if_neg h₂]
    by_cases h₁ : j₁ ∈ e
    · rw [if_pos (Or.inl h₁), if_pos h₁]
    · have e1 : e ≠ s(j₂, x) := fun h => h₂ (h ▸ Sym2.mem_mk_left j₂ x)
      have h12 : ¬ (j₁ ∈ e ∨ j₂ ∈ e) := by tauto
      rw [if_neg h₁, if_neg h12, if_neg e1, add_zero]

/-- **Two smoothings give the closure.** -/
theorem isClosureU_of_smooth {G : UMultigraph V} {j₁ j₂ n1 n1' n2 n2' : V} (hl : G.Loopless) (hj : j₁ ≠ j₂)
    (hσ : G.mult s(j₁, j₂) < 2) (h1 : nbrs G j₁ = {n1, n1'}) (h2 : nbrs (smooth G j₁ n1 n1') j₂ = {n2, n2'})
    (hloop : (smooth (smooth G j₁ n1 n1') j₂ n2 n2').Loopless) :
    IsClosureU G j₁ j₂ (smooth (smooth G j₁ n1 n1') j₂ n2 n2') := by
  have hn1 := nbrs_mem_ne hl h1
  have hn1V := nbrs_mem_verts h1
  have hG₁V : (smooth G j₁ n1 n1').verts = G.verts.erase j₁ := smooth_verts hn1V.1 hn1V.2
  have hn2V := nbrs_mem_verts h2
  rw [hG₁V] at hn2V
  have hn2 : n2 ≠ j₁ ∧ n2' ≠ j₁ := ⟨(Finset.mem_erase.mp hn2V.1).1, (Finset.mem_erase.mp hn2V.2).1⟩
  have hσc : G.mult s(j₁, j₂) = ({n1, n1'} : Multiset V).count j₂ := mult_of_nbrs_eq h1 (Ne.symm hj)
  -- no loop at `j₂` after the first smoothing
  have hloop₁ : (smooth G j₁ n1 n1').mult s(j₂, j₂) = 0 := by
    rw [smooth_mult_at G (Ne.symm hj), if_neg (Ne.symm hj), hl, zero_add, if_neg]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    · rw [← h3, ← h4, count_pair_self] at hσc; simp at hσc; omega
  have hn2' : n2 ≠ j₂ ∧ n2' ≠ j₂ := by
    have := not_mem_nbrs_of_loop hloop₁
    rw [h2] at this
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at this
    exact ⟨Ne.symm this.1, Ne.symm this.2⟩
  have hverts : (smooth (smooth G j₁ n1 n1') j₂ n2 n2').verts = (G.verts.erase j₁).erase j₂ := by
    rw [smooth_verts (by rw [hG₁V]; exact hn2V.1) (by rw [hG₁V]; exact hn2V.2), hG₁V]
  by_cases hj₂n : j₂ = n1 ∨ j₂ = n1'
  · -- `σ = 1`
    obtain ⟨x, hx⟩ : ∃ x, ({n1, n1'} : Multiset V) = {j₂, x} := by
      rcases hj₂n with h | h
      · exact ⟨n1', by rw [h]⟩
      · exact ⟨n1, by rw [h, Multiset.pair_comm]⟩
    have hs : s(n1, n1') = s(j₂, x) := sym2_eq_of_pair_eq hx
    have hG₁ : smooth G j₁ n1 n1' = smooth G j₁ j₂ x := by rw [smooth, smooth, hs]
    rw [hx] at h1 hσc
    rw [hG₁] at h2 hloop hverts hG₁V ⊢
    rw [count_pair_self] at hσc
    have hxj₂ : x ≠ j₂ := by intro h; rw [h] at hσc; simp at hσc; omega
    have hσ1 : G.mult s(j₁, j₂) = 1 := by rw [hσc, if_neg (Ne.symm hxj₂)]
    have hxj₁ := (nbrs_mem_ne hl h1).2
    -- `x` is a neighbour of `j₂` after the smoothing
    have hxmem : x ∈ ({n2, n2'} : Multiset V) := by
      have := mult_of_nbrs_eq h2 hxj₂
      rw [smooth_mult_at G (Ne.symm hj), if_neg hxj₁, if_pos rfl] at this
      exact Multiset.count_pos.mp (by omega)
    obtain ⟨y, hy⟩ := pair_eq_of_mem hxmem
    have hs2 : s(n2, n2') = s(x, y) := sym2_eq_of_pair_eq hy
    rw [hy] at h2
    have hyj₁ : y ≠ j₁ := by
      rcases hn2 with ⟨h, h'⟩
      have : y ∈ ({n2, n2'} : Multiset V) := by rw [hy]; simp
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
      rcases this with rfl | rfl <;> assumption
    have hyj₂ : y ≠ j₂ := by
      have : y ∈ ({n2, n2'} : Multiset V) := by rw [hy]; simp
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
      rcases this with rfl | rfl <;> [exact hn2'.1; exact hn2'.2]
    have hsm : smooth (smooth G j₁ j₂ x) j₂ n2 n2' = smooth (smooth G j₁ j₂ x) j₂ x y := by
      unfold smooth; rw [hs2]
    rw [hsm] at hloop hverts ⊢
    have h2G : nbrs G j₂ = {j₁, y} := by
      apply nbrs_eq_of_mult _ (hl j₂)
      · intro z hz
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨G.supp _ (by omega) z (Sym2.mem_mk_left z j₂), hj⟩
        · have := nbrs_mem_verts h2
          rw [hG₁V] at this
          exact ⟨Finset.mem_of_mem_erase this.2, hyj₂⟩
      · intro z hz
        by_cases hzj : z = j₁
        · subst hzj; rw [Sym2.eq_swap, hσ1, count_pair_self, if_neg (Ne.symm hyj₁)]
        · rw [count_pair_of_ne hzj]
          have := mult_of_nbrs_eq h2 hz
          rw [smooth_mult_at G (Ne.symm hj), if_neg hzj] at this
          have hiff : (s(j₂, z) = s(j₂, x)) ↔ z = x := Sym2.congr_right
          by_cases hzx : z = x
          · rw [if_pos (hiff.mpr hzx), hzx, count_pair_self] at this
            rw [hzx]
            split_ifs at this ⊢ <;> omega
          · rw [if_neg (mt hiff.mp hzx), count_pair_of_ne hzx, add_zero] at this
            exact this
    refine ⟨by omega, hverts, hloop, {s(x, y)}, Or.inr ⟨hσ1, x, y, h1, h2G, rfl⟩, fun e => ?_⟩
    exact smooth2_mult_σ1 G ⟨hxj₁, hxj₂⟩ ⟨hyj₁, hyj₂⟩ e
  · -- `σ = 0`
    have hn1' : n1 ≠ j₂ ∧ n1' ≠ j₂ := ⟨fun h => hj₂n (Or.inl h.symm), fun h => hj₂n (Or.inr h.symm)⟩
    have hσ0 : G.mult s(j₁, j₂) = 0 := by
      rw [hσc, count_pair_of_ne (Ne.symm hn1'.1), if_neg (Ne.symm hn1'.2)]
    have h2G : nbrs G j₂ = {n2, n2'} := by
      apply nbrs_eq_of_mult _ (hl j₂)
      · intro z hz
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨Finset.mem_of_mem_erase hn2V.1, hn2'.1⟩
        · exact ⟨Finset.mem_of_mem_erase hn2V.2, hn2'.2⟩
      · intro z hz
        by_cases hzj : z = j₁
        · subst hzj
          rw [Sym2.eq_swap, hσ0, count_pair_of_ne (Ne.symm hn2.1), if_neg (Ne.symm hn2.2)]
        · have := mult_of_nbrs_eq h2 hz
          rw [smooth_mult_at G (Ne.symm hj), if_neg hzj, if_neg, add_zero] at this
          · exact this
          · intro h
            rcases Sym2.eq_iff.mp h with ⟨h3, _⟩ | ⟨h3, _⟩
            exacts [hn1'.1 h3.symm, hn1'.2 h3.symm]
    refine ⟨by omega, hverts, hloop, _, Or.inl ⟨hσ0, n1, n1', n2, n2', h1, h2G, rfl⟩, fun e => ?_⟩
    exact smooth2_mult_σ0 G hn1 hn1' hn2 hn2' e

end WaveTurbulence.TVine.Core
