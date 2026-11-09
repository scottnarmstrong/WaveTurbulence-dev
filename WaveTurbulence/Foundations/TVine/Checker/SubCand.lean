/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SoundClosure

/-!
# Sub-objects of `G` as candidates of the instance

* `deg_eq_sum`: the list degree as a sum of multiplicities; `degU_iso`: L1's `deg` through an isomorphism;
* `inner_closed`: every bond at an interior atom of a sub-object of a block stays inside the sub-object;
* `Iso.restrict`: isomorphisms of sub-multigraphs; `isoCore`: the core `U°` of a sub-object is isomorphic to the
  core list of its candidate;
* `selMask`, `selectComps_selMask`: choosing the components that make up an interior.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

/-! ## Degrees -/

theorem deg_cons (e : ℕ × ℕ) (es : Edges) (x : ℕ) :
    deg (e :: es) x = (if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0) + deg es x := by
  simp only [deg, List.filter_cons, nat_beq_eq_decide, decide_eq_true_eq]
  split_ifs <;> simp <;> omega

/-- The list degree as a sum of multiplicities over a set containing the ends (a loop counts twice). -/
theorem deg_eq_sum (es : Edges) (x : ℕ) (T : Finset ℕ) (hT : ∀ y, InEnds es y → y ∈ T) :
    deg es x = ∑ y ∈ T, mult es x y + mult es x x := by
  induction es with
  | nil => simp [deg]
  | cons e es ih =>
    have hT' : ∀ y, InEnds es y → y ∈ T := fun y hy => by
      obtain ⟨e', he', h⟩ := hy; exact hT y ⟨e', List.mem_cons_of_mem _ he', h⟩
    have h1 : e.1 ∈ T := hT e.1 ⟨e, List.mem_cons_self, Or.inl rfl⟩
    have h2 : e.2 ∈ T := hT e.2 ⟨e, List.mem_cons_self, Or.inr rfl⟩
    rw [deg_cons, ih hT']
    simp only [mult_cons, Finset.sum_add_distrib]
    have key : ∑ y ∈ T, (if isPair x y e = true then 1 else 0) + (if isPair x x e = true then 1 else 0) =
        (if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0) := by
      by_cases a1 : e.1 = x <;> by_cases a2 : e.2 = x
      · have h : ∀ y, isPair x y e = true ↔ y = x := by intro y; rw [isPair_iff]; omega
        have hx : x ∈ T := a1 ▸ h1
        simp [h, Finset.sum_ite_eq', hx, a1, a2]
      · have h : ∀ y, isPair x y e = true ↔ y = e.2 := by intro y; rw [isPair_iff]; omega
        simp [h, Finset.sum_ite_eq', h2, a1, a2, Ne.symm a2]
      · have h : ∀ y, isPair x y e = true ↔ y = e.1 := by intro y; rw [isPair_iff]; omega
        simp [h, Finset.sum_ite_eq', h1, a1, a2, Ne.symm a1]
      · have h : ∀ y, isPair x y e = true ↔ False := by intro y; rw [isPair_iff, iff_false]; omega
        simp [h, a1, a2]
    omega

variable {V : Type*} [DecidableEq V]

/-- L1's degree through an isomorphism. -/
theorem degU_iso {H : UMultigraph V} {c : Edges} (φ : Iso H c) {v : V} (hv : v ∈ H.verts) :
    Core.deg H v = deg c (φ.f v) := by
  unfold Core.deg
  rw [deg_eq_sum c (φ.f v) (H.verts.image φ.f) (fun y hy => Finset.mem_image.mpr ⟨φ.g y, φ.gv y hy, φ.fg y hy⟩),
    Finset.sum_image (fun x hx y hy h => φ.f_injOn hx hy h), φ.mult_eq v hv v hv]
  congr 1
  exact Finset.sum_congr rfl fun w hw => φ.mult_eq v hv w hw

/-! ## Cores of sub-objects -/

theorem core_verts (G : UMultigraph V) (U : SubObj V) : (U.core G).verts = U.atoms := by
  unfold SubObj.core SubObj.edges
  split_ifs <;> rfl

theorem core_mult_le (G : UMultigraph V) (U : SubObj V) (e : Sym2 V) : (U.core G).mult e ≤ G.mult e := by
  unfold SubObj.core SubObj.edges
  split_ifs
  · simp only [eraseBond, induce]; split_ifs <;> omega
  · simp only [induce]; split_ifs <;> omega

theorem core_mult_of_mem (G : UMultigraph V) (U : SubObj V) {u v : V} (hu : u ∈ U.atoms) (hv : v ∈ U.atoms) :
    (U.core G).mult s(u, v) =
      G.mult s(u, v) - (if U.hyper = true ∧ s(u, v) = s(U.k₁, U.k₂) then 1 else 0) := by
  have hs : s(u, v) ∈ U.atoms.sym2 := Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩
  unfold SubObj.core SubObj.edges
  by_cases hh : U.hyper = true
  · simp only [hh, if_true, eraseBond, induce, hs, true_and]
    split_ifs <;> simp_all
  · simp only [hh, if_false, induce, hs, Bool.false_eq_true, false_and]; simp

/-- **Interior closedness**: in a multigraph of degree ≤ 4, every bond at an interior atom of a sub-object has its
other end in the sub-object. -/
theorem inner_closed {G : UMultigraph V} (hdeg : ∀ v ∈ G.verts, Core.deg G v ≤ 4) {U : SubObj V}
    (hU : IsSubObjU G U) {v w : V} (hv : v ∈ U.inner) (hvw : G.mult s(v, w) ≠ 0) : w ∈ U.atoms := by
  obtain ⟨hsub, -, hB⟩ := hU
  obtain ⟨-, -, -, -, -, hd4, -⟩ := hB
  have hvU : v ∈ U.atoms := by simp only [SubObj.inner, Finset.mem_erase] at hv; exact hv.2.2
  have hvk : v ≠ U.k₁ ∧ v ≠ U.k₂ := by simp only [SubObj.inner, Finset.mem_erase] at hv; exact ⟨hv.2.1, hv.1⟩
  have h4 := hd4 v (by rw [core_verts]; exact hvU) hvk.1 hvk.2
  have hvG : v ∈ G.verts := hsub.1 hvU
  have hG := hdeg v hvG
  by_contra hw
  have hwG : w ∈ G.verts := G.supp _ hvw w (Sym2.mem_mk_right v w)
  unfold Core.deg at h4 hG
  rw [core_verts] at h4
  have le1 : ∑ x ∈ U.atoms, (U.core G).mult s(v, x) ≤ ∑ x ∈ U.atoms, G.mult s(v, x) :=
    Finset.sum_le_sum fun x _ => core_mult_le G U _
  have le2 : ∑ x ∈ U.atoms, G.mult s(v, x) + G.mult s(v, w) ≤ ∑ x ∈ G.verts, G.mult s(v, x) := by
    have hi := Finset.sum_insert (s := U.atoms) (a := w) (f := fun x => G.mult s(v, x)) hw
    rw [Nat.add_comm, ← hi]
    exact Finset.sum_le_sum_of_subset (Finset.insert_subset hwG hsub.1)
  have le3 := core_mult_le G U s(v, v)
  omega

/-! ## Restricting an isomorphism -/

/-- An isomorphism of a sub-multigraph, given the multiplicities and the ends. -/
def Iso.restrict {G H : UMultigraph V} {es es' : Edges} (φ : Iso G es) (hHG : H.verts ⊆ G.verts)
    (hends : ∀ z, InEnds es' z ↔ InEnds es z ∧ φ.g z ∈ H.verts)
    (hmult : ∀ u ∈ H.verts, ∀ v ∈ H.verts, H.mult s(u, v) = mult es' (φ.f u) (φ.f v)) : Iso H es' where
  f := φ.f
  g := φ.g
  gf := fun v hv => φ.gf v (hHG hv)
  fg := fun z hz => φ.fg z ((hends z).mp hz).1
  fv := fun v hv => (hends _).mpr ⟨φ.fv v (hHG hv), by rw [φ.gf v (hHG hv)]; exact hv⟩
  gv := fun z hz => ((hends z).mp hz).2
  mult_eq := hmult

/-! ## Components and their selection -/

theorem mem_grow_of_mem : ∀ (es : Edges) (R : ℕ) {v : ℕ}, mem v R = true → mem v (grow es R) = true
  | [], _, _, h => h
  | e :: es, R, v, h => by
    simp only [grow]
    apply mem_grow_of_mem
    split
    · simp [h]
    · exact h

theorem mem_reach_of_mem : ∀ (k : ℕ) (es : Edges) (R : ℕ) {v : ℕ}, mem v R = true → mem v (reach k es R) = true
  | 0, _, _, _, h => h
  | k + 1, es, R, v, h => by
    simp only [reach]
    split
    · exact h
    · exact mem_reach_of_mem k es _ (mem_grow_of_mem es R h)

theorem mem_comp_self (es : Edges) (s : ℕ) : mem s (comp es s) = true :=
  mem_reach_of_mem 16 es _ (by simp)

/-- Every component is connected from one of its members. -/
theorem comps_conn : ∀ (k : ℕ) (es : Edges) (W : ℕ) {X : ℕ}, X ∈ comps k es W →
    ∃ s, mem s X = true ∧ Reached es s X
  | 0, _, _, _, h => by simp [comps] at h
  | k + 1, es, W, X, h => by
    simp only [comps] at h
    split at h
    · simp at h
    · rename_i s _
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨s, mem_comp_self es s, comp_reached es s⟩
      · exact comps_conn k es _ h

theorem mem_foldr_or {z : ℕ} : ∀ (cs : List ℕ), mem z (cs.foldr (· ||| ·) 0) = true ↔ ∃ X ∈ cs, mem z X = true
  | [] => by simp
  | X :: cs => by simp [mem_foldr_or cs]

/-- The selection mask of the components satisfying `P`. -/
noncomputable def selMask (P : ℕ → Prop) : List ℕ → ℕ
  | [] => 0
  | X :: cs => (by classical exact if P X then 1 else 0) + 2 * selMask P cs

theorem selMask_lt (P : ℕ → Prop) : ∀ cs : List ℕ, selMask P cs < 2 ^ cs.length
  | [] => by simp [selMask]
  | X :: cs => by
    have := selMask_lt P cs
    simp only [selMask, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem mem_selectComps (P : ℕ → Prop) {z : ℕ} : ∀ cs : List ℕ,
    mem z (selectComps cs (selMask P cs)) = true ↔ ∃ X ∈ cs, P X ∧ mem z X = true
  | [] => by simp [selectComps]
  | X :: cs => by
    classical
    simp only [selectComps, selMask, mem_or, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    have h2 : ((if P X then 1 else 0) + 2 * selMask P cs) / 2 = selMask P cs := by split_ifs <;> omega
    rw [h2, mem_selectComps P cs]
    by_cases hP : P X
    · have : ((if P X then 1 else 0) + 2 * selMask P cs) % 2 = 1 := by simp [hP]
      simp [this, hP]
    · have : ((if P X then 1 else 0) + 2 * selMask P cs) % 2 = 0 := by simp [hP]
      simp [this, hP]

end WaveTurbulence.TVine.Checker
