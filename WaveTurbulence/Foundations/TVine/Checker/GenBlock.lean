/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.GenStep
public import WaveTurbulence.Foundations.TVine.Checker.Statement

/-!
# Generation of T-vines (N2 Lemma 1.7, with the joints)

* `iso_extend2`: the bookkeeping of extending an isomorphism `C ≅ es` by two new vertices `j₁ ↦ J₁`, `j₂ ↦ J₂`;
* `placeTwo`, `placeOne`: the joints placed on two bonds (`σ = 0`) or twice on one bond (`σ = 1`), with arbitrary
  joint names, and their multiplicities;
* `iso_two`, `iso_one`: a block whose closure is `C ≅ es` is isomorphic to the placed bond list;
* `generation`: **`GenerationStatement`** (N2 Lemma 1.7; M4 Lemma 1.7′, direction ⇒), with normalized placements.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

universe u

variable {V : Type*} [DecidableEq V]

/-! ## Extending an isomorphism by two vertices -/

/-- Extending `φ : C ≅ es` to `G ≅ es'`, where `G` has the two extra vertices `j₁, j₂` sent to fresh `J₁, J₂`. -/
def iso_extend2 {G C : UMultigraph V} {es es' : Edges} (φ : Iso C es) {j₁ j₂ : V} {J₁ J₂ : ℕ}
    (hj : j₁ ≠ j₂) (hJ : J₁ ≠ J₂) (hJ₁ : ¬ InEnds es J₁) (hJ₂ : ¬ InEnds es J₂)
    (hGv : ∀ v, v ∈ G.verts ↔ v = j₁ ∨ v = j₂ ∨ v ∈ C.verts) (hj₁C : j₁ ∉ C.verts) (hj₂C : j₂ ∉ C.verts)
    (hends : ∀ z, InEnds es' z ↔ InEnds es z ∨ z = J₁ ∨ z = J₂)
    (F : V → ℕ) (hF₁ : F j₁ = J₁) (hF₂ : F j₂ = J₂) (hFv : ∀ v ∈ C.verts, F v = φ.f v)
    (hmult : ∀ u ∈ G.verts, ∀ v ∈ G.verts, G.mult s(u, v) = mult es' (F u) (F v)) : Iso G es' where
  f := F
  g := fun z => if z = J₁ then j₁ else if z = J₂ then j₂ else φ.g z
  gf := by
    intro v hv
    rcases (hGv v).mp hv with rfl | rfl | hv
    · simp [hF₁]
    · simp [hF₂, Ne.symm hJ]
    · have hf := φ.fv v hv
      have h1 : φ.f v ≠ J₁ := fun h => hJ₁ (h ▸ hf)
      have h2 : φ.f v ≠ J₂ := fun h => hJ₂ (h ▸ hf)
      simp [hFv v hv, h1, h2, φ.gf v hv]
  fg := by
    intro z hz
    rcases (hends z).mp hz with hz | rfl | rfl
    · have h1 : z ≠ J₁ := fun h => hJ₁ (h ▸ hz)
      have h2 : z ≠ J₂ := fun h => hJ₂ (h ▸ hz)
      simp only [h1, h2, if_false]
      rw [hFv _ (φ.gv z hz), φ.fg z hz]
    · simp [hF₁]
    · simp [hF₂, Ne.symm hJ]
  fv := by
    intro v hv
    rw [hends]
    rcases (hGv v).mp hv with rfl | rfl | hv
    · exact Or.inr (Or.inl hF₁)
    · exact Or.inr (Or.inr hF₂)
    · rw [hFv v hv]; exact Or.inl (φ.fv v hv)
  gv := by
    intro z hz
    rcases (hends z).mp hz with hz | rfl | rfl
    · have h1 : z ≠ J₁ := fun h => hJ₁ (h ▸ hz)
      have h2 : z ≠ J₂ := fun h => hJ₂ (h ▸ hz)
      simp only [h1, h2, if_false]
      exact (hGv _).mpr (Or.inr (Or.inr (φ.gv z hz)))
    · simp only [if_true]; exact (hGv _).mpr (Or.inl rfl)
    · simp only [Ne.symm hJ, if_false, if_true]; exact (hGv _).mpr (Or.inr (Or.inl rfl))
  mult_eq := hmult

/-! ## Placing the joints -/

/-- Two joints `J₁`, `J₂` subdividing the bonds `X₁–Y₁` and `X₂–Y₂`. -/
def placeTwo (es : Edges) (X₁ Y₁ J₁ X₂ Y₂ J₂ : ℕ) : Edges :=
  eraseOne (eraseOne es X₁ Y₁) X₂ Y₂ ++ [(X₁, J₁), (J₁, Y₁), (X₂, J₂), (J₂, Y₂)]

/-- The path `X–J₁–J₂–Y` replacing the bond `X–Y`. -/
def placeOne (es : Edges) (X Y J₁ J₂ : ℕ) : Edges := eraseOne es X Y ++ [(X, J₁), (J₁, J₂), (J₂, Y)]

theorem placeJ_two (es : Edges) (n x₁ y₁ x₂ y₂ : ℕ) :
    placeJ es n (.two x₁ y₁ x₂ y₂) = placeTwo es x₁ y₁ n x₂ y₂ (n + 1) := rfl

theorem placeJ_one (es : Edges) (n x y : ℕ) : placeJ es n (.one x y) = placeOne es x y n (n + 1) := rfl

/-- Indicator of a pair. -/
def ind (u v x y : ℕ) : ℕ := if s(u, v) = s(x, y) then 1 else 0

theorem mult_list_cons (x y : ℕ) (es : Edges) (u v : ℕ) : mult ((x, y) :: es) u v = ind u v x y + mult es u v := by
  rw [mult_cons]
  unfold ind
  by_cases h : s(u, v) = s(x, y)
  · rw [if_pos h, if_pos ((isPair_iff_sym2 u v (x, y)).mpr h.symm)]
  · rw [if_neg h, if_neg (fun hh => h ((isPair_iff_sym2 u v (x, y)).mp hh).symm)]

/-- Removability of the two bonds. -/
def Removable2 (es : Edges) (X₁ Y₁ X₂ Y₂ : ℕ) : Prop :=
  1 ≤ mult es X₁ Y₁ ∧ 1 + ind X₂ Y₂ X₁ Y₁ ≤ mult es X₂ Y₂

theorem mult_eraseOne' {es : Edges} {x y : ℕ} (h : mult es x y ≠ 0) (u v : ℕ) :
    mult (eraseOne es x y) u v + ind u v x y = mult es u v := mult_eraseOne es x y u v h

theorem Removable2.second {es : Edges} {X₁ Y₁ X₂ Y₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) :
    mult (eraseOne es X₁ Y₁) X₂ Y₂ ≠ 0 := by
  have := mult_eraseOne' (show mult es X₁ Y₁ ≠ 0 by have := h.1; omega) X₂ Y₂
  have := h.2; omega

theorem mult_placeTwo {es : Edges} {X₁ Y₁ J₁ X₂ Y₂ J₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) (u v : ℕ) :
    mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) u v + ind u v X₁ Y₁ + ind u v X₂ Y₂ =
      mult es u v + ind u v X₁ J₁ + ind u v J₁ Y₁ + ind u v X₂ J₂ + ind u v J₂ Y₂ := by
  have h1 := mult_eraseOne' (show mult es X₁ Y₁ ≠ 0 by have := h.1; omega) u v
  have h2 := mult_eraseOne' h.second u v
  simp only [placeTwo, mult_append, mult_list_cons, mult_nil]
  omega

theorem mult_placeOne {es : Edges} {X Y J₁ J₂ : ℕ} (h : mult es X Y ≠ 0) (u v : ℕ) :
    mult (placeOne es X Y J₁ J₂) u v + ind u v X Y = mult es u v + ind u v X J₁ + ind u v J₁ J₂ + ind u v J₂ Y := by
  have h1 := mult_eraseOne' h u v
  simp only [placeOne, mult_append, mult_list_cons, mult_nil]
  omega

theorem ind_swap (u v x y : ℕ) : ind u v x y = ind u v y x := by
  unfold ind; rw [Sym2.eq_swap (a := x)]

theorem ind_comm (u v x y : ℕ) : ind u v x y = ind v u x y := by
  unfold ind; rw [Sym2.eq_swap (a := u)]

theorem inEnds_placeTwo {es : Edges} {X₁ Y₁ J₁ X₂ Y₂ J₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) (z : ℕ) :
    InEnds (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) z ↔ InEnds es z ∨ z = J₁ ∨ z = J₂ := by
  have hX := inEnds_of_mult_ne_zero (show mult es X₁ Y₁ ≠ 0 by have := h.1; omega)
  have hX2 := inEnds_of_mult_ne_zero (show mult es X₂ Y₂ ≠ 0 by have := h.2; omega)
  constructor
  · intro hz
    rcases inEnds_append.mp hz with hz | ⟨e, he, hz⟩
    · exact Or.inl (inEnds_eraseOne (inEnds_eraseOne hz))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> rcases hz with hz | hz <;> simp only at hz <;> subst hz <;>
        simp_all
  · rintro (hz | rfl | rfl)
    · obtain ⟨w, hw⟩ := inEnds_iff.mp hz
      have := mult_placeTwo (J₁ := J₁) (J₂ := J₂) h z w
      by_cases h1 : s(z, w) = s(X₁, Y₁)
      · rw [Sym2.eq_iff] at h1
        rcases h1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact inEnds_append.mpr (Or.inr ⟨(z, J₁), by simp, Or.inl rfl⟩)
        · exact inEnds_append.mpr (Or.inr ⟨(J₁, z), by simp, Or.inr rfl⟩)
      by_cases h2 : s(z, w) = s(X₂, Y₂)
      · rw [Sym2.eq_iff] at h2
        rcases h2 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact inEnds_append.mpr (Or.inr ⟨(z, J₂), by simp, Or.inl rfl⟩)
        · exact inEnds_append.mpr (Or.inr ⟨(J₂, z), by simp, Or.inr rfl⟩)
      · refine inEnds_iff.mpr ⟨w, ?_⟩
        unfold ind at this
        rw [if_neg h1, if_neg h2] at this
        omega
    · exact inEnds_append.mpr (Or.inr ⟨(X₁, z), by simp, Or.inr rfl⟩)
    · exact inEnds_append.mpr (Or.inr ⟨(X₂, z), by simp, Or.inr rfl⟩)

theorem inEnds_placeOne {es : Edges} {X Y J₁ J₂ : ℕ} (h : mult es X Y ≠ 0) (z : ℕ) :
    InEnds (placeOne es X Y J₁ J₂) z ↔ InEnds es z ∨ z = J₁ ∨ z = J₂ := by
  have hX := inEnds_of_mult_ne_zero h
  constructor
  · intro hz
    rcases inEnds_append.mp hz with hz | ⟨e, he, hz⟩
    · exact Or.inl (inEnds_eraseOne hz)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> rcases hz with hz | hz <;> simp only at hz <;> subst hz <;>
        simp_all
  · rintro (hz | rfl | rfl)
    · obtain ⟨w, hw⟩ := inEnds_iff.mp hz
      have := mult_placeOne (J₁ := J₁) (J₂ := J₂) h z w
      by_cases h1 : s(z, w) = s(X, Y)
      · rw [Sym2.eq_iff] at h1
        rcases h1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact inEnds_append.mpr (Or.inr ⟨(z, J₁), by simp, Or.inl rfl⟩)
        · exact inEnds_append.mpr (Or.inr ⟨(J₂, z), by simp, Or.inr rfl⟩)
      · refine inEnds_iff.mpr ⟨w, ?_⟩
        unfold ind at this
        rw [if_neg h1] at this
        omega
    · exact inEnds_append.mpr (Or.inr ⟨(X, z), by simp, Or.inr rfl⟩)
    · exact inEnds_append.mpr (Or.inr ⟨(J₁, z), by simp, Or.inr rfl⟩)

/-! ## Evaluating indicators -/

theorem ind_eq_zero {u v x y : ℕ} (h : ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : ind u v x y = 0 := by
  unfold ind; rw [if_neg]; rwa [Sym2.eq_iff]

theorem ind_eq_one {u v x y : ℕ} (h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)) : ind u v x y = 1 := by
  unfold ind; rw [if_pos]; rwa [Sym2.eq_iff]

theorem ind_left (u v x : ℕ) (h : u ≠ x) : ind u v x u = if v = x then 1 else 0 := by
  split_ifs with hv
  · exact ind_eq_one (Or.inr ⟨rfl, hv⟩)
  · exact ind_eq_zero (by omega)

theorem ind_right (u v y : ℕ) (h : u ≠ y) : ind u v u y = if v = y then 1 else 0 := by
  split_ifs with hv
  · exact ind_eq_one (Or.inl ⟨rfl, hv⟩)
  · exact ind_eq_zero (by omega)

theorem count_pair {α : Type*} [DecidableEq α] (a b w : α) :
    ({a, b} : Multiset α).count w = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases h1 : w = a <;> by_cases h2 : w = b <;> simp [h1, h2, eq_comm] <;> omega

/-! ## The isomorphism of a block from that of its closure -/

theorem memC {G C : UMultigraph V} {j₁ j₂ : V} (hCv : C.verts = (G.verts.erase j₁).erase j₂) (v : V) :
    v ∈ C.verts ↔ v ∈ G.verts ∧ v ≠ j₁ ∧ v ≠ j₂ := by
  rw [hCv]; simp only [Finset.mem_erase]; tauto

theorem joint_row {G : UMultigraph V} {j : V} {R : Multiset V} (hn : Core.nbrs G j = R) {w : V} (hw : w ∈ G.verts)
    (hjw : j ≠ w) : G.mult s(j, w) = R.count w := by
  rw [← hn, Core.count_nbrs]; simp [hw, hjw]

theorem joint_loop {G : UMultigraph V} {j : V} {R : Multiset V} (hn : Core.nbrs G j = R) (hj : j ∈ G.verts)
    (hR : R.count j = 0) : G.mult s(j, j) = 0 := by
  have := Core.count_nbrs G j j
  rw [hn, hR] at this; simp [hj] at this; omega

theorem ite_one_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then 1 else 0 : ℕ) = if q then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-- **The joints, `σ = 0`.** -/
theorem iso_two {G C : UMultigraph V} {es : Edges} (φ : Iso C es) {j₁ j₂ a b c d : V} {J₁ J₂ : ℕ}
    (hJ : J₁ ≠ J₂) (hJ₁ : ¬ InEnds es J₁) (hJ₂ : ¬ InEnds es J₂)
    (hj : j₁ ≠ j₂) (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts)
    (hCv : C.verts = (G.verts.erase j₁).erase j₂) (hloop : C.Loopless)
    (hσ : G.mult s(j₁, j₂) = 0) (hn₁ : Core.nbrs G j₁ = {a, b}) (hn₂ : Core.nbrs G j₂ = {c, d})
    (hCm : ∀ e, C.mult e = (if j₁ ∈ e ∨ j₂ ∈ e then 0 else G.mult e) +
      ({s(a, b), s(c, d)} : Multiset (Sym2 V)).count e) :
    Removable2 es (φ.f a) (φ.f b) (φ.f c) (φ.f d) ∧
      ∃ ψ : Iso G (placeTwo es (φ.f a) (φ.f b) J₁ (φ.f c) (φ.f d) J₂), ψ.f j₁ = J₁ ∧ ψ.f j₂ = J₂ := by
  have cnt := fun e => count_pair (s(a, b)) (s(c, d)) e
  have hge : ∀ e, ({s(a, b), s(c, d)} : Multiset (Sym2 V)).count e ≤ C.mult e := fun e => by
    rw [hCm e]; omega
  have hCab : 1 + (if s(c, d) = s(a, b) then 1 else 0) ≤ C.mult s(a, b) := by
    have := hge (s(a, b)); rw [cnt, if_pos rfl, ite_one_iff eq_comm] at this; exact this
  have hCcd : 1 + (if s(c, d) = s(a, b) then 1 else 0) ≤ C.mult s(c, d) := by
    have := hge (s(c, d)); rw [cnt, if_pos rfl] at this; omega
  have mem : ∀ x y, 1 ≤ C.mult s(x, y) → x ∈ C.verts ∧ y ∈ C.verts := fun x y h =>
    ⟨C.supp _ (by omega) x (Sym2.mem_mk_left x y), C.supp _ (by omega) y (Sym2.mem_mk_right x y)⟩
  obtain ⟨ha, hb⟩ := mem a b (by omega)
  obtain ⟨hc, hd⟩ := mem c d (by omega)
  have hmemC := memC hCv
  -- the images
  have fe : ∀ v ∈ C.verts, InEnds es (φ.f v) ∧ φ.f v ≠ J₁ ∧ φ.f v ≠ J₂ := by
    intro v hv
    have := φ.fv v hv
    exact ⟨this, fun h => hJ₁ (h ▸ this), fun h => hJ₂ (h ▸ this)⟩
  have finj : ∀ u ∈ C.verts, ∀ v ∈ C.verts, φ.f u = φ.f v ↔ u = v := fun u hu v hv =>
    ⟨fun h => by rw [← φ.gf u hu, h, φ.gf v hv], fun h => h ▸ rfl⟩
  have fsym : ∀ u ∈ C.verts, ∀ v ∈ C.verts, ∀ x ∈ C.verts, ∀ y ∈ C.verts,
      (s(φ.f u, φ.f v) = s(φ.f x, φ.f y) ↔ s(u, v) = s(x, y)) := by
    intro u hu v hv x hx y hy
    simp only [Sym2.eq_iff, finj u hu x hx, finj v hv y hy, finj u hu y hy, finj v hv x hx]
  have hR : Removable2 es (φ.f a) (φ.f b) (φ.f c) (φ.f d) := by
    refine ⟨by rw [← φ.mult_eq a ha b hb]; omega, ?_⟩
    rw [← φ.mult_eq c hc d hd]
    unfold ind; rw [ite_one_iff (fsym c hc d hd a ha b hb)]; omega
  refine ⟨hR, iso_extend2 φ (G := G) hj hJ hJ₁ hJ₂ ?_ (fun h => ((hmemC j₁).mp h).2.1 rfl)
    (fun h => ((hmemC j₂).mp h).2.2 rfl) (inEnds_placeTwo hR)
    (fun v => if v = j₁ then J₁ else if v = j₂ then J₂ else φ.f v) (by simp) (by simp [Ne.symm hj])
    (fun v hv => by have := (hmemC v).mp hv; simp [this.2.1, this.2.2]) ?_,
    show (if j₁ = j₁ then J₁ else if j₁ = j₂ then J₂ else φ.f j₁) = J₁ by simp,
    show (if j₂ = j₁ then J₁ else if j₂ = j₂ then J₂ else φ.f j₂) = J₂ by simp [Ne.symm hj]⟩
  · intro v
    constructor
    · intro hv
      by_cases h1 : v = j₁
      · exact Or.inl h1
      by_cases h2 : v = j₂
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr ((hmemC v).mpr ⟨hv, h1, h2⟩))
    · rintro (rfl | rfl | hv)
      · exact hj₁
      · exact hj₂
      · exact ((hmemC v).mp hv).1
  -- the multiplicities
  set X₁ := φ.f a; set Y₁ := φ.f b; set X₂ := φ.f c; set Y₂ := φ.f d
  obtain ⟨eX₁, X₁J₁, X₁J₂⟩ := fe a ha
  obtain ⟨eY₁, Y₁J₁, Y₁J₂⟩ := fe b hb
  obtain ⟨eX₂, X₂J₁, X₂J₂⟩ := fe c hc
  obtain ⟨eY₂, Y₂J₁, Y₂J₂⟩ := fe d hd
  have aj : a ≠ j₁ ∧ b ≠ j₁ ∧ c ≠ j₂ ∧ d ≠ j₂ :=
    ⟨((hmemC a).mp ha).2.1, ((hmemC b).mp hb).2.1, ((hmemC c).mp hc).2.2, ((hmemC d).mp hd).2.2⟩
  have L₁ : G.mult s(j₁, j₁) = 0 := joint_loop hn₁ hj₁ (by rw [count_pair]; simp [Ne.symm aj.1, Ne.symm aj.2.1])
  have L₂ : G.mult s(j₂, j₂) = 0 :=
    joint_loop hn₂ hj₂ (by rw [count_pair]; simp [Ne.symm aj.2.2.1, Ne.symm aj.2.2.2])
  -- rows of the joints
  have row₁ : ∀ w ∈ C.verts, G.mult s(j₁, w) = mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) J₁ (φ.f w) := by
    intro w hw
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR J₁ (φ.f w)
    rw [mult_eq_zero_of_not_inEnds hJ₁, ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_left _ _ _ (Ne.symm X₁J₁), ind_right _ _ _ (Ne.symm Y₁J₁), ind_eq_zero (by omega),
      ind_eq_zero (by omega)] at key
    rw [joint_row hn₁ ((hmemC w).mp hw).1 (Ne.symm ((hmemC w).mp hw).2.1), count_pair]
    rw [ite_one_iff (finj w hw a ha), ite_one_iff (finj w hw b hb)] at key
    omega
  have row₂ : ∀ w ∈ C.verts, G.mult s(j₂, w) = mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) J₂ (φ.f w) := by
    intro w hw
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR J₂ (φ.f w)
    rw [mult_eq_zero_of_not_inEnds hJ₂, ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega), ind_eq_zero (by omega), ind_left _ _ _ (Ne.symm X₂J₂),
      ind_right _ _ _ (Ne.symm Y₂J₂)] at key
    rw [joint_row hn₂ ((hmemC w).mp hw).1 (Ne.symm ((hmemC w).mp hw).2.2), count_pair]
    rw [ite_one_iff (finj w hw c hc), ite_one_iff (finj w hw d hd)] at key
    omega
  have J11 : mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) J₁ J₁ = 0 := by
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR J₁ J₁
    rw [mult_eq_zero_of_not_inEnds hJ₁] at key
    rw [ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega), ind_eq_zero (by omega)] at key
    omega
  have J22 : mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) J₂ J₂ = 0 := by
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR J₂ J₂
    rw [mult_eq_zero_of_not_inEnds hJ₂] at key
    rw [ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega), ind_eq_zero (by omega)] at key
    omega
  have J12 : mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) J₁ J₂ = 0 := by
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR J₁ J₂
    rw [mult_eq_zero_of_not_inEnds hJ₁] at key
    rw [ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega), ind_eq_zero (by omega)] at key
    omega
  have inner : ∀ u ∈ C.verts, ∀ w ∈ C.verts,
      G.mult s(u, w) = mult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) (φ.f u) (φ.f w) := by
    intro u hu w hw
    obtain ⟨eU, UJ₁, UJ₂⟩ := fe u hu
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeTwo (J₁ := J₁) (J₂ := J₂) hR (φ.f u) (φ.f w)
    rw [ind_eq_zero (u := φ.f u) (v := φ.f w) (x := X₁) (y := J₁) (by omega),
      ind_eq_zero (u := φ.f u) (v := φ.f w) (x := J₁) (y := Y₁) (by omega),
      ind_eq_zero (u := φ.f u) (v := φ.f w) (x := X₂) (y := J₂) (by omega),
      ind_eq_zero (u := φ.f u) (v := φ.f w) (x := J₂) (y := Y₂) (by omega),
      ← φ.mult_eq u hu w hw, hCm] at key
    have hnj : ¬ (j₁ ∈ s(u, w) ∨ j₂ ∈ s(u, w)) := by
      obtain ⟨_, hu1, hu2⟩ := (hmemC u).mp hu
      obtain ⟨_, hw1, hw2⟩ := (hmemC w).mp hw
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hu1, Ne.symm hw1⟩, Ne.symm hu2, Ne.symm hw2⟩
    rw [if_neg hnj, cnt] at key
    unfold ind at key
    rw [ite_one_iff (fsym u hu w hw a ha b hb), ite_one_iff (fsym u hu w hw c hc d hd)] at key
    omega
  intro u hu v hv
  have cls : ∀ z ∈ G.verts, z = j₁ ∨ z = j₂ ∨ z ∈ C.verts := by
    intro z hz
    by_cases h1 : z = j₁
    · exact Or.inl h1
    by_cases h2 : z = j₂
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ((hmemC z).mpr ⟨hz, h1, h2⟩))
  have F₁ : (if j₁ = j₁ then J₁ else if j₁ = j₂ then J₂ else φ.f j₁) = J₁ := by simp
  have F₂ : (if j₂ = j₁ then J₁ else if j₂ = j₂ then J₂ else φ.f j₂) = J₂ := by simp [Ne.symm hj]
  have Fv : ∀ z ∈ C.verts, (if z = j₁ then J₁ else if z = j₂ then J₂ else φ.f z) = φ.f z := by
    intro z hz; have := (hmemC z).mp hz; simp [this.2.1, this.2.2]
  rcases cls u hu with rfl | rfl | hu' <;> rcases cls v hv with rfl | rfl | hv'
  · rw [F₁, L₁, J11]
  · rw [F₁, F₂, hσ, J12]
  · rw [F₁, Fv v hv', row₁ v hv']
  · rw [F₁, F₂, Sym2.eq_swap, hσ, mult_comm, J12]
  · rw [F₂, L₂, J22]
  · rw [F₂, Fv v hv', row₂ v hv']
  · rw [F₁, Fv u hu', Sym2.eq_swap, mult_comm, row₁ u hu']
  · rw [F₂, Fv u hu', Sym2.eq_swap, mult_comm, row₂ u hu']
  · rw [Fv u hu', Fv v hv', inner u hu' v hv']

/-- **The joints, `σ = 1`.** -/
theorem iso_one {G C : UMultigraph V} {es : Edges} (φ : Iso C es) {j₁ j₂ x y : V} {J₁ J₂ : ℕ}
    (hJ : J₁ ≠ J₂) (hJ₁ : ¬ InEnds es J₁) (hJ₂ : ¬ InEnds es J₂)
    (hj : j₁ ≠ j₂) (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts)
    (hCv : C.verts = (G.verts.erase j₁).erase j₂)
    (hσ : G.mult s(j₁, j₂) = 1) (hn₁ : Core.nbrs G j₁ = {j₂, x}) (hn₂ : Core.nbrs G j₂ = {j₁, y})
    (hCm : ∀ e, C.mult e = (if j₁ ∈ e ∨ j₂ ∈ e then 0 else G.mult e) +
      ({s(x, y)} : Multiset (Sym2 V)).count e) :
    mult es (φ.f x) (φ.f y) ≠ 0 ∧
      ∃ ψ : Iso G (placeOne es (φ.f x) (φ.f y) J₁ J₂), ψ.f j₁ = J₁ ∧ ψ.f j₂ = J₂ := by
  have hge : ∀ e, ({s(x, y)} : Multiset (Sym2 V)).count e ≤ C.mult e := fun e => by rw [hCm e]; omega
  have hCxy : 1 ≤ C.mult s(x, y) := by have := hge (s(x, y)); simpa using this
  have hx : x ∈ C.verts := C.supp _ (by omega) x (Sym2.mem_mk_left x y)
  have hy : y ∈ C.verts := C.supp _ (by omega) y (Sym2.mem_mk_right x y)
  have hmemC := memC hCv
  have fe : ∀ v ∈ C.verts, InEnds es (φ.f v) ∧ φ.f v ≠ J₁ ∧ φ.f v ≠ J₂ := by
    intro v hv
    have := φ.fv v hv
    exact ⟨this, fun h => hJ₁ (h ▸ this), fun h => hJ₂ (h ▸ this)⟩
  have finj : ∀ u ∈ C.verts, ∀ v ∈ C.verts, φ.f u = φ.f v ↔ u = v := fun u hu v hv =>
    ⟨fun h => by rw [← φ.gf u hu, h, φ.gf v hv], fun h => h ▸ rfl⟩
  have fsym : ∀ u ∈ C.verts, ∀ v ∈ C.verts, ∀ x ∈ C.verts, ∀ y ∈ C.verts,
      (s(φ.f u, φ.f v) = s(φ.f x, φ.f y) ↔ s(u, v) = s(x, y)) := by
    intro u hu v hv x hx y hy
    simp only [Sym2.eq_iff, finj u hu x hx, finj v hv y hy, finj u hu y hy, finj v hv x hx]
  have hR : mult es (φ.f x) (φ.f y) ≠ 0 := by rw [← φ.mult_eq x hx y hy]; omega
  refine ⟨hR, iso_extend2 φ (G := G) hj hJ hJ₁ hJ₂ ?_ (fun h => ((hmemC j₁).mp h).2.1 rfl)
    (fun h => ((hmemC j₂).mp h).2.2 rfl) (inEnds_placeOne hR)
    (fun v => if v = j₁ then J₁ else if v = j₂ then J₂ else φ.f v) (by simp) (by simp [Ne.symm hj])
    (fun v hv => by have := (hmemC v).mp hv; simp [this.2.1, this.2.2]) ?_,
    show (if j₁ = j₁ then J₁ else if j₁ = j₂ then J₂ else φ.f j₁) = J₁ by simp,
    show (if j₂ = j₁ then J₁ else if j₂ = j₂ then J₂ else φ.f j₂) = J₂ by simp [Ne.symm hj]⟩
  · intro v
    constructor
    · intro hv
      by_cases h1 : v = j₁
      · exact Or.inl h1
      by_cases h2 : v = j₂
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr ((hmemC v).mpr ⟨hv, h1, h2⟩))
    · rintro (rfl | rfl | hv)
      · exact hj₁
      · exact hj₂
      · exact ((hmemC v).mp hv).1
  set X := φ.f x; set Y := φ.f y
  obtain ⟨eX, XJ₁, XJ₂⟩ := fe x hx
  obtain ⟨eY, YJ₁, YJ₂⟩ := fe y hy
  have xj : x ≠ j₁ ∧ y ≠ j₂ := ⟨((hmemC x).mp hx).2.1, ((hmemC y).mp hy).2.2⟩
  have L₁ : G.mult s(j₁, j₁) = 0 := joint_loop hn₁ hj₁ (by rw [count_pair]; simp [hj, Ne.symm xj.1])
  have L₂ : G.mult s(j₂, j₂) = 0 := joint_loop hn₂ hj₂ (by rw [count_pair]; simp [Ne.symm hj, Ne.symm xj.2])
  have row₁ : ∀ w ∈ C.verts, G.mult s(j₁, w) = mult (placeOne es X Y J₁ J₂) J₁ (φ.f w) := by
    intro w hw
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR J₁ (φ.f w)
    rw [mult_eq_zero_of_not_inEnds hJ₁, ind_eq_zero (u := J₁) (x := X) (y := Y) (by omega),
      ind_left _ _ _ (Ne.symm XJ₁), ind_right _ _ _ hJ, ind_eq_zero (u := J₁) (x := J₂) (y := Y) (by omega),
      if_neg WJ₂] at key
    rw [joint_row hn₁ ((hmemC w).mp hw).1 (Ne.symm ((hmemC w).mp hw).2.1), count_pair,
      if_neg ((hmemC w).mp hw).2.2]
    rw [ite_one_iff (finj w hw x hx)] at key
    omega
  have row₂ : ∀ w ∈ C.verts, G.mult s(j₂, w) = mult (placeOne es X Y J₁ J₂) J₂ (φ.f w) := by
    intro w hw
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR J₂ (φ.f w)
    rw [mult_eq_zero_of_not_inEnds hJ₂, ind_eq_zero (u := J₂) (x := X) (y := Y) (by omega),
      ind_eq_zero (u := J₂) (x := X) (y := J₁) (by omega), ind_left _ _ _ (Ne.symm hJ),
      ind_right _ _ _ (Ne.symm YJ₂), if_neg WJ₁] at key
    rw [joint_row hn₂ ((hmemC w).mp hw).1 (Ne.symm ((hmemC w).mp hw).2.2), count_pair,
      if_neg ((hmemC w).mp hw).2.1]
    rw [ite_one_iff (finj w hw y hy)] at key
    omega
  have J11 : mult (placeOne es X Y J₁ J₂) J₁ J₁ = 0 := by
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR J₁ J₁
    rw [mult_eq_zero_of_not_inEnds hJ₁, ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega)] at key
    omega
  have J22 : mult (placeOne es X Y J₁ J₂) J₂ J₂ = 0 := by
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR J₂ J₂
    rw [mult_eq_zero_of_not_inEnds hJ₂, ind_eq_zero (by omega), ind_eq_zero (by omega), ind_eq_zero (by omega),
      ind_eq_zero (by omega)] at key
    omega
  have J12 : mult (placeOne es X Y J₁ J₂) J₁ J₂ = 1 := by
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR J₁ J₂
    rw [mult_eq_zero_of_not_inEnds hJ₁, ind_eq_zero (u := J₁) (x := X) (y := Y) (by omega),
      ind_eq_zero (u := J₁) (x := X) (y := J₁) (by omega), ind_eq_one (Or.inl ⟨rfl, rfl⟩),
      ind_eq_zero (u := J₁) (x := J₂) (y := Y) (by omega)] at key
    omega
  have inner : ∀ u ∈ C.verts, ∀ w ∈ C.verts, G.mult s(u, w) = mult (placeOne es X Y J₁ J₂) (φ.f u) (φ.f w) := by
    intro u hu w hw
    obtain ⟨eU, UJ₁, UJ₂⟩ := fe u hu
    obtain ⟨eW, WJ₁, WJ₂⟩ := fe w hw
    have key := mult_placeOne (J₁ := J₁) (J₂ := J₂) hR (φ.f u) (φ.f w)
    rw [ind_eq_zero (u := φ.f u) (v := φ.f w) (x := X) (y := J₁) (by omega),
      ind_eq_zero (u := φ.f u) (v := φ.f w) (x := J₁) (y := J₂) (by omega),
      ind_eq_zero (u := φ.f u) (v := φ.f w) (x := J₂) (y := Y) (by omega),
      ← φ.mult_eq u hu w hw, hCm] at key
    have hnj : ¬ (j₁ ∈ s(u, w) ∨ j₂ ∈ s(u, w)) := by
      obtain ⟨_, hu1, hu2⟩ := (hmemC u).mp hu
      obtain ⟨_, hw1, hw2⟩ := (hmemC w).mp hw
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hu1, Ne.symm hw1⟩, Ne.symm hu2, Ne.symm hw2⟩
    rw [if_neg hnj, Multiset.count_singleton] at key
    unfold ind at key
    rw [ite_one_iff (fsym u hu w hw x hx y hy), ite_one_iff eq_comm] at key
    omega
  intro u hu v hv
  have cls : ∀ z ∈ G.verts, z = j₁ ∨ z = j₂ ∨ z ∈ C.verts := by
    intro z hz
    by_cases h1 : z = j₁
    · exact Or.inl h1
    by_cases h2 : z = j₂
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ((hmemC z).mpr ⟨hz, h1, h2⟩))
  have F₁ : (if j₁ = j₁ then J₁ else if j₁ = j₂ then J₂ else φ.f j₁) = J₁ := by simp
  have F₂ : (if j₂ = j₁ then J₁ else if j₂ = j₂ then J₂ else φ.f j₂) = J₂ := by simp [Ne.symm hj]
  have Fv : ∀ z ∈ C.verts, (if z = j₁ then J₁ else if z = j₂ then J₂ else φ.f z) = φ.f z := by
    intro z hz; have := (hmemC z).mp hz; simp [this.2.1, this.2.2]
  rcases cls u hu with rfl | rfl | hu' <;> rcases cls v hv with rfl | rfl | hv'
  · rw [F₁, L₁, J11]
  · rw [F₁, F₂, hσ, J12]
  · rw [F₁, Fv v hv', row₁ v hv']
  · rw [F₁, F₂, Sym2.eq_swap, hσ, mult_comm, J12]
  · rw [F₂, L₂, J22]
  · rw [F₂, Fv v hv', row₂ v hv']
  · rw [F₁, Fv u hu', Sym2.eq_swap, mult_comm, row₁ u hu']
  · rw [F₂, Fv u hu', Sym2.eq_swap, mult_comm, row₂ u hu']
  · rw [Fv u hu', Fv v hv', inner u hu' v hv']

/-! ## Normalizing the placement -/

theorem sum_ind_orient (u v x y J : ℕ) : ind u v x J + ind u v J y = ind u v y J + ind u v J x := by
  rw [ind_swap u v x J, ind_swap u v J y]; omega

theorem ind_congr {u v x y x' y' : ℕ} (h : s(x', y') = s(x, y)) : ind u v x' y' = ind u v x y := by
  unfold ind; rw [h]

theorem removable2_congr {es : Edges} {X₁ Y₁ X₂ Y₂ X₁' Y₁' X₂' Y₂' : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂)
    (h₁ : s(X₁', Y₁') = s(X₁, Y₁)) (h₂ : s(X₂', Y₂') = s(X₂, Y₂)) : Removable2 es X₁' Y₁' X₂' Y₂' := by
  have e₁ : mult es X₁' Y₁' = mult es X₁ Y₁ := by rw [mult_eq_count, h₁, ← mult_eq_count]
  have e₂ : mult es X₂' Y₂' = mult es X₂ Y₂ := by rw [mult_eq_count, h₂, ← mult_eq_count]
  have i : ind X₂' Y₂' X₁' Y₁' = ind X₂ Y₂ X₁ Y₁ := by unfold ind; simp only [h₁, h₂]
  exact ⟨by rw [e₁]; exact h.1, by rw [e₂, i]; exact h.2⟩

theorem removable2_swap {es : Edges} {X₁ Y₁ X₂ Y₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) :
    Removable2 es X₂ Y₂ X₁ Y₁ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by have := h2; omega, ?_⟩
  unfold ind at h2 ⊢
  by_cases e : s(X₁, Y₁) = s(X₂, Y₂)
  · rw [if_pos e]; rw [if_pos e.symm] at h2
    rw [mult_eq_count, e, ← mult_eq_count]; omega
  · rw [if_neg e]; omega

theorem sameMult_placeTwo_orient {es : Edges} {X₁ Y₁ X₂ Y₂ X₁' Y₁' X₂' Y₂' J₁ J₂ : ℕ}
    (h : Removable2 es X₁ Y₁ X₂ Y₂) (h₁ : s(X₁', Y₁') = s(X₁, Y₁)) (h₂ : s(X₂', Y₂') = s(X₂, Y₂)) :
    SameMult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) (placeTwo es X₁' Y₁' J₁ X₂' Y₂' J₂) := by
  intro u v
  have a := mult_placeTwo (J₁ := J₁) (J₂ := J₂) h u v
  have b := mult_placeTwo (J₁ := J₁) (J₂ := J₂) (removable2_congr h h₁ h₂) u v
  rw [ind_congr (u := u) (v := v) h₁, ind_congr (u := u) (v := v) h₂] at b
  have o₁ : ind u v X₁' J₁ + ind u v J₁ Y₁' = ind u v X₁ J₁ + ind u v J₁ Y₁ := by
    rw [Sym2.eq_iff] at h₁
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact sum_ind_orient u v _ _ J₁
  have o₂ : ind u v X₂' J₂ + ind u v J₂ Y₂' = ind u v X₂ J₂ + ind u v J₂ Y₂ := by
    rw [Sym2.eq_iff] at h₂
    rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact sum_ind_orient u v _ _ J₂
  omega

theorem sameMult_placeTwo_swap {es : Edges} {X₁ Y₁ X₂ Y₂ J₁ J₂ : ℕ} (h : Removable2 es X₁ Y₁ X₂ Y₂) :
    SameMult (placeTwo es X₁ Y₁ J₁ X₂ Y₂ J₂) (placeTwo es X₂ Y₂ J₂ X₁ Y₁ J₁) := by
  intro u v
  have a := mult_placeTwo (J₁ := J₁) (J₂ := J₂) h u v
  have b := mult_placeTwo (J₁ := J₂) (J₂ := J₁) (removable2_swap h) u v
  omega

theorem sameMult_placeOne_rev {es : Edges} {X Y J₁ J₂ : ℕ} (h : mult es X Y ≠ 0) :
    SameMult (placeOne es X Y J₁ J₂) (placeOne es Y X J₂ J₁) := by
  intro u v
  have a := mult_placeOne (J₁ := J₁) (J₂ := J₂) h u v
  have b := mult_placeOne (J₁ := J₂) (J₂ := J₁) (by rw [mult_comm]; exact h) u v
  rw [ind_swap u v Y X, ind_swap u v J₂ J₁] at b
  rw [ind_swap u v Y J₂, ind_swap u v J₁ X] at b
  omega

/-! ## The generation theorem -/

theorem genC_lt_jname {p : CParam} (hp : p.Valid) {z : ℕ} (h : InEnds (genC p) z) : z < p.jname := by
  unfold CParam.jname
  rcases genC_ends hp h with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> omega

theorem mult_le_two_of_isTVineU {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) :
    ∀ u ∈ G.verts, ∀ v ∈ G.verts, G.mult s(u, v) ≤ 2 := by
  intro u hu v hv
  by_cases huv : u = v
  · subst huv
    obtain ⟨⟨_, _, _, d₁, d₂, d, _⟩, _⟩ := h
    have hdeg : Core.deg G u ≤ 4 := by
      by_cases h1 : u = j₁
      · subst h1; omega
      by_cases h2 : u = j₂
      · subst h2; omega
      exact (d u hu h1 h2).le
    have : G.mult s(u, u) ≤ ∑ w ∈ G.verts, G.mult s(u, w) :=
      Finset.single_le_sum (f := fun w => G.mult s(u, w)) (fun _ _ => Nat.zero_le _) hu
    unfold Core.deg at hdeg; omega
  · exact h.2.1 u hu v hv huv

theorem multLe2_of_iso {G : UMultigraph V} {es : Edges} (φ : Iso G es)
    (h : ∀ u ∈ G.verts, ∀ v ∈ G.verts, G.mult s(u, v) ≤ 2) : multLe2 es = true := by
  unfold multLe2
  rw [List.all_eq_true]
  intro e he
  have hm := mult_ne_zero_of_mem he
  have e1 := (inEnds_of_mult_ne_zero hm).1
  have e2 := (inEnds_of_mult_ne_zero hm).2
  have := h _ (φ.gv _ e1) _ (φ.gv _ e2)
  rw [φ.mult_g e1 e2] at this
  simpa using this

theorem atMostTwoTriples_of_closure {G C : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂)
    (hcl : IsClosureU G j₁ j₂ C) : AtMostTwoTriples C := by
  obtain ⟨_, _, hloop, added, hadd, hCm⟩ := hcl
  have h2 := mult_le_two_of_isTVineU h
  have key : ∀ e, C.mult e = 3 → e ∈ added := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      by_cases huv : u = v
      · subst huv; rw [hloop u] at he; omega
      have hG : (if j₁ ∈ s(u, v) ∨ j₂ ∈ s(u, v) then 0 else G.mult s(u, v)) ≤ 2 := by
        split_ifs
        · omega
        · by_cases hu : u ∈ G.verts
          · by_cases hv : v ∈ G.verts
            · exact h2 u hu v hv
            · rw [mult_eq_zero_of_right G hv]; omega
          · rw [mult_eq_zero_of_left G hu]; omega
      rw [hCm] at he
      exact Multiset.count_ne_zero.mp (by omega)
  intro e₁ e₂ e₃ m1 m2 m3
  have k1 := key e₁ m1; have k2 := key e₂ m2; have k3 := key e₃ m3
  rcases hadd with ⟨_, a, b, c, d, _, _, rfl⟩ | ⟨_, x, y, _, _, rfl⟩
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at k1 k2 k3
    rcases k1 with rfl | rfl <;> rcases k2 with rfl | rfl <;> rcases k3 with rfl | rfl <;> simp
  · simp only [Multiset.mem_singleton] at k1 k2 k3
    subst k1 k2 k3; simp

theorem lex_total (a b c d : ℕ) : (a < c ∨ (a = c ∧ b ≤ d)) ∨ (c < a ∨ (c = a ∧ d ≤ b)) := by omega

/-- **N2 Lemma 1.7 (generation; M4 Lemma 1.7′, direction ⇒).** -/
theorem generation : GenerationStatement.{u} := by
  intro V _ G j₁ j₂ hT
  have hT' := hT
  obtain ⟨⟨hj₁, hj₂, hj, -, -, -, -⟩, -, C, hcl, C', hpath, hTri⟩ := hT
  have h2C := atMostTwoTriples_of_closure hT' hcl
  have hle := mult_le_two_of_isTVineU hT'
  obtain ⟨-, hCv, hloop, added, hadd, hCm⟩ := hcl
  obtain ⟨p, hp, ⟨φ⟩⟩ := closure_generation hpath hTri h2C
  have hJ : ¬ InEnds (genC p) p.jname := fun h => absurd (genC_lt_jname hp h) (lt_irrefl _)
  have hJ1 : ¬ InEnds (genC p) (p.jname + 1) := fun h => absurd (genC_lt_jname hp h) (by omega)
  have hJne : p.jname ≠ p.jname + 1 := by omega
  have hJne' : p.jname + 1 ≠ p.jname := by omega
  rcases hadd with ⟨hσ0, a, b, c, d, hn₁, hn₂, rfl⟩ | ⟨hσ1, x, y, hn₁, hn₂, rfl⟩
  · -- σ = 0: two subdivided bonds
    obtain ⟨hR, _⟩ := iso_two φ (J₁ := p.jname) (J₂ := p.jname + 1) hJne hJ hJ1 hj hj₁ hj₂ hCv hloop hσ0 hn₁ hn₂ hCm
    have hne : ∀ {X Y : ℕ}, 1 ≤ mult (genC p) X Y → X ≠ Y → min X Y < max X Y := by intro X Y _ h; omega
    have nab : φ.f a ≠ φ.f b := by
      intro h
      have := hR.1
      rw [h] at this
      have hb := (inEnds_of_mult_ne_zero (show mult (genC p) (φ.f b) (φ.f b) ≠ 0 by omega)).1
      rw [← φ.fg _ hb, ← φ.mult_eq _ (φ.gv _ hb) _ (φ.gv _ hb), hloop] at this; omega
    have ncd : φ.f c ≠ φ.f d := by
      intro h
      have := hR.2
      rw [h] at this
      have hd := (inEnds_of_mult_ne_zero (show mult (genC p) (φ.f d) (φ.f d) ≠ 0 by omega)).1
      rw [← φ.fg _ hd, ← φ.mult_eq _ (φ.gv _ hd) _ (φ.gv _ hd), hloop] at this; omega
    set X₁ := φ.f a; set Y₁ := φ.f b; set X₂ := φ.f c; set Y₂ := φ.f d
    have o₁ : s(min X₁ Y₁, max X₁ Y₁) = s(X₁, Y₁) := by
      rcases le_total X₁ Y₁ with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]
    have o₂ : s(min X₂ Y₂, max X₂ Y₂) = s(X₂, Y₂) := by
      rcases le_total X₂ Y₂ with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]
    have lt₁ : min X₁ Y₁ < max X₁ Y₁ := by omega
    have lt₂ : min X₂ Y₂ < max X₂ Y₂ := by omega
    rcases lex_total (min X₁ Y₁) (max X₁ Y₁) (min X₂ Y₂) (max X₂ Y₂) with hlex | hlex
    · obtain ⟨_, ψ, hf₁, hf₂⟩ := iso_two φ (J₁ := p.jname) (J₂ := p.jname + 1) hJne hJ hJ1 hj hj₁ hj₂ hCv
        hloop hσ0 hn₁ hn₂ hCm
      have hR' := removable2_congr hR o₁ o₂
      let ψ' := ψ.ofSame (sameMult_placeTwo_orient hR o₁ o₂)
      exact ⟨p, .two (min X₁ Y₁) (max X₁ Y₁) (min X₂ Y₂) (max X₂ Y₂), hp,
        ⟨⟨lt₁, lt₂, hlex, by have := hR'.1; omega, hR'.second⟩, multLe2_of_iso ψ' hle⟩, ψ', Or.inl ⟨hf₁, hf₂⟩⟩
    · obtain ⟨_, ψ, hf₁, hf₂⟩ := iso_two φ (J₁ := p.jname + 1) (J₂ := p.jname) hJne' hJ1 hJ hj hj₁ hj₂ hCv
        hloop hσ0 hn₁ hn₂ hCm
      have hR' := removable2_congr (removable2_swap hR) o₂ o₁
      let ψ' := (ψ.ofSame (sameMult_placeTwo_swap hR)).ofSame
        (sameMult_placeTwo_orient (removable2_swap hR) o₂ o₁)
      exact ⟨p, .two (min X₂ Y₂) (max X₂ Y₂) (min X₁ Y₁) (max X₁ Y₁), hp,
        ⟨⟨lt₂, lt₁, hlex, by have := hR'.1; omega, hR'.second⟩, multLe2_of_iso ψ' hle⟩, ψ', Or.inr ⟨hf₁, hf₂⟩⟩
  · -- σ = 1: one bond subdivided twice
    obtain ⟨hR, _⟩ := iso_one φ (J₁ := p.jname) (J₂ := p.jname + 1) hJne hJ hJ1 hj hj₁ hj₂ hCv hσ1 hn₁ hn₂ hCm
    have nxy : φ.f x ≠ φ.f y := by
      intro h
      have := hR
      rw [h] at this
      have hy := (inEnds_of_mult_ne_zero this).1
      rw [← φ.fg _ hy, ← φ.mult_eq _ (φ.gv _ hy) _ (φ.gv _ hy), hloop] at this; exact this rfl
    rcases lt_or_gt_of_ne nxy with hlt | hlt
    · obtain ⟨_, ψ, hf₁, hf₂⟩ := iso_one φ (J₁ := p.jname) (J₂ := p.jname + 1) hJne hJ hJ1 hj hj₁ hj₂ hCv
        hσ1 hn₁ hn₂ hCm
      exact ⟨p, .one (φ.f x) (φ.f y), hp, ⟨⟨hlt, hR⟩, multLe2_of_iso ψ hle⟩, ψ, Or.inl ⟨hf₁, hf₂⟩⟩
    · obtain ⟨_, ψ, hf₁, hf₂⟩ := iso_one φ (J₁ := p.jname + 1) (J₂ := p.jname) hJne' hJ1 hJ hj hj₁ hj₂ hCv
        hσ1 hn₁ hn₂ hCm
      let ψ' := ψ.ofSame (sameMult_placeOne_rev hR)
      exact ⟨p, .one (φ.f y) (φ.f x), hp, ⟨⟨hlt, by rw [mult_comm]; exact hR⟩, multLe2_of_iso ψ' hle⟩, ψ',
        Or.inr ⟨hf₁, hf₂⟩⟩

end WaveTurbulence.TVine.Checker
