/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Basic
public import WaveTurbulence.Foundations.TVine.Defs

/-!
# The compact T-vine checker: soundness of the graph primitives

* bitmask lemmas (`mem_bit`, `mem_or`, `mem_sdiff`, …);
* multiplicities of bond lists (`mult`, `mult_comm`, `mult_append`, …);
* soundness of the fixpoint search (`comp`, `connB`) and of closedness (`closedB`);
* `Iso G es`: an explicit isomorphism between a `UMultigraph V` and a bond list on `ℕ`, and the transport of
  paths along it.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

/-! ## Bitmasks -/

/-- `Nat.beq` as `decide` (so that `simp` handles the `Bool` programs). -/
@[simp] theorem nat_beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp [Nat.beq_refl]
  · simp only [h, decide_false]
    cases hh : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem bit_eq (v : ℕ) : bit v = 2 ^ v := Nat.one_shiftLeft v

@[simp] theorem mem_bit (v a : ℕ) : mem v (bit a) = decide (a = v) := by
  simp [mem, bit_eq, Nat.testBit_two_pow]

@[simp] theorem mem_or (v R S : ℕ) : mem v (R ||| S) = (mem v R || mem v S) := by
  simp [mem, Nat.testBit_or]

@[simp] theorem mem_and (v R S : ℕ) : mem v (R &&& S) = (mem v R && mem v S) := by
  simp [mem, Nat.testBit_and]

@[simp] theorem mem_sdiff (v S T : ℕ) : mem v (sdiff S T) = (mem v S && !mem v T) := by
  simp only [sdiff, mem, Nat.testBit_xor, Nat.testBit_and]
  cases S.testBit v <;> cases T.testBit v <;> rfl

@[simp] theorem mem_full (v n : ℕ) : mem v (full n) = decide (v < n) := by
  simp [mem, full, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

@[simp] theorem mem_zero (v : ℕ) : mem v 0 = false := by simp [mem]

theorem lowBit_mem {S s : ℕ} (h : lowBit S = some s) : mem s S = true := by
  unfold lowBit at h
  have := List.find?_some h
  simpa using this

theorem lowBit_none {S : ℕ} (h : lowBit S = none) {v : ℕ} (hv : v < 32) : mem v S = false := by
  unfold lowBit at h
  have := List.find?_eq_none.mp h v (List.mem_range.mpr hv)
  simpa using this

theorem mem_elems {S v : ℕ} : v ∈ elems S ↔ v < 32 ∧ mem v S = true := by
  simp [elems, List.mem_filter, List.mem_range]

/-! ## Bond lists: pairs, multiplicities, adjacency -/

theorem isPair_iff (a b : ℕ) (e : ℕ × ℕ) :
    isPair a b e = true ↔ (e.1 = a ∧ e.2 = b) ∨ (e.1 = b ∧ e.2 = a) := by
  simp [isPair, Nat.beq_eq]

theorem isPair_comm (a b : ℕ) (e : ℕ × ℕ) : isPair a b e = isPair b a e := by
  simp only [isPair, Bool.or_comm]

theorem isPair_iff_sym2 (a b : ℕ) (e : ℕ × ℕ) : isPair a b e = true ↔ s(e.1, e.2) = s(a, b) := by
  rw [isPair_iff, Sym2.eq_iff]

theorem mult_comm (es : Edges) (a b : ℕ) : mult es a b = mult es b a := by
  simp only [mult]; congr 1; exact List.filter_congr fun e _ => isPair_comm a b e

@[simp] theorem mult_nil (a b : ℕ) : mult [] a b = 0 := rfl

theorem mult_cons (e : ℕ × ℕ) (es : Edges) (a b : ℕ) :
    mult (e :: es) a b = (if isPair a b e then 1 else 0) + mult es a b := by
  simp only [mult, List.filter_cons]
  by_cases h : isPair a b e = true
  · simp [h, Nat.add_comm]
  · simp [h]

@[simp] theorem mult_append (es es' : Edges) (a b : ℕ) : mult (es ++ es') a b = mult es a b + mult es' a b := by
  simp [mult, List.filter_append]

/-- The multiplicity is the count of the unordered pair. -/
theorem mult_eq_count (es : Edges) (a b : ℕ) :
    mult es a b = (es.map fun e => s(e.1, e.2)).count s(a, b) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [mult_cons, List.map_cons, List.count_cons, ih, Nat.add_comm]
    by_cases h : isPair a b e = true
    · simp [h, (isPair_iff_sym2 a b e).mp h]
    · have h' : ¬ s(e.1, e.2) = s(a, b) := fun hh => h ((isPair_iff_sym2 a b e).mpr hh)
      simp [h, h']

/-- `x` is an end of some bond. -/
def InEnds (es : Edges) (x : ℕ) : Prop := ∃ e ∈ es, e.1 = x ∨ e.2 = x

theorem inEnds_of_mult_ne_zero {es : Edges} {a b : ℕ} (h : mult es a b ≠ 0) : InEnds es a ∧ InEnds es b := by
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
  rw [List.mem_filter] at he
  rcases (isPair_iff a b e).mp he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨e, he.1, Or.inl h1⟩, ⟨e, he.1, Or.inr h2⟩⟩
  · exact ⟨⟨e, he.1, Or.inr h2⟩, ⟨e, he.1, Or.inl h1⟩⟩

theorem mult_ne_zero_of_mem {es : Edges} {e : ℕ × ℕ} (he : e ∈ es) : mult es e.1 e.2 ≠ 0 := by
  have : e ∈ es.filter (isPair e.1 e.2) := List.mem_filter.mpr ⟨he, by simp [isPair, Nat.beq_refl]⟩
  exact Nat.pos_iff_ne_zero.mp (List.length_pos_of_mem this)

theorem inEnds_iff {es : Edges} {x : ℕ} : InEnds es x ↔ ∃ y, mult es x y ≠ 0 := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact ⟨e.2, h ▸ mult_ne_zero_of_mem he⟩
    · refine ⟨e.1, ?_⟩; rw [mult_comm]; exact h ▸ mult_ne_zero_of_mem he
  · rintro ⟨y, hy⟩; exact (inEnds_of_mult_ne_zero hy).1

/-- Adjacency in a bond list. -/
def Adj (es : Edges) (u v : ℕ) : Prop := mult es u v ≠ 0

theorem adj_symm {es : Edges} {u v : ℕ} (h : Adj es u v) : Adj es v u := by
  unfold Adj at *; rwa [mult_comm]

theorem adj_of_mem {es : Edges} {e : ℕ × ℕ} (he : e ∈ es) : Adj es e.1 e.2 := mult_ne_zero_of_mem he

theorem rtg_symm {es : Edges} {u v : ℕ} (h : Relation.ReflTransGen (Adj es) u v) :
    Relation.ReflTransGen (Adj es) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (adj_symm hbc) ih

theorem adj_mono {es es' : Edges} (h : ∀ e ∈ es, e ∈ es') {u v : ℕ} (huv : Adj es u v) : Adj es' u v := by
  unfold Adj mult at *
  intro h0
  apply huv
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0 ⊢
  exact fun e he => h0 e (h e he)

/-! ## The fixpoint search -/

/-- Invariant of the search: every member of `R` is reachable from `s`. -/
def Reached (es : Edges) (s R : ℕ) : Prop := ∀ v, mem v R = true → Relation.ReflTransGen (Adj es) s v

theorem grow_reached (es₀ : Edges) (s : ℕ) :
    ∀ (es : Edges), (∀ e ∈ es, e ∈ es₀) → ∀ R, Reached es₀ s R → Reached es₀ s (grow es R) := by
  intro es
  induction es with
  | nil => intro _ R h; exact h
  | cons e es ih =>
    intro hsub R hR
    simp only [grow]
    apply ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    have hadj : Adj es₀ e.1 e.2 := adj_of_mem (hsub e (List.mem_cons_self))
    split
    · rename_i hc
      intro v hv
      simp only [mem_or, Bool.or_eq_true, mem_bit, decide_eq_true_eq] at hv
      rcases hv with (hv | rfl) | rfl
      · exact hR v hv
      · rcases Bool.or_eq_true _ _ ▸ hc with h1 | h2
        · exact hR _ h1
        · exact (hR _ h2).tail (adj_symm hadj)
      · rcases Bool.or_eq_true _ _ ▸ hc with h1 | h2
        · exact (hR _ h1).tail hadj
        · exact hR _ h2
    · exact hR

theorem reach_reached (es : Edges) (s : ℕ) :
    ∀ k R, Reached es s R → Reached es s (reach k es R) := by
  intro k
  induction k with
  | zero => intro R h; exact h
  | succ k ih =>
    intro R hR
    simp only [reach]
    split
    · exact hR
    · exact ih _ (grow_reached es s es (fun _ h => h) R hR)

theorem comp_reached (es : Edges) (s : ℕ) : Reached es s (comp es s) := by
  apply reach_reached
  intro v hv
  simp only [mem_bit, decide_eq_true_eq] at hv
  subst hv; exact Relation.ReflTransGen.refl

/-- Soundness of `connB`: all atoms of `V` (below `16`) are joined by paths of `es`. -/
theorem connB_sound {V : ℕ} {es : Edges} (h : connB V es = true) {u v : ℕ} (hu : mem u V = true)
    (hv : mem v V = true) : Relation.ReflTransGen (Adj es) u v := by
  unfold connB at h
  split at h
  · have hV : V = 0 := by simpa [Nat.beq_eq] using h
    subst hV; simp at hu
  · rename_i s hs
    have hV : comp es s = V := by simpa [Nat.beq_eq] using h
    have hr := comp_reached es s
    rw [hV] at hr
    exact (rtg_symm (hr u hu)).trans (hr v hv)

/-- Closedness: a closed set containing `s` contains everything reachable from `s`. -/
theorem closedB_sound {es : Edges} {X : ℕ} (h : closedB es X = true) {s v : ℕ} (hs : mem s X = true)
    (hp : Relation.ReflTransGen (Adj es) s v) : mem v X = true := by
  induction hp with
  | refl => exact hs
  | @tail b c _ hbc ih =>
    obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hbc)
    rw [List.mem_filter] at he
    have hcl : (mem e.1 X == mem e.2 X) = true := List.all_eq_true.mp h e he.1
    have hcl' : mem e.1 X = mem e.2 X := beq_iff_eq.mp hcl
    rcases (isPair_iff b c e).mp he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2, ← hcl', h1]; exact ih
    · rw [← h1, hcl', h2]; exact ih

/-! ## Explicit isomorphisms between a `UMultigraph` and a bond list -/

variable {V : Type*}

/-- An explicit isomorphism between `G` and the multigraph of the bond list `es` (vertex set: the ends of the
bonds). -/
structure Iso (G : UMultigraph V) (es : Edges) where
  /-- The forward map. -/
  f : V → ℕ
  /-- The inverse map. -/
  g : ℕ → V
  gf : ∀ v ∈ G.verts, g (f v) = v
  fg : ∀ x, InEnds es x → f (g x) = x
  fv : ∀ v ∈ G.verts, InEnds es (f v)
  gv : ∀ x, InEnds es x → g x ∈ G.verts
  mult_eq : ∀ u ∈ G.verts, ∀ v ∈ G.verts, G.mult s(u, v) = mult es (f u) (f v)

namespace Iso

variable {G : UMultigraph V} {es : Edges} (φ : Iso G es)

theorem mult_g {x y : ℕ} (hx : InEnds es x) (hy : InEnds es y) : G.mult s(φ.g x, φ.g y) = mult es x y := by
  rw [φ.mult_eq _ (φ.gv x hx) _ (φ.gv y hy), φ.fg x hx, φ.fg y hy]

theorem f_injOn : Set.InjOn φ.f G.verts := fun u hu v hv h => by rw [← φ.gf u hu, h, φ.gf v hv]

/-- Paths of `es` pull back to `G`. -/
theorem rtg_g {x y : ℕ} (_hx : InEnds es x) (h : Relation.ReflTransGen (Adj es) x y) :
    Relation.ReflTransGen (fun a b => a ∈ G.verts ∧ b ∈ G.verts ∧ G.mult s(a, b) ≠ 0) (φ.g x) (φ.g y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have hb := (inEnds_of_mult_ne_zero hbc).1
    have hc := (inEnds_of_mult_ne_zero hbc).2
    exact ih.tail ⟨φ.gv b hb, φ.gv c hc, by rw [φ.mult_g hb hc]; exact hbc⟩

end Iso

end WaveTurbulence.TVine.Checker
