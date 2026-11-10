/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Graph

/-!
# The compact T-vine checker: soundness of the (Y2) primitives

For a `UMultigraph` `H` isomorphic to a bond list `es` (`Iso H es`):
* `y2At es a b = some (c, d)` gives a `Y2Step` of `H` to a multigraph isomorphic to `y2Apply es a b c d`
  (`y2_sound`);
* a greedy run (`y2Greedy`) gives `Relation.ReflTransGen Y2Step` (`y2Greedy_sound`);
* `isDoubledTriangle es = true` gives `IsDoubledTriangle H` (`isDoubledTriangle_sound`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

/-! ## Neighbour lists -/

theorem nbrs_cons (e : ℕ × ℕ) (es : Edges) (a : ℕ) :
    nbrs (e :: es) a = (if e.1 = a then [e.2] else if e.2 = a then [e.1] else []) ++ nbrs es a := by
  unfold nbrs
  rw [List.filterMap_cons]
  by_cases h1 : e.1 = a
  · simp [h1]
  · by_cases h2 : e.2 = a <;> simp [h1, h2]

theorem count_nbrs (es : Edges) (a x : ℕ) : (nbrs es a).count x = mult es a x := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [nbrs_cons, List.count_append, ih, mult_cons]
    suffices hh : List.count x (if e.1 = a then [e.2] else if e.2 = a then [e.1] else []) =
        (if isPair a x e = true then 1 else 0) by rw [hh]
    obtain ⟨p, q⟩ := e
    by_cases h1 : p = a
    · subst h1
      by_cases h4 : q = x
      · subst h4; simp [isPair]
      · simp [isPair, h4, Ne.symm h4, List.count_singleton]
        intro h; subst h; exact h4
    · by_cases h2 : q = a
      · subst h2
        by_cases h3 : p = x
        · subst h3; simp [isPair, h1]
        · simp [isPair, h1, h3, Ne.symm h3, List.count_singleton]
      · simp [isPair, h1, h2]

/-- If the neighbours of `a` other than `b` are exactly `[c]`, then `a`'s multiplicities are `1` to `c` and
`0` to everything else but `b`. -/
theorem mult_of_nbrs_filter {es : Edges} {a b c : ℕ} (h : (nbrs es a).filter (fun x => !x.beq b) = [c])
    {x : ℕ} (hx : x ≠ b) : mult es a x = if x = c then 1 else 0 := by
  have hc : (((nbrs es a).filter (fun x => !x.beq b))).count x = mult es a x := by
    rw [List.count_filter]
    · exact count_nbrs es a x
    · simpa using hx
  rw [← hc, h, List.count_singleton]
  by_cases hxc : x = c
  · simp [hxc]
  · simp [hxc, Ne.symm hxc]

/-! ## Counting with disjoint predicates -/

theorem countP_or_disjoint {α : Type*} (p q : α → Bool) (hd : ∀ a, ¬ (p a = true ∧ q a = true)) :
    ∀ l : List α, l.countP (fun a => p a || q a) = l.countP p + l.countP q
  | [] => rfl
  | a :: l => by
    simp only [List.countP_cons, countP_or_disjoint p q hd l]
    have := hd a
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-! ## The (Y2) move on a `UMultigraph` -/

variable {V : Type*} [DecidableEq V]

/-- The result of the (Y2) move at the triple pair `(a, b)` with externals `c, d`. -/
def y2Graph (H : UMultigraph V) (a b c d : V) (hc : c ∈ H.verts) (hd : d ∈ H.verts) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) : UMultigraph V where
  verts := (H.verts.erase a).erase b
  mult e := if a ∈ e ∨ b ∈ e then 0 else H.mult e + if e = s(c, d) then 1 else 0
  supp := by
    intro e he x hx
    split_ifs at he with h1 h2
    · exact absurd rfl he
    · subst h2
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · simp [Finset.mem_erase, hca, hcb, hc]
      · simp [Finset.mem_erase, hda, hdb, hd]
    · have hxa : x ≠ a := fun hh => h1 (Or.inl (hh ▸ hx))
      have hxb : x ≠ b := fun hh => h1 (Or.inr (hh ▸ hx))
      have hne : H.mult e ≠ 0 := by simpa using he
      simp [Finset.mem_erase, hxa, hxb, H.supp e hne x hx]

namespace Iso

variable {H : UMultigraph V} {es : Edges} (φ : Iso H es)
include φ

theorem mult_eq_zero_of_not_mem {u v : V} (hu : u ∉ H.verts) : H.mult s(u, v) = 0 := by
  by_contra h
  exact hu (H.supp _ h u (Sym2.mem_mk_left u v))

theorem mult_eq_zero_of_not_mem' {u v : V} (hv : v ∉ H.verts) : H.mult s(u, v) = 0 := by
  rw [Sym2.eq_swap]; exact φ.mult_eq_zero_of_not_mem hv

theorem g_injOn {x y : ℕ} (hx : InEnds es x) (hy : InEnds es y) (h : φ.g x = φ.g y) : x = y := by
  rw [← φ.fg x hx, ← φ.fg y hy, h]

theorem g_ne {x y : ℕ} (hx : InEnds es x) (hy : InEnds es y) (h : x ≠ y) : φ.g x ≠ φ.g y :=
  fun hh => h (φ.g_injOn hx hy hh)

/-- The multiplicity of `s(g x, w)` for any `w`. -/
theorem mult_g_left {x : ℕ} (hx : InEnds es x) (w : V) :
    H.mult s(φ.g x, w) = if w ∈ H.verts then mult es x (φ.f w) else 0 := by
  split_ifs with hw
  · rw [φ.mult_eq _ (φ.gv x hx) _ hw, φ.fg x hx]
  · exact φ.mult_eq_zero_of_not_mem' hw

/-- The multiplicity of an arbitrary pair, through `f`. -/
theorem mult_sym2 (e : Sym2 V) :
    H.mult e = Sym2.lift ⟨fun u v => if u ∈ H.verts ∧ v ∈ H.verts then mult es (φ.f u) (φ.f v) else 0,
      fun u v => by
        by_cases h : u ∈ H.verts ∧ v ∈ H.verts
        · simp [h, h.1, h.2, mult_comm]
        · have h' : ¬ (v ∈ H.verts ∧ u ∈ H.verts) := fun hh => h ⟨hh.2, hh.1⟩
          simp only [h, h', if_false]⟩ e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Sym2.lift_mk]
    split_ifs with h
    · exact φ.mult_eq u h.1 v h.2
    · by_cases hu : u ∈ H.verts
      · exact φ.mult_eq_zero_of_not_mem' (fun hv => h ⟨hu, hv⟩)
      · exact φ.mult_eq_zero_of_not_mem hu

end Iso

/-! ## Soundness of one (Y2) move -/

theorem mult_filter_ab (es : Edges) (a b u v : ℕ) (hu : u ≠ a) (hu' : u ≠ b) (hv : v ≠ a)
    (hv' : v ≠ b) : mult (es.filter fun e => !touches a e && !touches b e) u v = mult es u v := by
  simp only [mult, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e _
  by_cases h : isPair u v e = true
  · rcases (isPair_iff u v e).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [h, touches, h1, h2, hu, hu', hv, hv']
  · simp [h]

theorem y2_sound {H : UMultigraph V} {es : Edges} (φ : Iso H es) {a b c d : ℕ}
    (h : y2At es a b = some (c, d)) :
    ∃ H' : UMultigraph V, Y2Step H H' ∧ Nonempty (Iso H' (y2Apply es a b c d)) := by
  unfold y2At at h
  by_cases h3 : (mult es a b == 3) = true
  swap
  · simp only [h3, if_false] at h; exact absurd h (by simp)
  rw [if_pos h3] at h
  have hab3 : mult es a b = 3 := beq_iff_eq.mp h3
  split at h
  · rename_i c' d' hc' hd'
    split_ifs at h with hne
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc0, hd0⟩ := h
    have hc0' := hc0.symm
    have hd0' := hd0.symm
    subst hc0' hd0' 
    simp only [nat_beq_eq_decide, Bool.or_eq_true, decide_eq_true_eq, not_or] at hne
    obtain ⟨⟨⟨⟨⟨hab, hcd⟩, hca⟩, hcb⟩, hda⟩, hdb⟩ := hne
    -- the multiplicities at `a` and `b`
    have hA : ∀ x, x ≠ b → mult es a x = if x = c then 1 else 0 := fun x hx => mult_of_nbrs_filter hc' hx
    have hB : ∀ x, x ≠ a → mult es b x = if x = d then 1 else 0 := fun x hx => mult_of_nbrs_filter hd' hx
    have hac : mult es a c = 1 := by rw [hA c hcb]; simp
    have hbd : mult es b d = 1 := by rw [hB d hda]; simp
    have eA := inEnds_of_mult_ne_zero (show mult es a b ≠ 0 by omega)
    have eC := (inEnds_of_mult_ne_zero (show mult es a c ≠ 0 by omega)).2
    have eD := (inEnds_of_mult_ne_zero (show mult es b d ≠ 0 by omega)).2
    -- the graph
    have ne_ab : (φ.g a) ≠ (φ.g b) := φ.g_ne eA.1 eA.2 hab
    have ne_cd : (φ.g c) ≠ (φ.g d) := φ.g_ne eC eD hcd
    have ne_ca : (φ.g c) ≠ (φ.g a) := φ.g_ne eC eA.1 hca
    have ne_cb : (φ.g c) ≠ (φ.g b) := φ.g_ne eC eA.2 hcb
    have ne_da : (φ.g d) ≠ (φ.g a) := φ.g_ne eD eA.1 hda
    have ne_db : (φ.g d) ≠ (φ.g b) := φ.g_ne eD eA.2 hdb
    refine ⟨y2Graph H (φ.g a) (φ.g b) (φ.g c) (φ.g d) (φ.gv c eC) (φ.gv d eD) ne_ca ne_cb ne_da ne_db, ?_, ?_⟩
    · refine ⟨(φ.g a), (φ.g b), (φ.g c), (φ.g d), ne_ab, ne_cd, ne_ca, ne_cb, ne_da, ne_db, ?_, ?_, ?_, ?_, ?_, rfl, fun e => rfl⟩
      · rw [φ.mult_g eA.1 eA.2]; exact hab3
      · rw [φ.mult_g eA.1 eC]; exact hac
      · rw [φ.mult_g eA.2 eD]; exact hbd
      · intro x hxb hxc
        rw [φ.mult_g_left eA.1]
        split_ifs with hx
        · have hfb : φ.f x ≠ b := fun hh => hxb (by rw [← φ.gf x hx, hh])
          have hfc : φ.f x ≠ c := fun hh => hxc (by rw [← φ.gf x hx, hh])
          rw [hA _ hfb, if_neg hfc]
        · rfl
      · intro x hxa hxd
        rw [φ.mult_g_left eA.2]
        split_ifs with hx
        · have hfa : φ.f x ≠ a := fun hh => hxa (by rw [← φ.gf x hx, hh])
          have hfd : φ.f x ≠ d := fun hh => hxd (by rw [← φ.gf x hx, hh])
          rw [hB _ hfa, if_neg hfd]
        · rfl
    · -- the isomorphism
      have hends : ∀ x, InEnds (y2Apply es a b c d) x → InEnds es x ∧ x ≠ a ∧ x ≠ b := by
        rintro x ⟨e, he, hx⟩
        simp only [y2Apply, List.mem_append, List.mem_filter, List.mem_singleton] at he
        rcases he with ⟨he, hta⟩ | rfl
        · simp only [touches, nat_beq_eq_decide, Bool.and_eq_true, Bool.not_eq_true',
            Bool.or_eq_false_iff, decide_eq_false_iff_not] at hta
          refine ⟨⟨e, he, hx⟩, ?_, ?_⟩ <;> rcases hx with rfl | rfl <;> tauto
        · rcases hx with rfl | rfl
          · exact ⟨eC, hca, hcb⟩
          · exact ⟨eD, hda, hdb⟩
      have hv' : ∀ v, v ∈ (y2Graph H (φ.g a) (φ.g b) (φ.g c) (φ.g d) (φ.gv c eC) (φ.gv d eD) ne_ca ne_cb ne_da ne_db).verts →
          v ∈ H.verts ∧ φ.f v ≠ a ∧ φ.f v ≠ b := by
        intro v hv
        simp only [y2Graph, Finset.mem_erase] at hv
        obtain ⟨hvb, hva, hv⟩ := hv
        exact ⟨hv, fun hh => hva (by rw [← φ.gf v hv, hh]), fun hh => hvb (by rw [← φ.gf v hv, hh])⟩
      refine ⟨⟨φ.f, φ.g, fun v hv => φ.gf v (hv' v hv).1, fun x hx => φ.fg x (hends x hx).1, ?_, ?_, ?_⟩⟩
      · -- `f v` is still an end
        intro v hv
        obtain ⟨hvH, hfa, hfb⟩ := hv' v hv
        obtain ⟨y, hy⟩ := inEnds_iff.mp (φ.fv v hvH)
        by_cases hya : y = a
        · subst hya
          have : φ.f v = c := by
            have := hA (φ.f v) hfb; rw [mult_comm] at hy
            by_contra hc; rw [if_neg hc] at this; exact hy this
          rw [this]; exact ⟨(c, d), by simp [y2Apply], Or.inl rfl⟩
        by_cases hyb : y = b
        · subst hyb
          have : φ.f v = d := by
            have := hB (φ.f v) hfa; rw [mult_comm] at hy
            by_contra hd; rw [if_neg hd] at this; exact hy this
          rw [this]; exact ⟨(c, d), by simp [y2Apply], Or.inr rfl⟩
        refine inEnds_iff.mpr ⟨y, ?_⟩
        simp only [y2Apply, mult_append]
        rw [mult_filter_ab _ _ _ _ _ hfa hfb hya hyb]
        omega
      · intro x hx
        obtain ⟨hx, hxa, hxb⟩ := hends x hx
        simp only [y2Graph, Finset.mem_erase]
        exact ⟨φ.g_ne hx eA.2 hxb, φ.g_ne hx eA.1 hxa, φ.gv x hx⟩
      · intro u hu v hv
        obtain ⟨huH, hua, hub⟩ := hv' u hu
        obtain ⟨hvH, hva, hvb⟩ := hv' v hv
        have hu1 : (φ.g a) ∉ s(u, v) := by
          rw [Sym2.mem_iff]; rintro (h | h)
          · exact hua (by rw [← h]; exact φ.fg a eA.1)
          · exact hva (by rw [← h]; exact φ.fg a eA.1)
        have hu2 : (φ.g b) ∉ s(u, v) := by
          rw [Sym2.mem_iff]; rintro (h | h)
          · exact hub (by rw [← h]; exact φ.fg b eA.2)
          · exact hvb (by rw [← h]; exact φ.fg b eA.2)
        simp only [y2Graph, hu1, hu2, or_self, if_false, y2Apply, mult_append]
        rw [mult_filter_ab _ _ _ _ _ hua hub hva hvb, φ.mult_eq u huH v hvH]
        congr 1
        have key : s(u, v) = s((φ.g c), (φ.g d)) ↔ s(φ.f u, φ.f v) = s(c, d) := by
          constructor
          · intro hh
            have := congrArg (Sym2.map φ.f) hh
            simpa [Sym2.map_mk, φ.fg c eC, φ.fg d eD] using this
          · intro hh
            have := congrArg (Sym2.map φ.g) hh
            simpa [Sym2.map_mk, φ.gf u huH, φ.gf v hvH] using this
        by_cases hk : s(φ.f u, φ.f v) = s(c, d)
        · rw [if_pos (key.mpr hk)]
          simp [mult, List.filter_cons, (isPair_iff_sym2 (φ.f u) (φ.f v) (c, d)).mpr hk.symm]
        · rw [if_neg (fun hh => hk (key.mp hh))]
          have : isPair (φ.f u) (φ.f v) (c, d) = false := by
            cases hh : isPair (φ.f u) (φ.f v) (c, d)
            · rfl
            · exact absurd ((isPair_iff_sym2 _ _ _).mp hh).symm hk
          simp [mult, List.filter_cons, this]
  · exact absurd h (by simp)

/-! ## Greedy reduction -/

theorem findY2_spec {es : Edges} {m : ℕ × ℕ × ℕ × ℕ} (h : findY2 es = some m) :
    y2At es m.1 m.2.1 = some (m.2.2.1, m.2.2.2) := by
  unfold findY2 at h
  obtain ⟨e, _, he⟩ := List.exists_of_findSome?_eq_some h
  rw [Option.map_eq_some_iff] at he
  obtain ⟨cd, hcd, rfl⟩ := he
  exact hcd

theorem y2Greedy_sound : ∀ (k : ℕ) {H : UMultigraph V} {es : Edges} (_φ : Iso H es),
    ∃ H', Relation.ReflTransGen Y2Step H H' ∧ Nonempty (Iso H' (y2Greedy k es).2)
  | 0, H, es, φ => ⟨H, Relation.ReflTransGen.refl, ⟨φ⟩⟩
  | k + 1, H, es, φ => by
    simp only [y2Greedy]
    split
    · exact ⟨H, Relation.ReflTransGen.refl, ⟨φ⟩⟩
    · rename_i m hm
      obtain ⟨H₁, hstep, ⟨φ₁⟩⟩ := y2_sound φ (findY2_spec hm)
      obtain ⟨H', hrt, hφ'⟩ := y2Greedy_sound k φ₁
      exact ⟨H', Relation.ReflTransGen.head hstep hrt, hφ'⟩

/-! ## The doubled triangle -/

theorem isDoubledTriangle_sound {H : UMultigraph V} {es : Edges} (φ : Iso H es)
    (h : isDoubledTriangle es = true) : IsDoubledTriangle H := by
  unfold isDoubledTriangle at h
  split at h
  · rename_i a b rest
    split at h
    · rename_i c rest' hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', nat_beq_eq_decide,
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨⟨⟨⟨hlen, hab⟩, hac⟩, hbc⟩, mab⟩, mbc⟩, mac⟩ := h
      set es := (a, b) :: rest with hes
      -- every bond is a copy of one of the three pairs
      have hall : ∀ e ∈ es, isPair a b e = true ∨ isPair b c e = true ∨ isPair a c e = true := by
        have hd1 : ∀ e, ¬ (isPair a b e = true ∧ (isPair b c e || isPair a c e) = true) := by
          rintro e ⟨h1, h2⟩
          rw [isPair_iff] at h1
          rcases Bool.or_eq_true _ _ ▸ h2 with h2 | h2 <;> rw [isPair_iff] at h2 <;> omega
        have hd2 : ∀ e, ¬ (isPair b c e = true ∧ isPair a c e = true) := by
          rintro e ⟨h1, h2⟩
          rw [isPair_iff] at h1 h2; omega
        have hcnt : es.countP (fun e => isPair a b e || (isPair b c e || isPair a c e)) = es.length := by
          rw [countP_or_disjoint _ _ hd1, countP_or_disjoint _ _ hd2]
          simp only [List.countP_eq_length_filter]
          unfold mult at mab mbc mac
          omega
        intro e he
        have := (List.countP_eq_length.mp hcnt) e he
        simpa [Bool.or_eq_true] using this
      have hmult : ∀ x y, mult es x y = if s(x, y) = s(a, b) ∨ s(x, y) = s(b, c) ∨ s(x, y) = s(a, c)
          then 2 else 0 := by
        intro x y
        split_ifs with hxy
        · rcases hxy with hxy | hxy | hxy <;> rw [mult_eq_count, hxy, ← mult_eq_count] <;> assumption
        · unfold mult
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he hp
          rw [isPair_iff_sym2] at hp
          rcases hall e he with h1 | h1 | h1 <;> rw [isPair_iff_sym2] at h1 <;>
            exact hxy (by rw [← hp, h1]; simp)
      have eA : InEnds es a := ⟨(a, b), List.mem_cons_self, Or.inl rfl⟩
      have eB : InEnds es b := ⟨(a, b), List.mem_cons_self, Or.inr rfl⟩
      have eC : InEnds es c := (inEnds_of_mult_ne_zero (show mult es b c ≠ 0 by omega)).2
      have hends : ∀ x, InEnds es x → x = a ∨ x = b ∨ x = c := by
        rintro x ⟨e, he, hx⟩
        rcases hall e he with h1 | h1 | h1 <;> rw [isPair_iff] at h1 <;> omega
      refine ⟨φ.g a, φ.g b, φ.g c, φ.g_ne eA eB hab, φ.g_ne eA eC hac, φ.g_ne eB eC hbc, ?_, ?_⟩
      · ext v
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hv
          rcases hends _ (φ.fv v hv) with h1 | h1 | h1 <;> rw [← φ.gf v hv, h1] <;> simp
        · rintro (rfl | rfl | rfl)
          · exact φ.gv a eA
          · exact φ.gv b eB
          · exact φ.gv c eC
      · intro e
        rw [φ.mult_sym2 e]
        induction e using Sym2.ind with
        | _ u v =>
          simp only [Sym2.lift_mk]
          split_ifs with huv hx hx
          · rw [hmult, if_pos]
            have key : ∀ x y, s(u, v) = s(φ.g x, φ.g y) → InEnds es x → InEnds es y →
                s(φ.f u, φ.f v) = s(x, y) := by
              intro x y hh hx hy
              have := congrArg (Sym2.map φ.f) hh
              simpa [Sym2.map_mk, φ.fg x hx, φ.fg y hy] using this
            rcases hx with hx | hx | hx
            · exact Or.inl (key a b hx eA eB)
            · exact Or.inr (Or.inl (key b c hx eB eC))
            · exact Or.inr (Or.inr (key a c hx eA eC))
          · rw [hmult, if_neg]
            rintro (hh | hh | hh) <;> apply hx
            · left; have := congrArg (Sym2.map φ.g) hh
              simpa [Sym2.map_mk, φ.gf u huv.1, φ.gf v huv.2] using this
            · right; left; have := congrArg (Sym2.map φ.g) hh
              simpa [Sym2.map_mk, φ.gf u huv.1, φ.gf v huv.2] using this
            · right; right; have := congrArg (Sym2.map φ.g) hh
              simpa [Sym2.map_mk, φ.gf u huv.1, φ.gf v huv.2] using this
          · exfalso; apply huv
            have hg : ∀ x y, s(u, v) = s(φ.g x, φ.g y) → InEnds es x → InEnds es y →
                u ∈ H.verts ∧ v ∈ H.verts := by
              intro x y hh hxe hye
              rw [Sym2.eq_iff] at hh
              rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [h1, h2]; exact ⟨φ.gv x hxe, φ.gv y hye⟩
              · rw [h1, h2]; exact ⟨φ.gv y hye, φ.gv x hxe⟩
            rcases hx with hx | hx | hx
            · exact hg a b hx eA eB
            · exact hg b c hx eB eC
            · exact hg a c hx eA eC
          · rfl
    · simp at h
  · simp at h

end WaveTurbulence.TVine.Checker
