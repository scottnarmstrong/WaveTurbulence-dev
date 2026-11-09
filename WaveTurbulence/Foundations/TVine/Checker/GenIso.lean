/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.GenFacts

/-!
# Isomorphisms for the generation theorem

* `iso_of_y2`: a (Y2) step `G ⟶ G₁` and an isomorphism `G₁ ≅ es₁` give `G ≅ z1 es₁ (f c) (f d) N (N+1)` for
  fresh `N, N + 1` (the deleted atoms `a, b` are sent to `N, N + 1`);
* `iso_tri`: a doubled triangle is isomorphic to `tri`;
* relabelling by an involution of `ℕ` (`Iso.ofInvolution`) and `SameMult` from a permutation of normalized bond
  lists (`sameMult_of_perm`, decidable);
* `AtMostTwoTriples` and its transport (`atMostTwoTriplesE_of_iso`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Evaluating the new multiplicities of a (Z1) move -/

theorem sym2_ne_of_left {a w x y : ℕ} (hx : a ≠ x) (hy : a ≠ y) : s(a, w) ≠ s(x, y) := by
  rw [Ne, Sym2.eq_iff]; omega

theorem z1New_zero {x y a b u v : ℕ} (hua : u ≠ a) (hub : u ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    z1New x y a b u v = 0 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_a_x {x y a b : ℕ} (hxb : x ≠ b) (hab : a ≠ b) : z1New x y a b a x = 1 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_a_b {x y a b : ℕ} (hxb : x ≠ b) (hya : y ≠ a) : z1New x y a b a b = 3 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_a_other {x y a b w : ℕ} (hxa : x ≠ a) (hwx : w ≠ x) (hwb : w ≠ b) (hab : a ≠ b) :
    z1New x y a b a w = 0 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_b_y {x y a b : ℕ} (hya : y ≠ a) (hab : a ≠ b) : z1New x y a b b y = 1 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_b_a {x y a b : ℕ} (hxb : x ≠ b) (hya : y ≠ a) : z1New x y a b b a = 3 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

theorem z1New_b_other {x y a b w : ℕ} (hyb : y ≠ b) (hwy : w ≠ y) (hwa : w ≠ a) (hab : a ≠ b) :
    z1New x y a b b w = 0 := by
  simp only [z1New, Sym2.eq_iff, and_self, and_true, true_and, or_true, true_or, ite_true]
  split_ifs <;> omega

/-! ## The isomorphism along a (Y2) step -/

theorem iso_of_y2_aux {G G₁ : UMultigraph V} {es₁ : Edges} (φ : Iso G₁ es₁)
    {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (h3 : G.mult s(a, b) = 3) (hc1 : G.mult s(a, c) = 1) (hd1 : G.mult s(b, d) = 1)
    (hax : ∀ x, x ≠ b → x ≠ c → G.mult s(a, x) = 0) (hbx : ∀ x, x ≠ a → x ≠ d → G.mult s(b, x) = 0)
    (hv : G₁.verts = (G.verts.erase a).erase b)
    (hm : ∀ e, G₁.mult e = if a ∈ e ∨ b ∈ e then 0 else G.mult e + if e = s(c, d) then 1 else 0)
    (N : ℕ) (hN : ¬ InEnds es₁ N) (hN1 : ¬ InEnds es₁ (N + 1)) :
    Nonempty (Iso G (z1 es₁ (φ.f c) (φ.f d) N (N + 1))) := by
  -- membership facts
  have haV : a ∈ G.verts := G.supp _ (by omega) a (Sym2.mem_mk_left a b)
  have hbV : b ∈ G.verts := G.supp _ (by omega) b (Sym2.mem_mk_right a b)
  have hcV : c ∈ G.verts := G.supp _ (by omega) c (Sym2.mem_mk_right a c)
  have hdV : d ∈ G.verts := G.supp _ (by omega) d (Sym2.mem_mk_right b d)
  have hmem₁ : ∀ v, v ∈ G₁.verts ↔ v ∈ G.verts ∧ v ≠ a ∧ v ≠ b := by
    intro v; rw [hv]; simp only [Finset.mem_erase]; tauto
  have hc₁ : c ∈ G₁.verts := (hmem₁ c).mpr ⟨hcV, hca, hcb⟩
  have hd₁ : d ∈ G₁.verts := (hmem₁ d).mpr ⟨hdV, hda, hdb⟩
  obtain ⟨x, hxdef⟩ : ∃ x, φ.f c = x := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, φ.f d = y := ⟨_, rfl⟩
  rw [hxdef, hydef]
  have hx : InEnds es₁ x := hxdef ▸ φ.fv c hc₁
  have hy : InEnds es₁ y := hydef ▸ φ.fv d hd₁
  have hxy : mult es₁ x y ≠ 0 := by
    rw [← hxdef, ← hydef, ← φ.mult_eq c hc₁ d hd₁, hm]
    have : ¬ (a ∈ s(c, d) ∨ b ∈ s(c, d)) := by
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hca, Ne.symm hda⟩, Ne.symm hcb, Ne.symm hdb⟩
    rw [if_neg this, if_pos rfl]; omega
  have hxN : x ≠ N := fun h => hN (h ▸ hx)
  have hxN1 : x ≠ N + 1 := fun h => hN1 (h ▸ hx)
  have hyN : y ≠ N := fun h => hN (h ▸ hy)
  have hyN1 : y ≠ N + 1 := fun h => hN1 (h ▸ hy)
  -- the maps
  obtain ⟨f', hf'⟩ : ∃ f' : V → ℕ, ∀ v, f' v = if v = a then N else if v = b then N + 1 else φ.f v :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : ℕ → V, ∀ z, g' z = if z = N then a else if z = N + 1 then b else φ.g z :=
    ⟨_, fun _ => rfl⟩
  have hf'a : f' a = N := by simp [hf']
  have hf'b : f' b = N + 1 := by simp [hf', Ne.symm hab]
  have hf'v : ∀ v, v ≠ a → v ≠ b → f' v = φ.f v := by intro v h1 h2; simp [hf', h1, h2]
  have hg'N : g' N = a := by simp [hg']
  have hg'N1 : g' (N + 1) = b := by simp [hg']
  have hg'z : ∀ z, z ≠ N → z ≠ N + 1 → g' z = φ.g z := by intro z h1 h2; simp [hg', h1, h2]
  have hends : ∀ z, InEnds (z1 es₁ x y N (N + 1)) z ↔ InEnds es₁ z ∨ z = N ∨ z = N + 1 :=
    fun z => ⟨inEnds_z1 hxy, inEnds_z1_of hxy⟩
  have hfN : ∀ v ∈ G₁.verts, φ.f v ≠ N ∧ φ.f v ≠ N + 1 := by
    intro v hv'
    have := φ.fv v hv'
    exact ⟨fun h => hN (h ▸ this), fun h => hN1 (h ▸ this)⟩
  -- the rows of `a` and `b`
  have rowA : ∀ v ∈ G.verts, G.mult s(a, v) = mult (z1 es₁ x y N (N + 1)) N (f' v) := by
    intro v hvG
    have key := mult_z1' es₁ x y N (N + 1) N (f' v) hxy
    rw [mult_eq_zero_of_not_inEnds hN, if_neg (sym2_ne_of_left (Ne.symm hxN) (Ne.symm hyN))] at key
    by_cases hva : v = a
    · rw [hva, hf'a] at key ⊢
      rw [hax a hab (Ne.symm hca)]
      rw [z1New_a_other hxN hxN.symm (by omega) (by omega)] at key
      omega
    by_cases hvb : v = b
    · rw [hvb, hf'b] at key ⊢
      rw [h3]
      rw [z1New_a_b hxN1 hyN] at key
      omega
    rw [hf'v v hva hvb] at key ⊢
    have hv₁ : v ∈ G₁.verts := (hmem₁ v).mpr ⟨hvG, hva, hvb⟩
    obtain ⟨hfvN, hfvN1⟩ := hfN v hv₁
    by_cases hvc : v = c
    · have hfv : φ.f v = x := by rw [hvc, hxdef]
      rw [hfv] at key ⊢
      rw [hvc, hc1]
      rw [z1New_a_x hxN1 (by omega)] at key
      omega
    · rw [hax v hvb hvc]
      have hfx : φ.f v ≠ x := fun h => hvc (by rw [← φ.gf v hv₁, h, ← hxdef, φ.gf c hc₁])
      rw [z1New_a_other hxN hfx hfvN1 (by omega)] at key
      omega
  have rowB : ∀ v ∈ G.verts, G.mult s(b, v) = mult (z1 es₁ x y N (N + 1)) (N + 1) (f' v) := by
    intro v hvG
    have key := mult_z1' es₁ x y N (N + 1) (N + 1) (f' v) hxy
    rw [mult_eq_zero_of_not_inEnds hN1, if_neg (sym2_ne_of_left (Ne.symm hxN1) (Ne.symm hyN1))] at key
    by_cases hva : v = a
    · rw [hva, hf'a] at key ⊢
      rw [show s(b, a) = s(a, b) from Sym2.eq_swap, h3]
      rw [z1New_b_a hxN1 hyN] at key
      omega
    by_cases hvb : v = b
    · rw [hvb, hf'b] at key ⊢
      rw [hbx b (Ne.symm hab) (Ne.symm hdb)]
      rw [z1New_b_other hyN1 hyN1.symm (by omega) (by omega)] at key
      omega
    rw [hf'v v hva hvb] at key ⊢
    have hv₁ : v ∈ G₁.verts := (hmem₁ v).mpr ⟨hvG, hva, hvb⟩
    obtain ⟨hfvN, hfvN1⟩ := hfN v hv₁
    by_cases hvd : v = d
    · have hfv : φ.f v = y := by rw [hvd, hydef]
      rw [hfv] at key ⊢
      rw [hvd, hd1]
      rw [z1New_b_y hyN (by omega)] at key
      omega
    · rw [hbx v hva hvd]
      have hfy : φ.f v ≠ y := fun h => hvd (by rw [← φ.gf v hv₁, h, ← hydef, φ.gf d hd₁])
      rw [z1New_b_other hyN1 hfy hfvN (by omega)] at key
      omega
  refine ⟨⟨f', g', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v hvG
    by_cases hva : v = a
    · rw [hva, hf'a, hg'N]
    by_cases hvb : v = b
    · rw [hvb, hf'b, hg'N1]
    have hv₁ : v ∈ G₁.verts := (hmem₁ v).mpr ⟨hvG, hva, hvb⟩
    obtain ⟨h1, h2⟩ := hfN v hv₁
    rw [hf'v v hva hvb, hg'z _ h1 h2, φ.gf v hv₁]
  · intro z hz
    rcases (hends z).mp hz with hz | hz | hz
    · have hzN : z ≠ N := fun h => hN (h ▸ hz)
      have hzN1 : z ≠ N + 1 := fun h => hN1 (h ▸ hz)
      have hg := (hmem₁ _).mp (φ.gv z hz)
      rw [hg'z z hzN hzN1, hf'v _ hg.2.1 hg.2.2, φ.fg z hz]
    · rw [hz, hg'N, hf'a]
    · rw [hz, hg'N1, hf'b]
  · intro v hvG
    rw [hends]
    by_cases hva : v = a
    · rw [hva, hf'a]; exact Or.inr (Or.inl rfl)
    by_cases hvb : v = b
    · rw [hvb, hf'b]; exact Or.inr (Or.inr rfl)
    rw [hf'v v hva hvb]
    exact Or.inl (φ.fv v ((hmem₁ v).mpr ⟨hvG, hva, hvb⟩))
  · intro z hz
    rcases (hends z).mp hz with hz | hz | hz
    · have hzN : z ≠ N := fun h => hN (h ▸ hz)
      have hzN1 : z ≠ N + 1 := fun h => hN1 (h ▸ hz)
      rw [hg'z z hzN hzN1]
      exact ((hmem₁ _).mp (φ.gv z hz)).1
    · rw [hz, hg'N]; exact haV
    · rw [hz, hg'N1]; exact hbV
  · intro u hu v hvG'
    by_cases hua : u = a
    · rw [hua, hf'a]; exact rowA v hvG'
    by_cases hub : u = b
    · rw [hub, hf'b]; exact rowB v hvG'
    by_cases hva : v = a
    · rw [hva, hf'a, Sym2.eq_swap, mult_comm]; exact rowA u hu
    by_cases hvb : v = b
    · rw [hvb, hf'b, Sym2.eq_swap, mult_comm]; exact rowB u hu
    rw [hf'v u hua hub, hf'v v hva hvb]
    have hu₁ : u ∈ G₁.verts := (hmem₁ u).mpr ⟨hu, hua, hub⟩
    have hv₁ : v ∈ G₁.verts := (hmem₁ v).mpr ⟨hvG', hva, hvb⟩
    obtain ⟨hu1, hu2⟩ := hfN u hu₁
    obtain ⟨hv1, hv2⟩ := hfN v hv₁
    have key := mult_z1' es₁ x y N (N + 1) (φ.f u) (φ.f v) hxy
    have hnew : z1New x y N (N + 1) (φ.f u) (φ.f v) = 0 := z1New_zero hu1 hu2 hv1 hv2
    rw [hnew, ← φ.mult_eq u hu₁ v hv₁, hm] at key
    have hnab : ¬ (a ∈ s(u, v) ∨ b ∈ s(u, v)) := by
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hua, Ne.symm hva⟩, Ne.symm hub, Ne.symm hvb⟩
    rw [if_neg hnab] at key
    have hiff : s(φ.f u, φ.f v) = s(x, y) ↔ s(u, v) = s(c, d) := by
      constructor
      · intro h
        have := congrArg (Sym2.map φ.g) h
        simpa [Sym2.map_mk, φ.gf u hu₁, φ.gf v hv₁, ← hxdef, ← hydef, φ.gf c hc₁, φ.gf d hd₁] using this
      · intro h
        have := congrArg (Sym2.map φ.f) h
        simpa [Sym2.map_mk, hxdef, hydef] using this
    by_cases hcd' : s(u, v) = s(c, d)
    · rw [if_pos hcd', if_pos (hiff.mpr hcd')] at key; omega
    · rw [if_neg hcd', if_neg (fun h => hcd' (hiff.mp h))] at key; omega

/-- **The (Y2) step, reversed on the instance side**: if `G ⟶ G₁` and `G₁ ≅ es₁`, then for the (unordered)
images `x, y` of the externals, `G ≅ z1 es₁ x y N (N + 1)` and `G ≅ z1 es₁ y x N (N + 1)` for every fresh `N`. -/
theorem iso_of_y2 {G G₁ : UMultigraph V} (h : Y2Step G G₁) {es₁ : Edges} (φ : Iso G₁ es₁) :
    ∃ x y : ℕ, mult es₁ x y ≠ 0 ∧ x ≠ y ∧ ∀ N, ¬ InEnds es₁ N → ¬ InEnds es₁ (N + 1) →
      Nonempty (Iso G (z1 es₁ x y N (N + 1))) ∧ Nonempty (Iso G (z1 es₁ y x N (N + 1))) := by
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hc1, hd1, hax, hbx, hv, hm⟩ := h
  have hcV : c ∈ G.verts := G.supp _ (by omega) c (Sym2.mem_mk_right a c)
  have hdV : d ∈ G.verts := G.supp _ (by omega) d (Sym2.mem_mk_right b d)
  have hc₁ : c ∈ G₁.verts := by rw [hv]; simp [Finset.mem_erase, hca, hcb, hcV]
  have hd₁ : d ∈ G₁.verts := by rw [hv]; simp [Finset.mem_erase, hda, hdb, hdV]
  refine ⟨φ.f c, φ.f d, ?_, fun h => hcd (by rw [← φ.gf c hc₁, h, φ.gf d hd₁]), fun N hN hN1 =>
    ⟨iso_of_y2_aux φ hab hcd hca hcb hda hdb h3 hc1 hd1 hax hbx hv hm N hN hN1, ?_⟩⟩
  · rw [← φ.mult_eq c hc₁ d hd₁, hm]
    have : ¬ (a ∈ s(c, d) ∨ b ∈ s(c, d)) := by
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hca, Ne.symm hda⟩, Ne.symm hcb, Ne.symm hdb⟩
    rw [if_neg this, if_pos rfl]; omega
  · -- the swapped data `(b, a, d, c)`
    refine iso_of_y2_aux φ (Ne.symm hab) (Ne.symm hcd) hdb hda hcb hca (by rw [Sym2.eq_swap]; exact h3) hd1 hc1
      hbx hax (by rw [hv, Finset.erase_right_comm]) (fun e => ?_) N hN hN1
    rw [hm e, Sym2.eq_swap (a := d)]
    simp only [or_comm]

/-! ## The doubled triangle is `tri` -/

theorem mult_tri_eq (u v : ℕ) (hu : u ≤ 2) (hv : v ≤ 2) : mult tri u v = if u = v then 0 else 2 := by
  interval_cases u <;> interval_cases v <;> decide

theorem iso_tri {T' : UMultigraph V} (h : IsDoubledTriangle T') : Nonempty (Iso T' tri) := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, hm⟩ := h
  let f : V → ℕ := fun v => if v = a then 0 else if v = b then 1 else 2
  let g : ℕ → V := fun z => if z = 0 then a else if z = 1 then b else c
  have hmemV : ∀ v, v ∈ T'.verts ↔ v = a ∨ v = b ∨ v = c := by intro v; rw [hv]; simp
  have hfle : ∀ v, f v ≤ 2 := by intro v; simp only [f]; split_ifs <;> omega
  refine ⟨⟨f, g, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v hvT
    rcases (hmemV v).mp hvT with rfl | rfl | rfl
    · simp [f, g]
    · simp [f, g, Ne.symm hab]
    · simp [f, g, Ne.symm hac, Ne.symm hbc]
  · intro z hz
    have := inEnds_tri.mp hz
    interval_cases z <;> simp [f, g, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  · intro v _; exact inEnds_tri.mpr (hfle v)
  · intro z hz
    rw [hmemV]; simp only [g]; split_ifs <;> simp
  · intro u hu v hv'
    rw [hm, mult_tri_eq _ _ (hfle u) (hfle v)]
    rcases (hmemV u).mp hu with rfl | rfl | rfl <;> rcases (hmemV v).mp hv' with rfl | rfl | rfl <;>
      simp [f, Sym2.eq_iff, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-! ## Relabelling -/

/-- Relabel a bond list. -/
def mapE (σ : ℕ → ℕ) (es : Edges) : Edges := es.map fun e => (σ e.1, σ e.2)

theorem mult_mapE (σ : ℕ → ℕ) (hσ : Function.Injective σ) (es : Edges) (u v : ℕ) :
    mult (mapE σ es) (σ u) (σ v) = mult es u v := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [mapE, List.map_cons] at ih ⊢
    rw [mult_cons, mult_cons, ih]
    congr 2
    simp only [isPair, nat_beq_eq_decide, hσ.eq_iff]

/-- Relabelling by an involution of `ℕ` is an isomorphism. -/
def Iso.ofInvolution (σ : ℕ → ℕ) (hσ : ∀ x, σ (σ x) = x) (es : Edges) : Iso (ofEdges es) (mapE σ es) where
  f := σ
  g := σ
  gf := fun v _ => hσ v
  fg := fun x _ => hσ x
  fv := fun v hv => by
    obtain ⟨e, he, h⟩ := mem_ofEdges_verts.mp hv
    refine ⟨(σ e.1, σ e.2), List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  gv := fun x hx => by
    obtain ⟨e', he', h⟩ := hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    refine mem_ofEdges_verts.mpr ⟨e, he, ?_⟩
    rcases h with h | h
    · left; rw [← h, hσ]
    · right; rw [← h, hσ]
  mult_eq := fun u _ v _ => by
    rw [ofEdges_mult, mult_mapE σ (Function.LeftInverse.injective hσ)]

/-- Normalized bond. -/
def normE (e : ℕ × ℕ) : ℕ × ℕ := (min e.1 e.2, max e.1 e.2)

theorem sameMult_of_perm {es es' : Edges} (h : (es.map normE).Perm (es'.map normE)) : SameMult es es' := by
  intro u v
  have hn : ∀ l : Edges, l.map (fun e => s(e.1, e.2)) = (l.map normE).map fun e => s(e.1, e.2) := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp, normE]
    rcases le_total e.1 e.2 with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, Sym2.eq_swap]
  rw [mult_eq_count, mult_eq_count, hn es, hn es']
  exact (h.map _).count_eq _

/-! ## At most two triple bonds -/

/-- **At most two triple pairs** (the closure of a T-vine: N2 Lemma 1.7's hypothesis). -/
def AtMostTwoTriples (G : UMultigraph V) : Prop :=
  ∀ e₁ e₂ e₃ : Sym2 V, G.mult e₁ = 3 → G.mult e₂ = 3 → G.mult e₃ = 3 → e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃

/-- The same, for a bond list. -/
def AtMostTwoTriplesE (es : Edges) : Prop :=
  ∀ u₁ v₁ u₂ v₂ u₃ v₃ : ℕ, mult es u₁ v₁ = 3 → mult es u₂ v₂ = 3 → mult es u₃ v₃ = 3 →
    s(u₁, v₁) = s(u₂, v₂) ∨ s(u₁, v₁) = s(u₃, v₃) ∨ s(u₂, v₂) = s(u₃, v₃)

theorem atMostTwoTriplesE_of_iso {G : UMultigraph V} {es : Edges} (φ : Iso G es) (h : AtMostTwoTriples G) :
    AtMostTwoTriplesE es := by
  intro u₁ v₁ u₂ v₂ u₃ v₃ h1 h2 h3
  have e1 := inEnds_of_mult_ne_zero (show mult es u₁ v₁ ≠ 0 by omega)
  have e2 := inEnds_of_mult_ne_zero (show mult es u₂ v₂ ≠ 0 by omega)
  have e3 := inEnds_of_mult_ne_zero (show mult es u₃ v₃ ≠ 0 by omega)
  have back : ∀ x y x' y', InEnds es x → InEnds es y → InEnds es x' → InEnds es y' →
      s(φ.g x, φ.g y) = s(φ.g x', φ.g y') → s(x, y) = s(x', y') := by
    intro x y x' y' hx hy hx' hy' hh
    have := congrArg (Sym2.map φ.f) hh
    simpa [Sym2.map_mk, φ.fg x hx, φ.fg y hy, φ.fg x' hx', φ.fg y' hy'] using this
  rcases h _ _ _ (by rw [φ.mult_g e1.1 e1.2]; exact h1) (by rw [φ.mult_g e2.1 e2.2]; exact h2)
    (by rw [φ.mult_g e3.1 e3.2]; exact h3) with hh | hh | hh
  · exact Or.inl (back _ _ _ _ e1.1 e1.2 e2.1 e2.2 hh)
  · exact Or.inr (Or.inl (back _ _ _ _ e1.1 e1.2 e3.1 e3.2 hh))
  · exact Or.inr (Or.inr (back _ _ _ _ e2.1 e2.2 e3.1 e3.2 hh))

/-- `AtMostTwoTriples` passes along a (Y2) step. -/
theorem atMostTwoTriples_of_y2 {G G₁ : UMultigraph V} (h : Y2Step G G₁) (hG : AtMostTwoTriples G) :
    AtMostTwoTriples G₁ := by
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hc1, hd1, hax, hbx, hv, hm⟩ := h
  -- a triple of `G₁` avoids `a, b`, and is a triple of `G` or the pair `s(c, d)`
  have key : ∀ e, G₁.mult e = 3 → ¬ (a ∈ e ∨ b ∈ e) ∧ (G.mult e = 3 ∨ e = s(c, d)) := by
    intro e he
    rw [hm] at he
    by_cases h1 : a ∈ e ∨ b ∈ e
    · rw [if_pos h1] at he; omega
    · rw [if_neg h1] at he
      by_cases h2 : e = s(c, d)
      · exact ⟨h1, Or.inr h2⟩
      · rw [if_neg h2] at he; exact ⟨h1, Or.inl (by omega)⟩
  have hab3 : ∀ e, ¬ (a ∈ e ∨ b ∈ e) → e ≠ s(a, b) := by
    intro e he hh; exact he (Or.inl (hh ▸ Sym2.mem_mk_left a b))
  intro e₁ e₂ e₃ m1 m2 m3
  obtain ⟨n1, k1⟩ := key e₁ m1
  obtain ⟨n2, k2⟩ := key e₂ m2
  obtain ⟨n3, k3⟩ := key e₃ m3
  -- replace a member equal to `s(c, d)` by `s(a, b)`
  let r : Sym2 V → Sym2 V := fun e => if e = s(c, d) then s(a, b) else e
  have hr : ∀ e, ¬ (a ∈ e ∨ b ∈ e) → (G.mult e = 3 ∨ e = s(c, d)) → G.mult (r e) = 3 := by
    intro e _ he
    simp only [r]; split_ifs with hh
    · exact h3
    · exact he.resolve_right hh
  have hinj : ∀ e e', ¬ (a ∈ e ∨ b ∈ e) → ¬ (a ∈ e' ∨ b ∈ e') → r e = r e' → e = e' := by
    intro e e' he he' hh
    simp only [r] at hh
    split_ifs at hh with h1 h2 h2
    · rw [h1, h2]
    · exact absurd hh.symm (hab3 e' he')
    · exact absurd hh (hab3 e he)
    · exact hh
  rcases hG _ _ _ (hr e₁ n1 k1) (hr e₂ n2 k2) (hr e₃ n3 k3) with hh | hh | hh
  · exact Or.inl (hinj _ _ n1 n2 hh)
  · exact Or.inr (Or.inl (hinj _ _ n1 n3 hh))
  · exact Or.inr (Or.inr (hinj _ _ n2 n3 hh))

end WaveTurbulence.TVine.Checker
