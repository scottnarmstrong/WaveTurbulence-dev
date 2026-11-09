/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.VineII

/-!
# B2's vine (II) template is the uniform ladder

* `railBonds_map`: the rails of `insertRungs` in closed form;
* `ladTau M`: the relabelling of `VineType.II.expand [M]` onto the uniform ladder, `ladTauInv M` its inverse;
* `template_II_map`: `(expand [M]).bonds` relabelled by `ladTau M` is `ladMS M`;
* `isVineXU_II_iff`: `IsVineXU .II X p q` iff `X` is a block and is the uniform ladder under some labelling;
* `isVineXU_I_of`: a block whose bonds are the double bond `0 = 1` under some labelling is a vine (I).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

/-! ## The template as a uniform ladder -/

/-- The rails `z – c – c+1 – ⋯ – c+m-1 – z'` in closed form. -/
theorem railBonds_map (z z' c m : ℕ) :
    railBonds z ((List.range m).map (c + ·)) z' =
      (List.range (m + 1)).map fun i => (if i = 0 then z else c + i - 1, if i = m then z' else c + i) := by
  induction m generalizing z' with
  | zero => simp [railBonds]
  | succ m ih =>
    have hlen : (z :: (List.range m).map (c + ·)).length = ((List.range m).map (c + ·) ++ [c + m]).length := by
      simp
    have e1 : railBonds z ((List.range (m + 1)).map (c + ·)) z' =
        railBonds z ((List.range m).map (c + ·)) (c + m) ++ [(c + m, z')] := by
      unfold railBonds
      rw [List.range_succ, List.map_append, List.map_singleton, ← List.cons_append,
        List.zip_append hlen]
      rfl
    rw [e1, ih, List.range_succ (n := m + 1), List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Prod.mk.injEq, true_and]
      split_ifs <;> omega
    · simp

/-- The relabelling of the expanded template onto the uniform ladder. -/
def ladTau (M x : ℕ) : ℕ := if x < 4 then x else if x < 4 + M then 2 * x - 4 else 2 * (x - M) - 3

/-- Its inverse on `range (2M + 4)`. -/
def ladTauInv (M y : ℕ) : ℕ := if y < 4 then y else if y % 2 = 0 then y / 2 + 2 else (y + 3) / 2 + M

theorem ladTau_injective (M : ℕ) : Function.Injective (ladTau M) := by
  intro x y h; unfold ladTau at h; split_ifs at h <;> omega

theorem ladTauInv_ladTau {M x : ℕ} (hx : x < 2 * M + 4) : ladTauInv M (ladTau M x) = x := by
  unfold ladTau ladTauInv; split_ifs <;> omega

theorem ladTau_ladTauInv {M y : ℕ} (hy : y < 2 * M + 4) : ladTau M (ladTauInv M y) = y := by
  unfold ladTau ladTauInv; split_ifs <;> omega

theorem ladTau_lt {M x : ℕ} (hx : x < 2 * M + 4) : ladTau M x < 2 * M + 4 := by
  unfold ladTau; split_ifs <;> omega

theorem ladTauInv_lt {M y : ℕ} (hy : y < 2 * M + 4) : ladTauInv M y < 2 * M + 4 := by
  unfold ladTauInv; split_ifs <;> omega

theorem ladTau_ge {M x : ℕ} (hx : 2 * M + 4 ≤ x) : 2 * M + 4 ≤ ladTau M x := by
  unfold ladTau; split_ifs <;> omega

theorem ladTau_small {M x : ℕ} (hx : x < 4) : ladTau M x = x := by unfold ladTau; rw [if_pos hx]

theorem ladTauInv_small {M y : ℕ} (hy : y < 4) : ladTauInv M y = y := by unfold ladTauInv; rw [if_pos hy]

theorem count_ladMS_of_ge {M x y : ℕ} (hx : 2 * M + 4 ≤ x) : (ladMS M).count s(x, y) = 0 := by
  have h1 : ¬IsLadRung M x y := by unfold IsLadRung; omega
  have h2 : ¬IsLadRail M x y := by unfold IsLadRail IsLadRail1; omega
  rw [count_ladMS, if_neg h1, if_neg h2]

theorem expandII (m : ℕ) : VineType.II.expand [m] = insertRungs VineType.II.template ((2, 1), (3, 1)) m := rfl

theorem expandII_n (m : ℕ) : (VineType.II.expand [m]).n = 2 * m + 4 := by
  rw [expandII]; unfold insertRungs; split_ifs with h
  · subst h; rfl
  · show 4 + 2 * m = 2 * m + 4; omega

theorem expandII_bonds {m : ℕ} (hm : m ≠ 0) : (VineType.II.expand [m]).bonds =
    [(0, 2), (0, 3), (2, 3), (2, 3)] ++ railBonds 2 ((List.range m).map (4 + ·)) 1 ++
      railBonds 3 ((List.range m).map (4 + m + ·)) 1 ++
      (List.zip ((List.range m).map (4 + ·)) ((List.range m).map (4 + m + ·))).flatMap (fun p => [p, p]) := by
  rw [expandII]; unfold insertRungs; rw [if_neg hm]; rfl

theorem coe_flatMap_double (L : List (Sym2 ℕ)) :
    ((L.flatMap fun p => [p, p] : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) = (L : Multiset (Sym2 ℕ)) + L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih]
    simp only [← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
    rfl

theorem map_flatMap_double {α β : Type*} (f : α → β) (L : List α) :
    (L.flatMap fun p => [p, p]).map f = (L.map f).flatMap fun p => [p, p] := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- **The template is the ladder.** -/
theorem template_II_map (m : ℕ) :
    (((VineType.II.expand [m]).bonds.map fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)).map
      (Sym2.map (ladTau m)) = ladMS m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · decide
  rw [expandII_bonds hm.ne', Multiset.map_coe, List.map_map]
  simp only [List.map_append]
  have hA : List.map (Sym2.map (ladTau m) ∘ fun p : ℕ × ℕ => s(p.1, p.2)) [(0, 2), (0, 3), (2, 3), (2, 3)] =
      [s(0, 2), s(0, 3), s(2, 3), s(2, 3)] := by
    simp [ladTau]
  have hU : List.map (Sym2.map (ladTau m) ∘ fun p : ℕ × ℕ => s(p.1, p.2))
      (railBonds 2 ((List.range m).map (4 + ·)) 1) =
      (List.range m).map (fun j => s(2 + 2 * j, 4 + 2 * j)) ++ [s(2 + 2 * m, 1)] := by
    rw [railBonds_map, List.map_map, List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
      simp only [Function.comp_apply, Sym2.map_mk, ladTau]
      rw [Sym2.eq_iff]; left; constructor <;> split_ifs <;> omega
    · simp only [Function.comp_apply, Sym2.map_mk, ladTau, List.singleton_inj]
      rw [Sym2.eq_iff]; left; constructor <;> split_ifs <;> omega
  have hV : List.map (Sym2.map (ladTau m) ∘ fun p : ℕ × ℕ => s(p.1, p.2))
      (railBonds 3 ((List.range m).map (4 + m + ·)) 1) =
      (List.range m).map (fun j => s(3 + 2 * j, 5 + 2 * j)) ++ [s(3 + 2 * m, 1)] := by
    rw [railBonds_map, List.map_map, List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
      simp only [Function.comp_apply, Sym2.map_mk, ladTau]
      rw [Sym2.eq_iff]; left; constructor <;> split_ifs <;> omega
    · simp only [Function.comp_apply, Sym2.map_mk, ladTau, List.singleton_inj]
      rw [Sym2.eq_iff]; left; constructor <;> split_ifs <;> omega
  have hR : List.map (Sym2.map (ladTau m) ∘ fun p : ℕ × ℕ => s(p.1, p.2))
      ((List.zip ((List.range m).map (4 + ·)) ((List.range m).map (4 + m + ·))).flatMap fun p => [p, p]) =
      ((List.range m).map fun j => s(4 + 2 * j, 5 + 2 * j)).flatMap fun p => [p, p] := by
    rw [map_flatMap_double, List.zip_map', List.map_map]
    congr 1
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp_apply, Sym2.map_mk, ladTau]
    rw [Sym2.eq_iff]; left; constructor <;> split_ifs <;> omega
  rw [hA, hU, hV, hR]
  have hRung : ladRungs m = s(2, 3) :: (List.range m).map fun j => s(4 + 2 * j, 5 + 2 * j) := by
    unfold ladRungs
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.cons_eq_cons.mpr ⟨by simp, ?_⟩
    apply List.map_congr_left; intro j _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [Sym2.eq_iff]; left; omega
  unfold ladMS ladRails
  rw [hRung]
  simp only [← Multiset.coe_add, coe_flatMap_double, ← Multiset.cons_coe, Multiset.coe_nil,
    ← Multiset.singleton_add, add_zero]
  abel

/-! ## Labelled multigraphs -/

section Graph

variable {V : Type*} [DecidableEq V]

theorem mem_of_mem_bondMultiset {G : UMultigraph V} {e : Sym2 V} (he : e ∈ bondMultiset G) {x : V}
    (hx : x ∈ e) : x ∈ G.verts := by
  unfold bondMultiset at he
  obtain ⟨e', he', hm⟩ := Multiset.mem_sum.mp he
  rw [(Multiset.mem_replicate.mp hm).2] at hx
  exact Finset.mem_sym2_iff.mp he' x hx

theorem sym2_eq_iff_of_injOn {S : Finset V} {g : V → ℕ} (hinj : Set.InjOn g S) {x y z t : V}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (ht : t ∈ S) : s(g x, g y) = s(g z, g t) ↔ s(x, y) = s(z, t) := by
  rw [Sym2.eq_iff, Sym2.eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hinj hx hz h1, hinj hy ht h2⟩
    · exact Or.inr ⟨hinj hx ht h1, hinj hy hz h2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

theorem count_map_sym2 {S : Finset V} {g : V → ℕ} (hinj : Set.InjOn g S) {A : Multiset (Sym2 V)}
    (hA : ∀ e ∈ A, ∀ x ∈ e, x ∈ S) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (A.map (Sym2.map g)).count s(g x, g y) = A.count s(x, y) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro e he
  induction e using Sym2.ind with
  | _ z t =>
  exact sym2_eq_iff_of_injOn hinj hx hy (hA _ he z (Sym2.mem_mk_left z t)) (hA _ he t (Sym2.mem_mk_right z t))

theorem mult_eq_count_of_map {G : UMultigraph V} {f : V → ℕ} (hinj : Set.InjOn f G.verts)
    {T : Multiset (Sym2 ℕ)} (h : (bondMultiset G).map (Sym2.map f) = T) {x y : V} (hx : x ∈ G.verts)
    (hy : y ∈ G.verts) : G.mult s(x, y) = T.count s(f x, f y) := by
  rw [← h, count_map_sym2 hinj (fun e he z hz => mem_of_mem_bondMultiset he hz) hx hy, count_bondMultiset]

theorem map_eq_of_mult {G : UMultigraph V} {f : V → ℕ} {n : ℕ} {T : Multiset (Sym2 ℕ)}
    (hinj : Set.InjOn f G.verts) (himg : G.verts.image f = Finset.range n)
    (hT : ∀ x y, n ≤ x → T.count s(x, y) = 0)
    (hm : ∀ x ∈ G.verts, ∀ y ∈ G.verts, G.mult s(x, y) = T.count s(f x, f y)) :
    (bondMultiset G).map (Sym2.map f) = T := by
  have hlt : ∀ x ∈ G.verts, f x < n := fun x hx => by
    have := Finset.mem_image_of_mem f hx; rw [himg, Finset.mem_range] at this; exact this
  have hpre : ∀ u < n, ∃ x ∈ G.verts, f x = u := fun u hu => by
    have : u ∈ G.verts.image f := by rw [himg, Finset.mem_range]; exact hu
    exact Finset.mem_image.mp this
  apply Multiset.ext'
  intro e
  induction e using Sym2.ind with
  | _ u v =>
  by_cases huv : u < n ∧ v < n
  · obtain ⟨x, hx, rfl⟩ := hpre u huv.1
    obtain ⟨y, hy, rfl⟩ := hpre v huv.2
    rw [count_map_sym2 hinj (fun e he z hz => mem_of_mem_bondMultiset he hz) hx hy, count_bondMultiset,
      hm x hx y hy]
  · have h1 : Multiset.count s(u, v) ((bondMultiset G).map (Sym2.map f)) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨e, he, hee⟩ := Multiset.mem_map.mp hmem
      induction e using Sym2.ind with
      | _ z t =>
      have hz := hlt z (mem_of_mem_bondMultiset he (Sym2.mem_mk_left z t))
      have ht := hlt t (mem_of_mem_bondMultiset he (Sym2.mem_mk_right z t))
      have : s(f z, f t) = s(u, v) := hee
      rw [Sym2.eq_iff] at this
      omega
    have h2 : T.count s(u, v) = 0 := by
      by_cases hu : n ≤ u
      · exact hT u v hu
      · rw [Sym2.eq_swap]; exact hT v u (by omega)
    rw [h1, h2]

/-- `G` is the uniform ladder with `M + 1` rungs under the labelling `g` (joints `p, q ↦ {0, 1}`). -/
def IsLadderOf (G : UMultigraph V) (p q : V) (M : ℕ) (g : V → ℕ) : Prop :=
  Set.InjOn g G.verts ∧ G.verts.image g = Finset.range (2 * M + 4) ∧ ({g p, g q} : Finset ℕ) = {0, 1} ∧
    ∀ x ∈ G.verts, ∀ y ∈ G.verts, G.mult s(x, y) = (ladMS M).count s(g x, g y)

theorem lt_two_of_pair {a b : ℕ} (h : ({a, b} : Finset ℕ) = {0, 1}) : a < 2 ∧ b < 2 := by
  have ha : a ∈ ({0, 1} : Finset ℕ) := by rw [← h]; simp
  have hb : b ∈ ({0, 1} : Finset ℕ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  omega

theorem image_range_of_inv {S : Finset ℕ} {n : ℕ} {φ ψ : ℕ → ℕ} (hS : S = Finset.range n)
    (hφ : ∀ x < n, φ x < n) (hψ : ∀ y < n, ψ y < n) (hφψ : ∀ y < n, φ (ψ y) = y) :
    S.image φ = Finset.range n := by
  subst hS
  ext y; simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hφ x hx
  · intro hy; exact ⟨ψ y, hψ y hy, hφψ y hy⟩

/-- **Vine (II) is the uniform ladder.** -/
theorem isVineXU_II_iff {G : UMultigraph V} {p q : V} :
    IsVineXU .II G p q ↔ IsBlockU G p q ∧ ∃ M g, IsLadderOf G p q M g := by
  constructor
  · rintro ⟨hB, k, hk, f, hinj, himg, hpq, hbonds⟩
    obtain ⟨M, rfl⟩ : ∃ M, k = [M] := List.length_eq_one_iff.mp hk
    rw [expandII_n] at himg
    refine ⟨hB, M, ladTau M ∘ f, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy h; exact hinj hx hy (ladTau_injective M h)
    · rw [← Finset.image_image]
      exact image_range_of_inv himg (fun x hx => ladTau_lt hx) (fun y hy => ladTauInv_lt hy)
        (fun y hy => ladTau_ladTauInv hy)
    · have := lt_two_of_pair hpq
      simp only [Function.comp_apply, ladTau_small (M := M) (show f p < 4 by omega),
        ladTau_small (M := M) (show f q < 4 by omega)]
      exact hpq
    · intro x hx y hy
      rw [mult_eq_count_of_map hinj hbonds hx hy, ← template_II_map M, Function.comp_apply,
        Function.comp_apply, show s(ladTau M (f x), ladTau M (f y)) = Sym2.map (ladTau M) s(f x, f y) from rfl,
        Multiset.count_map_eq_count' _ _ (Sym2.map.injective (ladTau_injective M))]
  · rintro ⟨hB, M, g, hinj, himg, hpq, hm⟩
    have hlt : ∀ x ∈ G.verts, g x < 2 * M + 4 := fun x hx => by
      have := Finset.mem_image_of_mem g hx; rw [himg, Finset.mem_range] at this; exact this
    have hinj' : Set.InjOn (ladTauInv M ∘ g) G.verts := by
      intro x hx y hy h
      apply hinj hx hy
      have := congrArg (ladTau M) h
      simp only [Function.comp_apply] at this
      rwa [ladTau_ladTauInv (hlt x hx), ladTau_ladTauInv (hlt y hy)] at this
    have himg' : G.verts.image (ladTauInv M ∘ g) = Finset.range (2 * M + 4) := by
      rw [← Finset.image_image]
      exact image_range_of_inv himg (fun x hx => ladTauInv_lt hx) (fun y hy => ladTau_lt hy)
        (fun y hy => ladTauInv_ladTau hy)
    refine ⟨hB, [M], rfl, ladTauInv M ∘ g, hinj', by rw [expandII_n]; exact himg', ?_, ?_⟩
    · have := lt_two_of_pair hpq
      simp only [Function.comp_apply, ladTauInv_small (M := M) (show g p < 4 by omega),
        ladTauInv_small (M := M) (show g q < 4 by omega)]
      exact hpq
    · apply map_eq_of_mult hinj' himg'
      · intro x y hx
        rw [← Multiset.count_map_eq_count' _ _ (Sym2.map.injective (ladTau_injective M)), template_II_map]
        exact count_ladMS_of_ge (ladTau_ge hx)
      · intro x hx y hy
        rw [hm x hx y hy, ← template_II_map M, Function.comp_apply, Function.comp_apply,
          show s(g x, g y) = Sym2.map (ladTau M) s(ladTauInv M (g x), ladTauInv M (g y)) by
            rw [Sym2.map_mk, ladTau_ladTauInv (hlt x hx), ladTau_ladTauInv (hlt y hy)],
          Multiset.count_map_eq_count' _ _ (Sym2.map.injective (ladTau_injective M))]

/-- **A double bond is a vine (I).** -/
theorem isVineXU_I_of {G : UMultigraph V} {p q : V} (hB : IsBlockU G p q) (hV : G.verts = {p, q})
    (hm : G.mult s(p, q) = 2) : IsVineXU .I G p q := by
  have hpq : p ≠ q := hB.2.2.1
  have hm' : G.mult s(q, p) = 2 := by rw [Sym2.eq_swap]; exact hm
  have hlp : G.mult s(p, p) = 0 := by
    have hd := hB.2.2.2.1
    unfold deg at hd; rw [hV, Finset.sum_pair hpq] at hd; omega
  have hlq : G.mult s(q, q) = 0 := by
    have hd := hB.2.2.2.2.1
    unfold deg at hd; rw [hV, Finset.sum_pair hpq] at hd; omega
  let f : V → ℕ := fun x => if x = p then 0 else 1
  have hfp : f p = 0 := by simp [f]
  have hfq : f q = 1 := by simp [f, hpq.symm]
  have hinj : Set.InjOn f G.verts := by
    intro x hx y hy h
    rw [Finset.mem_coe, hV, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rw [hfp, hfq] at h; exact absurd h (by decide)
    · rw [hfp, hfq] at h; exact absurd h (by decide)
    · rfl
  have himg : G.verts.image f = Finset.range 2 := by
    rw [hV, Finset.image_insert, Finset.image_singleton, hfp, hfq]; decide
  have hcnt : ∀ e, ((VineType.I.expand []).bonds.map (fun p => s(p.1, p.2)) : Multiset (Sym2 ℕ)).count e =
      if e = s(0, 1) then 2 else 0 := by
    intro e
    show Multiset.count e (s(0, 1) ::ₘ s(0, 1) ::ₘ 0) = _
    rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
    split_ifs <;> rfl
  refine ⟨hB, [], rfl, f, hinj, himg, by rw [hfp, hfq], ?_⟩
  apply map_eq_of_mult hinj himg
  · intro x y hx
    rw [hcnt, if_neg]
    rw [Sym2.eq_iff]; omega
  · intro x hx y hy
    rw [hcnt]
    rw [hV, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rw [hlp, hfp, if_neg (by rw [Sym2.eq_iff]; omega)]
    · rw [hm, hfp, hfq, if_pos rfl]
    · rw [hm', hfp, hfq, if_pos Sym2.eq_swap]
    · rw [hlq, hfq, if_neg (by rw [Sym2.eq_iff]; omega)]

end Graph

end WaveTurbulence.TVine.Core
