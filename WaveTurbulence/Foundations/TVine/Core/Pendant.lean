/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.SmoothInv

/-!
# N3 Lemma 6.2: no two pendant poles (path-wise; N3 §1.4, REF3)

`pendantPoles_holds : PendantPolesStatement`. A T-vine has no two disjoint nonempty sets of interior atoms with two
leaving bonds each.

Proof (N3 Lemma 6.2): transfer both sets to the closure (Step 1: two leaving bonds, no internal triple bond), then
follow the given (Y2)-path. A set `K` is *intact* (`Intact H K`) while it has two leaving bonds and no internal
triple bond. A move never touches an intact set; it keeps it intact unless both its externals lie in it, and then the
whole graph is `K ∪ {p, q}`, which leaves no room for the other (disjoint, intact) set. At the end a doubled triangle
has no set with two leaving bonds.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- `K` is intact in `H`: inside `H`, two leaving bonds, no internal triple bond. -/
def Intact (H : UMultigraph V) (K : Finset V) : Prop :=
  K ⊆ H.verts ∧ cut H K = 2 ∧ ∀ u ∈ K, ∀ w ∈ K, H.mult s(u, w) ≤ 2

/-- A doubled triangle has no set with exactly two leaving bonds. -/
theorem doubledTriangle_cut_ne_two {T : UMultigraph V} (hT : IsDoubledTriangle T) {K : Finset V}
    (hK : K ⊆ T.verts) : cut T K ≠ 2 := by
  intro hc
  -- some atom inside and some atom outside
  obtain ⟨u, hu⟩ : K.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; subst h; simp [cut] at hc
  obtain ⟨w, hw, hwK⟩ : ∃ w ∈ T.verts, w ∉ K := by
    by_contra h; push_neg at h
    have : T.verts \ K = ∅ := by
      ext x; simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and, not_not]; exact h x
    simp [cut, this] at hc
  have huw : u ≠ w := fun h => hwK (h ▸ hu)
  obtain ⟨t, ht, htu, htw⟩ := doubledTriangle_third hT u w
  have h1 := doubledTriangle_mult_of_ne hT (hK hu) hw huw
  by_cases htK : t ∈ K
  · have h2 := doubledTriangle_mult_of_ne hT ht hw htw
    -- rows `u` and `t`
    have hrow : ∀ x ∈ K, T.mult s(x, w) ≤ ∑ w' ∈ T.verts \ K, T.mult s(x, w') := fun x _ =>
      Finset.single_le_sum (f := fun w' => T.mult s(x, w')) (fun _ _ => Nat.zero_le _)
        (Finset.mem_sdiff.mpr ⟨hw, hwK⟩)
    have hsub : ({u, t} : Finset V) ⊆ K := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset (f := fun x => ∑ w' ∈ T.verts \ K, T.mult s(x, w')) hsub
    rw [Finset.sum_pair (Ne.symm htu)] at this
    have := hrow u hu; have := hrow t htK
    unfold cut at hc; omega
  · have h2 := doubledTriangle_mult_of_ne hT (hK hu) ht (Ne.symm htu)
    have hsub : ({w, t} : Finset V) ⊆ T.verts \ K := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hw, hwK⟩
      · exact Finset.mem_sdiff.mpr ⟨ht, htK⟩
    have := Finset.sum_le_sum_of_subset (f := fun x => T.mult s(u, x)) hsub
    rw [Finset.sum_pair (Ne.symm htw)] at this
    have hrowu := Finset.single_le_sum (f := fun x => ∑ w' ∈ T.verts \ K, T.mult s(x, w'))
      (fun _ _ => Nat.zero_le _) hu
    unfold cut at hc; omega

/-- One (Y2) move and an intact set. -/
theorem intact_step {H : UMultigraph V} {K : Finset V} (hK : Intact H K) {p q p' q' : V}
    (hP : IsY2Pair H p q p' q') :
    p ∉ K ∧ q ∉ K ∧ (¬ (p' ∈ K ∧ q' ∈ K) → Intact (y2Move H p q p' q') K) ∧
      (p' ∈ K ∧ q' ∈ K → ∀ u ∈ K, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ K ∨ w = p ∨ w = q) := by
  obtain ⟨hKV, hc, hm⟩ := hK
  have h3 := hP.mult_ab
  have hpK : p ∉ K := by
    intro hp
    by_cases hq : q ∈ K
    · have := hm p hp q hq; omega
    · have := cut_ge_term H hp hP.b_mem hq; omega
  have hqK : q ∉ K := by
    intro hq
    have := cut_ge_term H hq hP.a_mem hpK
    rw [Sym2.eq_swap] at this; omega
  -- the bonds from `K` to `p` and `q`
  have hrowp : ∑ u ∈ K, H.mult s(u, p) = if p' ∈ K then 1 else 0 := by
    have h : ∀ u ∈ K, H.mult s(u, p) = if u = p' then 1 else 0 := by
      intro u hu; rw [Sym2.eq_swap, hP.mult_a, if_neg (fun h => hqK (by rw [← h]; exact hu))]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' K p' (fun _ => 1)]
  have hrowq : ∑ u ∈ K, H.mult s(u, q) = if q' ∈ K then 1 else 0 := by
    have h : ∀ u ∈ K, H.mult s(u, q) = if u = q' then 1 else 0 := by
      intro u hu; rw [Sym2.eq_swap, hP.mult_b, if_neg (fun h => hpK (by rw [← h]; exact hu))]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' K q' (fun _ => 1)]
  set S := (H.verts.erase p).erase q with hS
  set W := S \ K with hW
  have hpW : p ∉ W := by simp [hW, hS]
  have hqW : q ∉ W := by simp [hW, hS]
  have hsd : H.verts \ K = insert p (insert q W) := by
    ext x; simp only [hW, hS, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxK⟩
      by_cases hxp : x = p
      · exact Or.inl hxp
      · by_cases hxq : x = q
        · exact Or.inr (Or.inl hxq)
        · exact Or.inr (Or.inr ⟨⟨hxq, hxp, hx⟩, hxK⟩)
    · rintro (rfl | rfl | ⟨⟨_, _, hx⟩, hxK⟩)
      · exact ⟨hP.a_mem, hpK⟩
      · exact ⟨hP.b_mem, hqK⟩
      · exact ⟨hx, hxK⟩
  have hcutH : cut H K = ∑ u ∈ K, ∑ w ∈ W, H.mult s(u, w) + (if p' ∈ K then 1 else 0) + (if q' ∈ K then 1 else 0) := by
    unfold cut
    rw [hsd]
    simp only [Finset.sum_insert (Finset.mem_insert.not.mpr (by rintro (h | h); exacts [hP.ne h, hpW h])),
      Finset.sum_insert hqW, Finset.sum_add_distrib, hrowp, hrowq]
    ring
  have hKp : ∀ u ∈ K, u ≠ p := fun u hu h => hpK (h ▸ hu)
  have hKq : ∀ u ∈ K, u ≠ q := fun u hu h => hqK (h ▸ hu)
  refine ⟨hpK, hqK, fun hnot => ?_, fun hboth u hu w hw hmw => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [y2Move_verts hP]; simp [hKV hx, hKp x hx, hKq x hx]
    · -- the cut is unchanged
      have hS' : cut (y2Move H p q p' q') K =
          ∑ u ∈ K, ∑ w ∈ W, (H.mult s(u, w) + (if s(u, w) = s(p', q') then 1 else 0)) := by
        unfold cut
        rw [y2Move_verts hP, ← hS, ← hW]
        apply Finset.sum_congr rfl; intro u hu
        apply Finset.sum_congr rfl; intro w hw
        have hwS := (Finset.mem_sdiff.mp hw).1
        rw [y2Move_mult, if_neg]
        rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
        · exact hKp u hu h.symm
        · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hwS) h.symm
        · exact hKq u hu h.symm
        · exact Finset.ne_of_mem_erase hwS h.symm
      have hp'S : p' ∈ S := by simp [hS, hP.c_ne_a, hP.c_ne_b, hP.c_mem]
      have hq'S : q' ∈ S := by simp [hS, hP.d_ne_a, hP.d_ne_b, hP.d_mem]
      have hind : ∑ u ∈ K, ∑ w ∈ W, (if s(u, w) = s(p', q') then 1 else 0) =
          (if p' ∈ K then 1 else 0) + (if q' ∈ K then 1 else 0) := by
        have hrow : ∀ u, ∑ w ∈ W, (if s(u, w) = s(p', q') then 1 else 0) =
            (if u = p' ∧ q' ∈ W then 1 else 0) + (if u = q' ∧ p' ∈ W then 1 else 0) := by
          intro u
          by_cases hu1 : u = p'
          · subst hu1
            have : ∀ w, (s(u, w) = s(u, q')) ↔ w = q' := fun w => Sym2.congr_right
            simp only [this, Finset.sum_ite_eq', hP.ext_ne, false_and, if_false, add_zero, true_and]
          · by_cases hu2 : u = q'
            · subst hu2
              have : ∀ w, (s(u, w) = s(p', u)) ↔ w = p' := fun w => by
                rw [Sym2.eq_swap (a := p'), Sym2.congr_right]
              simp only [this, Finset.sum_ite_eq', hu1, false_and, if_false, zero_add, true_and]
            · have : ∀ w, ¬ (s(u, w) = s(p', q')) := fun w h => by
                rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
                exacts [hu1 h1, hu2 h1]
              simp [this, hu1, hu2]
        rw [Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_add_distrib]
        have e1 : ∑ u ∈ K, (if u = p' ∧ q' ∈ W then 1 else 0) = if p' ∈ K ∧ q' ∉ K then 1 else 0 := by
          by_cases h : q' ∈ W
          · have : q' ∉ K := (Finset.mem_sdiff.mp h).2
            simp only [h, and_true, this, not_false_eq_true]; rw [Finset.sum_ite_eq']
          · have : ¬ (q' ∉ K) := fun h' => h (Finset.mem_sdiff.mpr ⟨hq'S, h'⟩)
            simp [h, this]
        have e2 : ∑ u ∈ K, (if u = q' ∧ p' ∈ W then 1 else 0) = if q' ∈ K ∧ p' ∉ K then 1 else 0 := by
          by_cases h : p' ∈ W
          · have : p' ∉ K := (Finset.mem_sdiff.mp h).2
            simp only [h, and_true, this, not_false_eq_true]; rw [Finset.sum_ite_eq']
          · have : ¬ (p' ∉ K) := fun h' => h (Finset.mem_sdiff.mpr ⟨hp'S, h'⟩)
            simp [h, this]
        rw [e1, e2]
        by_cases h1 : p' ∈ K <;> by_cases h2 : q' ∈ K
        · exact absurd ⟨h1, h2⟩ hnot
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [hS', Finset.sum_congr rfl fun u _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hind]
      omega
    · intro u hu w hw
      rw [y2Move_mult, if_neg]
      · split_ifs with h
        · exfalso; rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hnot ⟨by assumption, by assumption⟩
        · simpa using hm u hu w hw
      · rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
        · exact hKp u hu h.symm
        · exact hKp w hw h.symm
        · exact hKq u hu h.symm
        · exact hKq w hw h.symm
  · -- both externals in `K`: the two leaving bonds are `p–p'` and `q–q'`
    by_contra hcon
    push_neg at hcon
    have hwW : w ∈ W := by simp [hW, hS, hw, hcon.1, hcon.2.1, hcon.2.2]
    have hrest : H.mult s(u, w) ≤ ∑ u ∈ K, ∑ w ∈ W, H.mult s(u, w) := by
      have h1 := Finset.single_le_sum (f := fun w' => H.mult s(u, w')) (fun _ _ => Nat.zero_le _) hwW
      exact h1.trans (Finset.single_le_sum (f := fun u' => ∑ w' ∈ W, H.mult s(u', w'))
        (fun _ _ => Nat.zero_le _) hu)
    rw [if_pos hboth.1, if_pos hboth.2] at hcutH
    omega

/-- The path induction: two disjoint nonempty intact sets cannot both survive to a doubled triangle. -/
theorem pendant_path {H T' : UMultigraph V} {ps : List (Sym2 V)} (hp : Y2Path H ps T')
    (hT : IsDoubledTriangle T') :
    ∀ {K₁ K₂ : Finset V}, Connected H → Intact H K₁ → Intact H K₂ → Disjoint K₁ K₂ → K₁.Nonempty →
      K₂.Nonempty → False := by
  induction hp with
  | nil G =>
    intro K₁ K₂ _ h1 _ _ _ _
    exact doubledTriangle_cut_ne_two hT h1.1 h1.2.1
  | @cons H T' p q p' q' rest hP hrest ih =>
    intro K₁ K₂ hc h1 h2 hdisj hne₁ hne₂
    obtain ⟨hp1, hq1, hstay1, hclose1⟩ := intact_step h1 hP
    obtain ⟨hp2, hq2, hstay2, hclose2⟩ := intact_step h2 hP
    -- a violated set fills the graph, leaving no room for the other
    have hfill : ∀ {K L : Finset V}, Intact H K → Intact H L → Disjoint K L → L.Nonempty → p ∉ L → q ∉ L →
        (p' ∈ K ∧ q' ∈ K → ∀ u ∈ K, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ K ∨ w = p ∨ w = q) →
        p' ∈ K ∧ q' ∈ K → False := by
      intro K L hK hL hKL hLne hpL hqL hcl hboth
      set Y := insert p (insert q K) with hY
      have hYV : Y ⊆ H.verts := by
        intro x hx; simp only [hY, Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hx
        · exact hP.a_mem
        · exact hP.b_mem
        · exact hK.1 hx
      have hYc : ∀ u ∈ Y, ∀ w ∈ H.verts, H.mult s(u, w) ≠ 0 → w ∈ Y := by
        intro u hu w hw hm
        simp only [hY, Finset.mem_insert] at hu ⊢
        rcases hu with rfl | rfl | hu
        · rw [hP.mult_a] at hm
          by_cases h1 : w = q
          · exact Or.inr (Or.inl h1)
          · rw [if_neg h1] at hm
            by_cases h2 : w = p'
            · exact Or.inr (Or.inr (h2 ▸ hboth.1))
            · rw [if_neg h2] at hm; exact absurd rfl hm
        · rw [hP.mult_b] at hm
          by_cases h1 : w = p
          · exact Or.inl h1
          · rw [if_neg h1] at hm
            by_cases h2 : w = q'
            · exact Or.inr (Or.inr (h2 ▸ hboth.2))
            · rw [if_neg h2] at hm; exact absurd rfl hm
        · rcases hcl hboth u hu w hw hm with h | h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
      have hYall : Y = H.verts := eq_of_closed' hc hYV ⟨p, by simp [hY]⟩ hYc
      obtain ⟨x, hx⟩ := hLne
      have hxY : x ∈ Y := by rw [hYall]; exact hL.1 hx
      simp only [hY, Finset.mem_insert] at hxY
      rcases hxY with rfl | rfl | hxK
      · exact hpL hx
      · exact hqL hx
      · exact Finset.disjoint_left.mp hKL hxK hx
    by_cases hb1 : p' ∈ K₁ ∧ q' ∈ K₁
    · exact hfill h1 h2 hdisj hne₂ hp2 hq2 hclose1 hb1
    by_cases hb2 : p' ∈ K₂ ∧ q' ∈ K₂
    · exact hfill h2 h1 hdisj.symm hne₁ hp1 hq1 hclose2 hb2
    exact ih hT (connected_y2Move hP hc) (hstay1 hb1) (hstay2 hb2) hdisj hne₁ hne₂

/-- Sums of neighbour indicators over a set. -/
theorem sum_count_pair (K : Finset V) (n n' : V) :
    ∑ u ∈ K, ({n, n'} : Multiset V).count u = (if n ∈ K then 1 else 0) + (if n' ∈ K then 1 else 0) := by
  simp only [count_pair_v, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- Smoothing a degree-2 atom `j ∉ K` whose two neighbours lie in `K` closes `insert j K` off. -/
theorem closed_insert_of_nbrs {G : UMultigraph V} {j n n' : V} {K : Finset V} (hl : G.mult s(j, j) = 0)
    (hnb : nbrs G j = {n, n'}) (hdeg : deg G j = 2) (hjK : j ∉ K) (hKV : K ⊆ G.verts) (hn : n ∈ K)
    (hn' : n' ∈ K) (hcK : cut G K = 2) : cut G (insert j K) = 0 := by
  have hjV := mem_verts_of_nbrs hnb
  have h := cut_insert G hjK hjV hKV hl
  have hsum : ∑ u ∈ K, G.mult s(j, u) = 2 := by
    rw [Finset.sum_congr rfl fun u hu => mult_of_nbrs_eq hnb (fun h => hjK (h ▸ hu)), sum_count_pair,
      if_pos hn, if_pos hn']
  omega

/-- **N3 Lemma 6.2** (pendant poles). -/
theorem pendantPoles_holds : PendantPolesStatement.{u} := by
  intro V _ G j₁ j₂ K₁ K₂ hT hK₁ hK₂ hdisj hne₁ hne₂ hc₁ hc₂
  have hl := hT.loopless
  obtain ⟨hB, hm2, C, hC, hRT⟩ := hT
  obtain ⟨hj₁V, hj₂V, hj, hd₁, hd₂, hd, hconn⟩ := hB
  have hσ := hC.1
  obtain ⟨n1, n1', n2, n2', h1, h2, rfl⟩ := hC.eq_smooth hl hj
  have hn1V := nbrs_mem_verts h1
  have hB₁V : (smooth G j₁ n1 n1').verts = G.verts.erase j₁ := smooth_verts hn1V.1 hn1V.2
  have hl₂ := smooth_loop_j₂ hl hj hσ h1
  have hB₁c : Connected (smooth G j₁ n1 n1') := connected_smooth (hl j₁) h1 hconn
  have hCc : Connected (smooth (smooth G j₁ n1 n1') j₂ n2 n2') := connected_smooth hl₂ h2 hB₁c
  have hdeg₂ : deg (smooth G j₁ n1 n1') j₂ = 2 := by rw [deg_smooth (hl j₁) h1 (Ne.symm hj)]; exact hd₂
  have hn2V := nbrs_mem_verts h2
  have hCV : (smooth (smooth G j₁ n1 n1') j₂ n2 n2').verts = (G.verts.erase j₁).erase j₂ := by
    rw [smooth_verts hn2V.1 hn2V.2, hB₁V]
  have hint : ∀ {K : Finset V}, K ⊆ interior G j₁ j₂ → K ⊆ G.verts ∧ j₁ ∉ K ∧ j₂ ∉ K := by
    intro K hK
    refine ⟨fun x hx => ?_, fun h => ?_, fun h => ?_⟩
    · have := hK hx; simp only [interior, Finset.mem_erase] at this; exact this.2.2
    · have := hK h; simp [interior] at this
    · have := hK h; simp [interior] at this
  -- Step 1: an interior set with two leaving bonds is intact in the closure
  have step1 : ∀ K L : Finset V, K ⊆ interior G j₁ j₂ → L ⊆ interior G j₁ j₂ → Disjoint K L → L.Nonempty →
      cut G K = 2 → Intact (smooth (smooth G j₁ n1 n1') j₂ n2 n2') K := by
    intro K L hK hL hKL hLne hcK
    obtain ⟨hKV, hj₁K, hj₂K⟩ := hint hK
    have hKV₁ : K ⊆ (smooth G j₁ n1 n1').verts := by
      rw [hB₁V]; intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hj₁K (h ▸ hx), hKV hx⟩
    -- (i) not both neighbours of `j₁` in `K`
    have hi : ¬ (n1 ∈ K ∧ n1' ∈ K) := by
      rintro ⟨hn, hn'⟩
      have h0 := closed_insert_of_nbrs (hl j₁) h1 hd₁ hj₁K hKV hn hn' hcK
      have hall := eq_of_closed' hconn (S := insert j₁ K) (fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj₁V
        · exact hKV hx) ⟨j₁, Finset.mem_insert_self _ _⟩ (fun u hu w hw hm => closed_of_cut_zero G h0 u hu w hw hm)
      have : j₂ ∈ insert j₁ K := by rw [hall]; exact hj₂V
      rcases Finset.mem_insert.mp this with h | h
      · exact hj h.symm
      · exact hj₂K h
    have hcut1 : cut (smooth G j₁ n1 n1') K = 2 := by
      have := cut_smooth (hl j₁) h1 hj₁K hKV
      rw [if_neg hi] at this; omega
    -- (iii) not both neighbours of `j₂` (after smoothing `j₁`) in `K`
    have hiii : ¬ (n2 ∈ K ∧ n2' ∈ K) := by
      rintro ⟨hn, hn'⟩
      have h0 := closed_insert_of_nbrs hl₂ h2 hdeg₂ hj₂K hKV₁ hn hn' hcut1
      have hj₂V₁ : j₂ ∈ (smooth G j₁ n1 n1').verts := by rw [hB₁V]; exact Finset.mem_erase.mpr ⟨Ne.symm hj, hj₂V⟩
      have hall := eq_of_closed' hB₁c (S := insert j₂ K) (fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj₂V₁
        · exact hKV₁ hx) ⟨j₂, Finset.mem_insert_self _ _⟩
        (fun u hu w hw hm => closed_of_cut_zero _ h0 u hu w hw hm)
      obtain ⟨x, hx⟩ := hLne
      obtain ⟨hLV, hj₁L, hj₂L⟩ := hint hL
      have hxB : x ∈ insert j₂ K := by
        rw [hall, hB₁V]; exact Finset.mem_erase.mpr ⟨fun h => hj₁L (h ▸ hx), hLV hx⟩
      rcases Finset.mem_insert.mp hxB with h | h
      · exact hj₂L (h ▸ hx)
      · exact Finset.disjoint_left.mp hKL h hx
    refine ⟨?_, ?_, ?_⟩
    · rw [hCV]; intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hj₂K (h ▸ hx), Finset.mem_erase.mpr ⟨fun h => hj₁K (h ▸ hx), hKV hx⟩⟩
    · have := cut_smooth hl₂ h2 hj₂K hKV₁
      rw [if_neg hiii] at this; omega
    · intro u hu w hw
      have huj₁ : u ≠ j₁ := fun h => hj₁K (h ▸ hu)
      have huj₂ : u ≠ j₂ := fun h => hj₂K (h ▸ hu)
      have hwj₁ : w ≠ j₁ := fun h => hj₁K (h ▸ hw)
      have hwj₂ : w ≠ j₂ := fun h => hj₂K (h ▸ hw)
      rw [smooth_mult_at _ huj₂, if_neg hwj₂, smooth_mult_at _ huj₁, if_neg hwj₁]
      have e1 : ¬ (s(u, w) = s(n1, n1')) := by
        intro h; apply hi
        rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨h3 ▸ hu, h4 ▸ hw⟩
        · exact ⟨h4 ▸ hw, h3 ▸ hu⟩
      have e2 : ¬ (s(u, w) = s(n2, n2')) := by
        intro h; apply hiii
        rcases Sym2.eq_iff.mp h with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨h3 ▸ hu, h4 ▸ hw⟩
        · exact ⟨h4 ▸ hw, h3 ▸ hu⟩
      rw [if_neg e1, if_neg e2, add_zero, add_zero]
      by_cases huw : u = w
      · subst huw; rw [hl u]; omega
      · exact hm2 u (hKV hu) w (hKV hw) huw
  obtain ⟨ps, T', hp, hT'⟩ := reducesToT_iff.mp hRT
  exact pendant_path hp hT' hCc (step1 K₁ K₂ hK₁ hK₂ hdisj hne₂ hc₁) (step1 K₂ K₁ hK₂ hK₁ hdisj.symm hne₁ hc₂)
    hdisj hne₁ hne₂

end WaveTurbulence.TVine.Core
