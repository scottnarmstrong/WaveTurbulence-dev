/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Induced

/-!
# N2 Lemma 1.11: joints in rungs

`jointsInRungs_holds : JointsInRungsStatement`. If a sub-object `U` of a block has a joint in a 2-cut rung
`R = {a, b}`, then `U` is the double bond `a = b`, or the side hyper-block `K ∪ R` (adjoint `a = b`) for a side `K`
of `R` without joints of the block.

Proof (N2 Lemma 1.11): count the bonds of `U` at `a` and `b`; parity (N2 Lemma 1.10 / even cuts of blocks) across the
2-edge-cuts `δ(Km)`, `δ(Kp)`; closedness inside the connected core of `U` and the connected poles.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section Sums

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem ind_sum_eq (T : Finset V) (x : V) : ∑ w ∈ T, (if w = x then 1 else 0) = if x ∈ T then 1 else 0 :=
  Finset.sum_ite_eq' T x (fun _ => 1)

/-- The bonds of `a` into a set `T`. -/
theorem RungCore.sum_mult_a (hR : RungCore G a b xm xp ym yp Km Kp) (T : Finset V) :
    ∑ w ∈ T, G.mult s(a, w) =
      2 * (if b ∈ T then 1 else 0) + (if xm ∈ T then 1 else 0) + (if xp ∈ T then 1 else 0) := by
  have hxb : xm ≠ b := (hR.ne_of_mem (Or.inl hR.xm_mem)).2
  have hpb : xp ≠ b := (hR.ne_of_mem (Or.inr hR.xp_mem)).2
  have hxx := hR.xm_ne_xp
  have h : ∀ w, G.mult s(a, w) = 2 * (if w = b then 1 else 0) + (if w = xm then 1 else 0) +
      (if w = xp then 1 else 0) := by
    intro w
    rw [hR.mult_a]
    by_cases h1 : w = b
    · subst h1; simp [Ne.symm hxb, Ne.symm hpb]
    · by_cases h2 : w = xm
      · subst h2; simp [h1, hxx]
      · by_cases h3 : w = xp
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, ind_sum_eq]

theorem RungCore.sum_mult_b (hR : RungCore G a b xm xp ym yp Km Kp) (T : Finset V) :
    ∑ w ∈ T, G.mult s(b, w) =
      2 * (if a ∈ T then 1 else 0) + (if ym ∈ T then 1 else 0) + (if yp ∈ T then 1 else 0) :=
  hR.swapAB.sum_mult_a T

/-- The bonds of `E(S)` leaving `Km ∩ S`: the rails `a–xm` and `b–ym` when present. -/
theorem RungCore.cut_induce_Km (hR : RungCore G a b xm xp ym yp Km Kp) {S : Finset V} (hS : S ⊆ G.verts) :
    cut (induce G S) (Km ∩ S) =
      (if a ∈ S ∧ xm ∈ S then 1 else 0) + (if b ∈ S ∧ ym ∈ S then 1 else 0) := by
  have hrow : ∀ u ∈ Km ∩ S, ∑ w ∈ S \ (Km ∩ S), (induce G S).mult s(u, w) =
      (if a ∈ S ∧ u = xm then 1 else 0) + (if b ∈ S ∧ u = ym then 1 else 0) := by
    intro u hu
    obtain ⟨huK, huS⟩ := Finset.mem_inter.mp hu
    have hua := (hR.ne_of_mem (Or.inl huK)).1
    have hub := (hR.ne_of_mem (Or.inl huK)).2
    have hux : u ≠ xp := fun h => hR.not_mem_both huK (h ▸ hR.xp_mem)
    have huy : u ≠ yp := fun h => hR.not_mem_both huK (h ▸ hR.yp_mem)
    have hval : ∀ w ∈ S \ (Km ∩ S), (induce G S).mult s(u, w) =
        (if w = a then (if u = xm then 1 else 0) else 0) + (if w = b then (if u = ym then 1 else 0) else 0) := by
      intro w hw
      obtain ⟨hwS, hwK⟩ := Finset.mem_sdiff.mp hw
      have hwK' : w ∉ Km := fun h => hwK (Finset.mem_inter.mpr ⟨h, hwS⟩)
      rw [induce_mult_of_mem G huS hwS]
      by_cases hwa : w = a
      · subst hwa; rw [Sym2.eq_swap, hR.mult_a]; simp [hub, hux, hR.ne]
      · by_cases hwb : w = b
        · subst hwb; rw [Sym2.eq_swap, hR.mult_b]; simp [hua, huy, hwa]
        · rcases hR.mem_poles (hS hwS) hwa hwb with h | h
          · exact absurd h hwK'
          · rw [hR.noBond u huK w h]; simp [hwa, hwb]
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have haK : a ∉ Km := fun h => (hR.ne_of_mem (Or.inl h)).1 rfl
    have hbK : b ∉ Km := fun h => (hR.ne_of_mem (Or.inl h)).2 rfl
    simp only [Finset.mem_sdiff, Finset.mem_inter, haK, hbK, false_and, not_false_eq_true, and_true]
    by_cases h1 : a ∈ S <;> by_cases h2 : b ∈ S <;> simp [h1, h2]
  rw [cut, show (induce G S).verts = S from rfl, Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  have e1 : ∑ u ∈ Km ∩ S, (if a ∈ S ∧ u = xm then 1 else 0) = if a ∈ S ∧ xm ∈ S then 1 else 0 := by
    by_cases ha : a ∈ S
    · simp only [ha, true_and]
      rw [Finset.sum_ite_eq']
      simp [hR.xm_mem]
    · simp [ha]
  have e2 : ∑ u ∈ Km ∩ S, (if b ∈ S ∧ u = ym then 1 else 0) = if b ∈ S ∧ ym ∈ S then 1 else 0 := by
    by_cases hb : b ∈ S
    · simp only [hb, true_and]
      rw [Finset.sum_ite_eq']
      simp [hR.ym_mem]
    · simp [hb]
  rw [e1, e2]

end Sums

section Main

variable {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V} {U : SubObj V}

theorem ite_one_le (p : Prop) [Decidable p] : (if p then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega

/-- `deg` in `E(S)` at the rung atom `a ∈ S`. -/
theorem RungCore.deg_induce_a (hR : RungCore G a b xm xp ym yp Km Kp) (hl : G.Loopless) {S : Finset V}
    (haS : a ∈ S) :
    deg (induce G S) a = 2 * (if b ∈ S then 1 else 0) + (if xm ∈ S then 1 else 0) + (if xp ∈ S then 1 else 0) := by
  unfold deg
  rw [show (induce G S).verts = S from rfl, induce_mult_of_mem G haS haS, hl a, add_zero,
    Finset.sum_congr rfl fun w hw => induce_mult_of_mem G haS hw, hR.sum_mult_a]

/-- A non-joint atom of a sub-object has all its bonds inside, and `G`-degree `4`. -/
theorem interior_closed (hB : IsBlockU G j₁ j₂) {S : Finset V} (hS : S ⊆ G.verts) {u : V} (huS : u ∈ S)
    (hdeg : deg (induce G S) u = 4) : u ≠ j₁ ∧ u ≠ j₂ ∧ ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ S := by
  have hadd := deg_induce_add G hS huS
  have hle : deg G u ≤ 4 := by
    by_cases h1 : u = j₁
    · rw [h1, hB.2.2.2.1]; omega
    by_cases h2 : u = j₂
    · rw [h2, hB.2.2.2.2.1]; omega
    rw [hB.2.2.2.2.2.1 u (hS huS) h1 h2]
  have hzero : ∑ w ∈ G.verts \ S, G.mult s(u, w) = 0 := by omega
  refine ⟨fun h => ?_, fun h => ?_, fun w hw hm => ?_⟩
  · subst h; have := hB.2.2.2.1; omega
  · subst h; have := hB.2.2.2.2.1; omega
  · by_contra hwS
    have := (Finset.sum_eq_zero_iff.mp hzero) w (Finset.mem_sdiff.mpr ⟨hw, hwS⟩)
    exact hm this

/-- The hyper case with `xm ∈ S`, `xp ∉ S`: `U` is the side hyper-block over `Km`. -/
private theorem jir_hyper (hB : IsBlockU G j₁ j₂) (hl : G.Loopless) (hR : IsRungAt G a b xm xp ym yp Km Kp)
    (hU : IsSubObjU G U) (hk : U.k₁ = a) (hh : U.hyper = true) (hbS : b ∈ U.atoms) (hxm : xm ∈ U.atoms)
    (hxp : xp ∉ U.atoms) :
    s(U.k₁, U.k₂) = s(a, b) ∧ U.atoms = insert a (insert b Km) ∧ j₁ ∉ Km ∧ j₂ ∉ Km := by
  have hRc := hR.toCore
  have hU' := hU
  obtain ⟨hsub, hadj, hcore⟩ := hU
  set S := U.atoms with hSdef
  have hSV : S ⊆ G.verts := hsub.subset
  have hcoreEq : U.core G = eraseBond (induce G S) s(U.k₁, U.k₂) := by simp [SubObj.core, hh, SubObj.edges, hSdef]
  rw [hcoreEq] at hcore
  obtain ⟨hk₁S, hk₂S, hkk, hd₁, hd₂, hd, hconn⟩ := hcore
  have hk₁S' : U.k₁ ∈ S := hk₁S
  have hk₂S' : U.k₂ ∈ S := hk₂S
  have haS : a ∈ S := hk ▸ hk₁S'
  have hmG : G.mult s(U.k₁, U.k₂) ≠ 0 := hadj hh
  have hmH : (induce G S).mult s(U.k₁, U.k₂) ≠ 0 := by rw [induce_mult_of_mem G hk₁S' hk₂S']; exact hmG
  have hdE := deg_eraseBond (induce G S) hkk hk₁S hk₂S hmH
  have hyp : yp ∉ S := by
    have hpar := (parity_holds G U Kp hU').2 hh
    have hcut := hRc.swapPoles.cut_induce_Km hSV
    have haKp : U.k₁ ∉ Kp := by rw [hk]; exact fun h => (hRc.ne_of_mem (Or.inr h)).1 rfl
    have hk₂Kp : U.k₂ ∉ Kp := by
      have hmem : U.k₂ = b ∨ U.k₂ = xm := by
        have h := hRc.mult_a U.k₂
        rw [← hk] at h
        rw [h] at hmG
        by_cases h1 : U.k₂ = b
        · exact Or.inl h1
        · rw [if_neg h1] at hmG
          by_cases h2 : U.k₂ = xm ∨ U.k₂ = xp
          · rcases h2 with h2 | h2
            · exact Or.inr h2
            · exact absurd (h2 ▸ hk₂S') hxp
          · rw [if_neg h2] at hmG; exact absurd rfl hmG
      rcases hmem with h | h <;> rw [h]
      · exact fun h' => (hRc.ne_of_mem (Or.inr h')).2 rfl
      · exact fun h' => hRc.not_mem_both hRc.xm_mem h'
    have hnotodd : ¬ Odd (cut (U.edges G) (Kp ∩ U.atoms)) := by
      rw [hpar]; tauto
    intro hyS
    apply hnotodd
    show Odd (cut (induce G S) (Kp ∩ S))
    rw [hcut, if_neg (fun h => hxp h.2), if_pos ⟨hbS, hyS⟩]
    exact odd_one
  -- `S` avoids `Kp`
  have hSKp : ∀ u ∈ S, u ∉ Kp := by
    have hT := eq_of_closed' (K := S) (S := S.filter fun u => u ∉ Kp) hconn (Finset.filter_subset _ _)
      ⟨a, Finset.mem_filter.mpr ⟨haS, fun h => (hRc.ne_of_mem (Or.inr h)).1 rfl⟩⟩ (by
        intro u hu w hwS hm
        obtain ⟨huS, huKp⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_filter.mpr ⟨hwS, fun hwK => ?_⟩
        have hmG' : G.mult s(u, w) ≠ 0 := by
          intro h0; apply hm
          show (if s(u, w) = s(U.k₁, U.k₂) then (induce G S).mult s(u, w) - 1 else (induce G S).mult s(u, w)) = 0
          rw [induce_mult_of_mem G huS hwS, h0]; split_ifs <;> rfl
        by_cases hua : u = a
        · subst hua
          have h := hRc.mult_a w
          rw [h] at hmG'
          have hwb : w ≠ b := fun h => (hRc.ne_of_mem (Or.inr (h ▸ hwK))).2 rfl
          have hwm : w ≠ xm := fun h => hRc.not_mem_both hRc.xm_mem (h ▸ hwK)
          rw [if_neg hwb] at hmG'
          by_cases h2 : w = xm ∨ w = xp
          · rcases h2 with h2 | h2
            · exact hwm h2
            · exact hxp (h2 ▸ hwS)
          · rw [if_neg h2] at hmG'; exact hmG' rfl
        by_cases hub : u = b
        · subst hub
          have h := hRc.mult_b w
          rw [h] at hmG'
          have hwa : w ≠ a := fun h => (hRc.ne_of_mem (Or.inr (h ▸ hwK))).1 rfl
          have hwm : w ≠ ym := fun h => hRc.not_mem_both hRc.ym_mem (h ▸ hwK)
          rw [if_neg hwa] at hmG'
          by_cases h2 : w = ym ∨ w = yp
          · rcases h2 with h2 | h2
            · exact hwm h2
            · exact hyp (h2 ▸ hwS)
          · rw [if_neg h2] at hmG'; exact hmG' rfl
        rcases hRc.mem_poles (hSV huS) hua hub with huK | huK
        · exact hmG' (hRc.noBond u huK w hwK)
        · exact huKp huK)
    intro u hu
    have : u ∈ S.filter fun u => u ∉ Kp := by rw [hT]; exact hu
    exact (Finset.mem_filter.mp this).2
  -- the second joint is `b`
  have hdegHb : deg (induce G S) b = 2 + (if ym ∈ S then 1 else 0) + (if yp ∈ S then 1 else 0) := by
    rw [hRc.swapAB.deg_induce_a hl hbS, if_pos haS]
  have hk₂b : U.k₂ = b := by
    by_contra hne
    have hba : b ≠ U.k₁ := by rw [hk]; exact hRc.ne.symm
    have h4 := hd b hbS hba (Ne.symm hne)
    have := hdE b
    rw [if_neg (by rintro (h | h); exacts [hba h, hne h.symm]), h4, add_zero, hdegHb, if_neg hyp] at this
    have := ite_one_le (ym ∈ S)
    omega
  have hymS : ym ∈ S := by
    have := hdE b
    rw [if_pos (Or.inr hk₂b.symm), ← hk₂b, hd₂, hk₂b, hdegHb, if_neg hyp] at this
    by_contra h; rw [if_neg h] at this; omega
  -- interior atoms of `U` in `Km` have all their bonds in `S`
  have hint : ∀ u ∈ S, u ∈ Km → u ≠ j₁ ∧ u ≠ j₂ ∧ ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ S := by
    intro u huS huK
    have hua : u ≠ U.k₁ := by rw [hk]; exact (hRc.ne_of_mem (Or.inl huK)).1
    have hub : u ≠ U.k₂ := by rw [hk₂b]; exact (hRc.ne_of_mem (Or.inl huK)).2
    have h4 := hd u huS hua hub
    have := hdE u
    rw [if_neg (by rintro (h | h); exacts [hua h, hub h]), h4, add_zero] at this
    exact interior_closed hB hSV huS this.symm
  have hKmS : Km ⊆ S := by
    have hT := eq_of_closed' (K := Km) (S := Km.filter fun u => u ∈ S) hR.connm (Finset.filter_subset _ _)
      ⟨xm, Finset.mem_filter.mpr ⟨hRc.xm_mem, hxm⟩⟩ (by
        intro u hu w hwK hm
        obtain ⟨huK, huS⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨hwK, (hint u huS huK).2.2 w (hRc.mem_verts (Or.inl hwK)).1 hm⟩)
    intro u hu
    have : u ∈ Km.filter fun u => u ∈ S := by rw [hT]; exact hu
    exact (Finset.mem_filter.mp this).2
  refine ⟨by rw [hk, hk₂b], ?_, fun h => (hint j₁ (hKmS h) h).1 rfl, fun h => (hint j₂ (hKmS h) h).2.1 rfl⟩
  ext u
  simp only [Finset.mem_insert]
  constructor
  · intro huS
    by_cases hua : u = a
    · exact Or.inl hua
    by_cases hub : u = b
    · exact Or.inr (Or.inl hub)
    rcases hRc.mem_poles (hSV huS) hua hub with h | h
    · exact Or.inr (Or.inr h)
    · exact absurd h (hSKp u huS)
  · rintro (rfl | rfl | h)
    · exact haS
    · exact hbS
    · exact hKmS h

/-- The core case: the joint `k₁` of `U` is `a`. -/
private theorem jir_core (hB : IsBlockU G j₁ j₂) (hl : G.Loopless) (hR : IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp)
    (hU : IsSubObjU G U) (hk : U.k₁ = a) :
    s(U.k₁, U.k₂) = s(a, b) ∧
      ((U.hyper = false ∧ U.atoms = {a, b}) ∨
       (U.hyper = true ∧ ((U.atoms = insert a (insert b Km) ∧ j₁ ∉ Km ∧ j₂ ∉ Km) ∨
                          (U.atoms = insert a (insert b Kp) ∧ j₁ ∉ Kp ∧ j₂ ∉ Kp)))) := by
  obtain ⟨hR', -, -, -, -⟩ := hR
  have hRc := hR'.toCore
  have hU' := hU
  obtain ⟨hsub, hadj, hcore⟩ := hU
  set S := U.atoms with hSdef
  have hSV : S ⊆ G.verts := hsub.subset
  cases hh : U.hyper
  · -- block type
    have hcoreEq : U.core G = induce G S := by simp [SubObj.core, hh, SubObj.edges, hSdef]
    rw [hcoreEq] at hcore
    have hk₁S : U.k₁ ∈ S := hcore.1
    have haS : a ∈ S := hk ▸ hk₁S
    have hda := hRc.deg_induce_a hl haS
    rw [← hk, hcore.2.2.2.1] at hda
    have hcut := hRc.cut_induce_Km hSV
    have hev := hcore.even_cut (Y := Km ∩ S) (fun x hx => (Finset.mem_inter.mp hx).2)
    by_cases hbS : b ∈ S
    · have hxm : xm ∉ S := by intro h; rw [if_pos hbS, if_pos h] at hda; have := ite_one_le (xp ∈ S); omega
      have hxp : xp ∉ S := by intro h; rw [if_pos hbS, if_pos h] at hda; have := ite_one_le (xm ∈ S); omega
      have hdb := hRc.swapAB.deg_induce_a hl hbS
      rw [if_pos haS] at hdb
      by_cases hbk : U.k₂ = b
      · rw [← hbk, hcore.2.2.2.2.1] at hdb
        have hym : ym ∉ S := by intro h; rw [if_pos h] at hdb; omega
        have hyp : yp ∉ S := by intro h; rw [if_pos h] at hdb; have := ite_one_le (ym ∈ S); omega
        refine ⟨by rw [hk, hbk], Or.inl ⟨rfl, ?_⟩⟩
        refine (eq_of_closed' hcore.2.2.2.2.2.2 (S := {a, b}) ?_ ⟨a, by simp⟩ ?_).symm
        · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · intro u hu w hwS hm
          have huS : u ∈ S := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> assumption
          rw [induce_mult_of_mem G huS hwS] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl
          · rw [hRc.mult_a] at hm
            by_cases h1 : w = b
            · exact Or.inr h1
            · rw [if_neg h1] at hm
              by_cases h2 : w = xm ∨ w = xp
              · rcases h2 with rfl | rfl <;> contradiction
              · rw [if_neg h2] at hm; exact absurd rfl hm
          · rw [hRc.mult_b] at hm
            by_cases h1 : w = a
            · exact Or.inl h1
            · rw [if_neg h1] at hm
              by_cases h2 : w = ym ∨ w = yp
              · rcases h2 with rfl | rfl <;> contradiction
              · rw [if_neg h2] at hm; exact absurd rfl hm
      · have hba : b ≠ U.k₁ := by rw [hk]; exact hRc.ne.symm
        rw [hcore.2.2.2.2.2.1 b hbS hba (Ne.symm hbk)] at hdb
        have hym : ym ∈ S := by by_contra h; rw [if_neg h] at hdb; have := ite_one_le (yp ∈ S); omega
        rw [hcut, if_neg (fun h => hxm h.2), if_pos ⟨hbS, hym⟩] at hev
        exact absurd hev (by decide)
    · have hxm : xm ∈ S := by
        by_contra h; rw [if_neg hbS, if_neg h] at hda; have := ite_one_le (xp ∈ S); omega
      rw [hcut, if_pos ⟨haS, hxm⟩, if_neg (fun h => hbS h.1)] at hev
      exact absurd hev (by decide)
  · -- hyper type
    have hcoreEq : U.core G = eraseBond (induce G S) s(U.k₁, U.k₂) := by
      simp [SubObj.core, hh, SubObj.edges, hSdef]
    have hcore' := hcore
    rw [hcoreEq] at hcore'
    have hk₁S : U.k₁ ∈ S := hcore'.1
    have hk₂S : U.k₂ ∈ S := hcore'.2.1
    have haS : a ∈ S := hk ▸ hk₁S
    have hmH : (induce G S).mult s(U.k₁, U.k₂) ≠ 0 := by
      rw [induce_mult_of_mem G hk₁S hk₂S]; exact hadj hh
    have hdE := deg_eraseBond (induce G S) hcore'.2.2.1 hk₁S hk₂S hmH U.k₁
    rw [if_pos (Or.inl rfl), hcore'.2.2.2.1, hk, hRc.deg_induce_a hl haS] at hdE
    have hbS : b ∈ S := by
      by_contra h; rw [if_neg h] at hdE
      have := ite_one_le (xm ∈ S); have := ite_one_le (xp ∈ S); omega
    rw [if_pos hbS] at hdE
    by_cases hxm : xm ∈ S
    · have hxp : xp ∉ S := by intro h; rw [if_pos hxm, if_pos h] at hdE; omega
      obtain ⟨h1, h2, h3, h4⟩ := jir_hyper hB hl hR' hU' hk hh hbS hxm hxp
      exact ⟨h1, Or.inr ⟨rfl, Or.inl ⟨h2, h3, h4⟩⟩⟩
    · have hxp : xp ∈ S := by by_contra h; rw [if_neg hxm, if_neg h] at hdE; omega
      obtain ⟨h1, h2, h3, h4⟩ := jir_hyper hB hl hR'.swapPoles hU' hk hh hbS hxp hxm
      exact ⟨h1, Or.inr ⟨rfl, Or.inr ⟨h2, h3, h4⟩⟩⟩

/-- **N2 Lemma 1.11** (joints in rungs). -/
theorem jointsInRungs_holds : JointsInRungsStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hR hU hj
  have hpair : ({b, a} : Finset V) = {a, b} := Finset.pair_comm b a
  have hins : ∀ K : Finset V, insert b (insert a K) = insert a (insert b K) := fun K => Finset.insert_comm b a K
  have hsab : s(b, a) = s(a, b) := Sym2.eq_swap
  rcases hj with h | h | h | h
  · exact jir_core hB hl hR hU h
  · have := jir_core hB hl hR.swapAB hU h
    rwa [hsab, hpair, hins, hins] at this
  · have := jir_core hB hl hR hU.swap h
    simp only [SubObj.swap] at this
    rwa [Sym2.eq_swap] at this
  · have := jir_core hB hl hR.swapAB hU.swap h
    simp only [SubObj.swap] at this
    rwa [Sym2.eq_swap, hsab, hpair, hins, hins] at this

end Main

end WaveTurbulence.TVine.Core
