/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Chain

/-!
# N2 Lemma 1.14(c′), chain level (N3 §2.1 (i))

In the core `H` of a vine-like sub-object (a block with joints `k₁, k₂`, chain of ingredients from `k₁`):
* `ChainU.prefix_closed`: the atoms of a prefix chain other than its end keep all their bonds inside it;
* `ChainU.junction_ne_a`: no junction is an atom of the rung (parity across the poles);
* `chain_rungDel`: the rung lies inside exactly one ingredient, and deleting it replaces that ingredient by its
  deletion (given the ingredient result `IngredientDel`), all other ingredients unchanged.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- A cut with a single leaving bond. -/
theorem cut_eq_one_of_unique (H : UMultigraph V) {Z : Finset V} {z₀ w₀ : V} (hz₀ : z₀ ∈ Z)
    (hw₀ : w₀ ∈ H.verts \ Z) (h1 : H.mult s(z₀, w₀) = 1)
    (honly : ∀ z ∈ Z, ∀ w ∈ H.verts \ Z, H.mult s(z, w) ≠ 0 → z = z₀ ∧ w = w₀) : cut H Z = 1 := by
  unfold cut
  rw [Finset.sum_eq_single z₀]
  · rw [Finset.sum_eq_single w₀]
    · exact h1
    · intro w hw hne; by_contra h; exact hne (honly z₀ hz₀ w hw h).2
    · intro h; exact absurd hw₀ h
  · intro z hz hne
    apply Finset.sum_eq_zero; intro w hw; by_contra h; exact hne (honly z hz w hw h).1
  · intro h; exact absurd hz₀ h

section

variable {H : UMultigraph V} {k₁ k₂ : V}

/-- In a block, the atoms of a prefix chain from `k₁`, other than its end, keep all their bonds inside it. -/
theorem ChainU.prefix_closed (hl : H.Loopless) (hB : IsBlockU H k₁ k₂) {S : Finset V} {c : V}
    {ks : List EnlKind} (h : ChainU H S k₁ c ks) :
    ∀ v ∈ S, v ≠ c → ∀ w ∈ H.verts, H.mult s(v, w) ≠ 0 → w ∈ S := by
  intro v hv hvc
  have hSV := h.subset
  obtain ⟨hdk, -, hdv⟩ := h.deg_ge hl
  apply closed_of_deg_eq H hSV hv
  have hle := deg_induce_le H hSV hv
  by_cases hvk : v = k₁
  · subst hvk; rw [hB.2.2.2.1] at hle ⊢; omega
  · have h4 := hdv v hv hvk hvc
    have hG : deg H v ≤ 4 := by
      by_cases h2 : v = k₂
      · rw [h2, hB.2.2.2.2.1]; omega
      · rw [hB.2.2.2.2.2.1 v (hSV hv) hvk h2]
    omega

variable {ra rb xm xp ym yp : V} {Km Kp : Finset V}

/-- No junction of a chain (in the core of a block) is an atom `ra` of a rung. -/
theorem ChainU.junction_ne_a (hl : H.Loopless) (hB : IsBlockU H k₁ k₂) (hR : RungCore H ra rb xm xp ym yp Km Kp)
    {S T : Finset V} {b c : V} {ks : List EnlKind} {k : EnlKind} (hch : ChainU H S k₁ b ks)
    (hv : IsVineKindU k (induce H T) b c) (hST : S ∩ T = {b}) : b ≠ ra := by
  intro hb
  subst hb
  have hcl := hch.prefix_closed hl hB
  have hSV := hch.subset
  have hbS : b ∈ S := hch.ends_mem.2
  have hbT : b ∈ T := hv.isBlockU.1
  obtain ⟨hxmV, hxma, hxmb⟩ := hR.mem_verts (Or.inl hR.xm_mem)
  have hrbK : ∀ x, x ∈ Km ∨ x ∈ Kp → x ≠ rb := fun x hx => (hR.ne_of_mem hx).2
  have hbK : ∀ x, x ∈ Km ∨ x ∈ Kp → x ≠ b := fun x hx => (hR.ne_of_mem hx).1
  have hxpm : xp ≠ xm := fun h => hR.not_mem_both hR.xm_mem (h ▸ hR.xp_mem)
  -- the bonds of `b`
  have hsum : ∀ X : Finset V, rb ∉ X →
      ∑ w ∈ X, H.mult s(b, w) = (if xm ∈ X then 1 else 0) + (if xp ∈ X then 1 else 0) := by
    intro X hrbX
    rw [hR.sum_mult_a X, if_neg hrbX]; ring
  have hdegX : ∀ X : Finset V, b ∈ X → deg (induce H X) b = ∑ w ∈ X, H.mult s(b, w) := by
    intro X hbX
    unfold deg
    rw [show (induce H X).verts = X from rfl, induce_mult_of_mem H hbX hbX, hl b, add_zero]
    exact Finset.sum_congr rfl fun w hw => induce_mult_of_mem H hbX hw
  have hev := fun (Z : Finset V) (hZ : Z ⊆ H.verts) => hB.even_cut hZ
  have h1 : H.mult s(xm, b) = 1 := by
    rw [Sym2.eq_swap, hR.mult_a, if_neg (hrbK xm (Or.inl hR.xm_mem)), if_pos (Or.inl rfl)]
  by_cases hrbS : rb ∈ S
  · -- the rails carry the two bonds of `b` into `T`
    have hrbT : rb ∉ T := by
      intro h
      have : rb ∈ S ∩ T := Finset.mem_inter.mpr ⟨hrbS, h⟩
      rw [hST] at this; exact hR.ne (Finset.mem_singleton.mp this).symm
    have hdT := hv.isBlockU.2.2.2.1
    rw [hdegX T hbT, hsum T hrbT] at hdT
    have hxmT : xm ∈ T := by by_contra h; rw [if_neg h] at hdT; split_ifs at hdT <;> omega
    have hxmS : xm ∉ S := by
      intro h
      have : xm ∈ S ∩ T := Finset.mem_inter.mpr ⟨h, hxmT⟩
      rw [hST] at this; exact hxma (Finset.mem_singleton.mp this)
    set Z := (H.verts \ S).filter (· ∈ Km) with hZ
    have hZV : Z ⊆ H.verts := fun z hz => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
    have hZ1 : cut H Z = 1 := by
      refine cut_eq_one_of_unique H (z₀ := xm) (w₀ := b)
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxmV, hxmS⟩, hR.xm_mem⟩)
        (Finset.mem_sdiff.mpr ⟨hR.a_verts, fun h => hbK b (Or.inl (Finset.mem_filter.mp h).2) rfl⟩) h1 ?_
      intro z hz w hw hm
      obtain ⟨hzVS, hzK⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzV, hzS⟩ := Finset.mem_sdiff.mp hzVS
      obtain ⟨hwV, hwZ⟩ := Finset.mem_sdiff.mp hw
      by_cases hwS : w ∈ S
      · by_cases hwb : w = b
        · rw [hwb] at hm ⊢
          refine ⟨?_, rfl⟩
          rw [Sym2.eq_swap, hR.mult_a] at hm
          by_contra hzx
          have hzrb : z ≠ rb := fun h => hzS (by rw [h]; exact hrbS)
          have hzxp : z ≠ xp := fun h => hR.not_mem_both hzK (by rw [h]; exact hR.xp_mem)
          have hor : ¬ (z = xm ∨ z = xp) := by rintro (h | h); exacts [hzx h, hzxp h]
          rw [if_neg hzrb, if_neg hor] at hm
          exact hm rfl
        · exact absurd (hcl w hwS hwb z hzV (by rw [Sym2.eq_swap]; exact hm)) hzS
      · exfalso
        have hwK : w ∉ Km := fun h => hwZ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwV, hwS⟩, h⟩)
        by_cases hwb : w = b
        · exact hwS (by rw [hwb]; exact hbS)
        by_cases hwrb : w = rb
        · exact hwS (by rw [hwrb]; exact hrbS)
        rcases hR.mem_poles hwV hwb hwrb with h | h
        · exact hwK h
        · exact hm (hR.noBond z hzK w h)
    have := hev Z hZV
    rw [hZ1] at this
    exact absurd this (by decide)
  · -- the rails carry the two bonds of `b` into the prefix
    have hdS := (hch.deg_ge hl).2.1
    rw [hdegX S hbS, hsum S hrbS] at hdS
    have hxmS : xm ∈ S := by by_contra h; rw [if_neg h] at hdS; split_ifs at hdS <;> omega
    set Z := (S.erase b).filter (· ∈ Km) with hZ
    have hZV : Z ⊆ H.verts := fun z hz => hSV (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
    have hZ1 : cut H Z = 1 := by
      refine cut_eq_one_of_unique H (z₀ := xm) (w₀ := b)
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxma, hxmS⟩, hR.xm_mem⟩)
        (Finset.mem_sdiff.mpr ⟨hR.a_verts, fun h => hbK b (Or.inl (Finset.mem_filter.mp h).2) rfl⟩) h1 ?_
      intro z hz w hw hm
      obtain ⟨hzSb, hzK⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzb, hzS⟩ := Finset.mem_erase.mp hzSb
      obtain ⟨hwV, hwZ⟩ := Finset.mem_sdiff.mp hw
      have hwS := hcl z hzS hzb w hwV hm
      by_cases hwb : w = b
      · rw [hwb] at hm ⊢
        refine ⟨?_, rfl⟩
        rw [Sym2.eq_swap, hR.mult_a] at hm
        by_contra hzx
        have hzrb : z ≠ rb := fun h => hrbS (by rw [← h]; exact hzS)
        have hzxp : z ≠ xp := fun h => hR.not_mem_both hzK (by rw [h]; exact hR.xp_mem)
        have hor : ¬ (z = xm ∨ z = xp) := by rintro (h | h); exacts [hzx h, hzxp h]
        rw [if_neg hzrb, if_neg hor] at hm
        exact hm rfl
      · exfalso
        have hwK : w ∉ Km := fun h => hwZ (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwb, hwS⟩, h⟩)
        by_cases hwrb : w = rb
        · exact hrbS (by rw [← hwrb]; exact hwS)
        rcases hR.mem_poles hwV hwb hwrb with h | h
        · exact hwK h
        · exact hm (hR.noBond z hzK w h)
    have := hev Z hZV
    rw [hZ1] at this
    exact absurd this (by decide)

end

end WaveTurbulence.TVine.Core
