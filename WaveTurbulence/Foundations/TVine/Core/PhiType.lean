/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiSub

/-!
# Toward N2 Lemma 1.14(c′): rungs inside a block

* `RungCore.cut_of_closedIn`: a set inside a pole, closed within the pole, has exactly the rails it contains as
  leaving bonds;
* `IsBlockU.isRungAt_of_rungCore`: in a block, rung data has connected poles (parity), i.e. it is a 2-cut rung;
* `isTVineU_rungDel_of_noncap`: a non-cap rung of a T-vine (given by rung data) can be deleted.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section

variable {X : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

/-- A subset of `Km`, closed within `Km`, has exactly the rails it contains as leaving bonds. -/
theorem RungCore.cut_of_closedIn (hR : RungCore X a b xm xp ym yp Km Kp) {Z : Finset V} (hZ : Z ⊆ Km)
    (hcl : ∀ u ∈ Z, ∀ w ∈ Km, X.mult s(u, w) ≠ 0 → w ∈ Z) :
    cut X Z = (if xm ∈ Z then 1 else 0) + (if ym ∈ Z then 1 else 0) := by
  have hrow : ∀ z ∈ Z, ∑ w ∈ X.verts \ Z, X.mult s(z, w) = (if z = xm then 1 else 0) + (if z = ym then 1 else 0) := by
    intro z hz
    have hzK := hZ hz
    obtain ⟨hzV, hza, hzb⟩ := hR.mem_verts (Or.inl hzK)
    have haS : a ∈ X.verts \ Z := Finset.mem_sdiff.mpr ⟨hR.a_verts, fun h => (hR.ne_of_mem (Or.inl (hZ h))).1 rfl⟩
    have hbS : b ∈ (X.verts \ Z).erase a :=
      Finset.mem_erase.mpr ⟨hR.ne.symm, Finset.mem_sdiff.mpr ⟨hR.b_verts, fun h => (hR.ne_of_mem (Or.inl (hZ h))).2 rfl⟩⟩
    have hzero : ∀ w ∈ ((X.verts \ Z).erase a).erase b, X.mult s(z, w) = 0 := by
      intro w hw
      simp only [Finset.mem_erase, Finset.mem_sdiff] at hw
      obtain ⟨hwb, hwa, hwV, hwZ⟩ := hw
      by_contra hm
      rcases hR.mem_poles hwV hwa hwb with hwK | hwK
      · exact hwZ (hcl z hz w hwK hm)
      · exact hm (hR.noBond z hzK w hwK)
    have hzp : z ≠ xp := fun h => hR.not_mem_both hzK (h ▸ hR.xp_mem)
    have hzq : z ≠ yp := fun h => hR.not_mem_both hzK (h ▸ hR.yp_mem)
    rw [← Finset.add_sum_erase _ _ haS, ← Finset.add_sum_erase _ _ hbS, Finset.sum_eq_zero hzero, add_zero,
      Sym2.eq_swap, hR.mult_a z, Sym2.eq_swap, hR.mult_b z, if_neg hzb, if_neg hza]
    simp only [hzp, hzq, or_false]
  unfold cut
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- In a block, rung data has connected poles: it is a 2-cut rung. -/
theorem IsBlockU.isRungAt_of_rungCore {p q : V} (hX : IsBlockU X p q) (hR : RungCore X a b xm xp ym yp Km Kp) :
    IsRungAt X a b xm xp ym yp Km Kp := by
  classical
  have hconn := hX.2.2.2.2.2.2
  have hpole : ∀ {K : Finset V} {x y : V}, RungCore X a b x xp y yp K Kp ∨ RungCore X a b x xm y ym K Km →
      x ∈ K → ConnOn X K := by
    intro K x y hRK hxK
    apply connOn_of_closed
    intro Z hZ hne hcl
    -- uniform access to the rung data with `K` as the first pole
    obtain ⟨Kp', xp', yp', hR'⟩ : ∃ Kp' xp' yp', RungCore X a b x xp' y yp' K Kp' := by
      rcases hRK with h | h
      · exact ⟨_, _, _, h⟩
      · exact ⟨_, _, _, h⟩
    have hcZ := hR'.cut_of_closedIn hZ hcl
    have hW : K \ Z ⊆ K := Finset.sdiff_subset
    have hclW : ∀ u ∈ K \ Z, ∀ w ∈ K, X.mult s(u, w) ≠ 0 → w ∈ K \ Z := by
      intro u hu w hw hm
      refine Finset.mem_sdiff.mpr ⟨hw, fun hwZ => ?_⟩
      exact (Finset.mem_sdiff.mp hu).2 (hcl w hwZ u (Finset.mem_sdiff.mp hu).1 (by rw [Sym2.eq_swap]; exact hm))
    have hcW := hR'.cut_of_closedIn hW hclW
    have hevZ := hX.even_cut (Y := Z) (fun z hz => (hR'.mem_verts (Or.inl (hZ hz))).1)
    have hevW := hX.even_cut (Y := K \ Z) (fun z hz => (hR'.mem_verts (Or.inl (hW hz))).1)
    rw [hcZ] at hevZ
    rw [hcW] at hevW
    -- a set with no leaving bond is everything, which is impossible inside a pole
    have hnot0 : ∀ Y ⊆ K, Y.Nonempty → cut X Y ≠ 0 := by
      intro Y hY hYne h0
      have hall := eq_of_closed' hconn (fun z hz => (hR'.mem_verts (Or.inl (hY hz))).1) hYne
        (fun u hu w hw hm => closed_of_cut_zero X h0 u hu w hw hm)
      have : a ∈ Y := by rw [hall]; exact hR'.a_verts
      exact (hR'.ne_of_mem (Or.inl (hY this))).1 rfl
    by_cases hxZ : x ∈ Z
    · have hyZ : y ∈ Z := by
        by_contra h; rw [if_pos hxZ, if_neg h] at hevZ; exact absurd hevZ (by decide)
      by_contra hne'
      have hWne : (K \ Z).Nonempty := by
        obtain ⟨w, hwK, hwZ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hZ, hne'⟩)
        exact ⟨w, Finset.mem_sdiff.mpr ⟨hwK, hwZ⟩⟩
      apply hnot0 (K \ Z) hW hWne
      rw [hR'.cut_of_closedIn hW hclW]
      simp [hxZ, hyZ]
    · have hyZ : y ∉ Z := by
        intro h; rw [if_neg hxZ, if_pos h] at hevZ; exact absurd hevZ (by decide)
      exfalso
      apply hnot0 Z hZ hne
      rw [hcZ]; simp [hxZ, hyZ]
  have hxb : xm ≠ b := (hR.ne_of_mem (Or.inl hR.xm_mem)).2
  have hpb : xp ≠ b := (hR.ne_of_mem (Or.inr hR.xp_mem)).2
  have hya : ym ≠ a := (hR.ne_of_mem (Or.inl hR.ym_mem)).1
  have hqa : yp ≠ a := (hR.ne_of_mem (Or.inr hR.yp_mem)).1
  refine ⟨hR.ne, hR.a_verts, hR.b_verts, by rw [hR.mult_a]; simp, hR.disj, hR.union,
    hpole (Or.inl hR) hR.xm_mem, hpole (Or.inr hR.swapPoles) hR.xp_mem, hR.noBond, hR.xm_mem, hR.xp_mem,
    hR.ym_mem, hR.yp_mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR.mult_a]; simp [hxb]
  · rw [hR.mult_a]; simp [hpb]
  · rw [hR.mult_b]; simp [hya]
  · rw [hR.mult_b]; simp [hqa]
  · intro z h1 h2 h3; rw [hR.mult_a]; simp [h1, h2, h3]
  · intro z h1 h2 h3; rw [hR.mult_b]; simp [h1, h2, h3]

/-- A non-cap rung of a T-vine (given by rung data, rung atoms interior) can be deleted. -/
theorem isTVineU_rungDel_of_noncap {p q : V} (hT : IsTVineU X p q) (hR : RungCore X a b xm xp ym yp Km Kp)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q) (hnc : ¬ IsCapAt p q Km Kp) (μ : Bool) :
    IsTVineU (rungDel X a b xm xp ym yp μ) p q :=
  isTVineU_rungDel hT ⟨⟨hT.1.isRungAt_of_rungCore hR, hap, haq, hbp, hbq⟩, hnc⟩ μ

end

end WaveTurbulence.TVine.Core
