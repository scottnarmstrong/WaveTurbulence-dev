/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiChain2
public import WaveTurbulence.Foundations.TVine.Core.PhiGap2

/-!
# N2 Lemma 1.14(c′): the Q-block case and the assembly

* `gapCut_of_qPrefix`: if the rung is the rung of a 4-atom Q-block ingredient of `U`, the gap of `U` at `k₁` is
  cut in `G`: `X₀ = {k₁} ∪ (K⁻ ∖ P)` (`K⁻` the pole of the Q-block's first joint, `P` the atoms of the chain before
  the Q-block) is left only by the two bonds of `U°` at `k₁`. By N2 1.14(d) (`phiGap_holds`) the gap of `Φ(U)` is
  then cut in `G/[μ]R`.
* `IsSubObjU.rungCore_core`, `phi_core_eq`: the rung data inside `U°` and `Φ(U)° = U°/[μ]R` (all-in case).
* `phiType_of_ingStep`: N2 1.14(c′) from the ingredient step `IngStep`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- A cut with a single boundary atom. -/
theorem cut_eq_of_boundary (G : UMultigraph V) {X : Finset V} {z₀ : V} (hz₀ : z₀ ∈ X)
    (hcross : ∀ z ∈ X, ∀ w ∈ G.verts \ X, G.mult s(z, w) ≠ 0 → z = z₀) :
    cut G X = ∑ w ∈ G.verts \ X, G.mult s(z₀, w) := by
  unfold cut
  rw [Finset.sum_eq_single z₀]
  · intro z hz hne
    apply Finset.sum_eq_zero; intro w hw; by_contra h; exact hne (hcross z hz w hw h)
  · intro h; exact absurd hz₀ h

theorem SubObj.core_mult_of_mem (G : UMultigraph V) (U : SubObj V) {v w : V} (hv : v ∈ U.atoms)
    (hw : w ∈ U.atoms) (hne : s(v, w) ≠ s(U.k₁, U.k₂)) : (U.core G).mult s(v, w) = G.mult s(v, w) := by
  unfold SubObj.core
  split
  · show (if s(v, w) = s(U.k₁, U.k₂) then (induce G U.atoms).mult s(v, w) - 1
      else (induce G U.atoms).mult s(v, w)) = _
    rw [if_neg hne]; exact induce_mult_of_mem G hv hw
  · exact induce_mult_of_mem G hv hw

section Gap

variable {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp p : V} {Km Kp : Finset V} {U : SubObj V} {P : Finset V}

/-- **The gap of `U` is cut in the Q-block case.** -/
theorem gapCut_of_qPrefix (hB : IsBlockU G j₁ j₂) (hl : G.Loopless) (hR : RungCore G a b xm xp ym yp Km Kp)
    (hU : IsSubObjU G U) (haS : a ∈ U.atoms) (hbS : b ∈ U.atoms) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b)
    (hPS : P ⊆ U.atoms) (hkP : U.k₁ ∈ P) (hpP : p ∈ P) (haP : a ∉ P) (hbP : b ∉ P) (h2P : U.k₂ ∉ P)
    (hcl : ∀ v ∈ P, ∀ w ∈ (U.core G).verts, (U.core G).mult s(v, w) ≠ 0 → w ∈ P ∨ (v = p ∧ (w = a ∨ w = b)))
    (hPK : P ⊆ Km) (hxm : xm = p) (hym : ym = p) : GapCutAt G U U.k₁ := by
  classical
  have hHv : (U.core G).verts = U.atoms := SubObj.core_verts G U
  have hSV := hU.atoms_subset
  have hBH : IsBlockU (U.core G) U.k₁ U.k₂ := hU.2.2
  have h12 : U.k₁ ≠ U.k₂ := hBH.2.2.1
  have hk₁V : U.k₁ ∈ G.verts := hSV (hPS hkP)
  have hKmV : Km ⊆ G.verts := fun x hx => (hR.mem_verts (Or.inl hx)).1
  have hk₁K : U.k₁ ∈ Km := hPK hkP
  have hak : a ≠ U.k₁ := fun h => haP (by rw [h]; exact hkP)
  have hbk : b ≠ U.k₁ := fun h => hbP (by rw [h]; exact hkP)
  have hadj : ∀ v w, v ≠ U.k₁ → v ≠ U.k₂ → s(v, w) ≠ s(U.k₁, U.k₂) := by
    intro v w h1 h2 h
    rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    exacts [h1 h', h2 h']
  have hadj' : ∀ w, w ≠ U.k₂ → s(U.k₁, w) ≠ s(U.k₁, U.k₂) := by
    intro w hw h
    rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [hw h', h12 h']
  set X₀ := insert U.k₁ (Km \ P) with hX₀
  have hX₀V : X₀ ⊆ G.verts := Finset.insert_subset hk₁V (fun x hx => hKmV (Finset.mem_sdiff.mp hx).1)
  have haK : a ∉ Km := fun h => (hR.ne_of_mem (Or.inl h)).1 rfl
  have hbK : b ∉ Km := fun h => (hR.ne_of_mem (Or.inl h)).2 rfl
  have haX : a ∉ X₀ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hak h
    · exact haK (Finset.mem_sdiff.mp h).1
  have hbX : b ∉ X₀ := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hbk h
    · exact hbK (Finset.mem_sdiff.mp h).1
  -- the atoms of `P` other than `k₁` keep their bonds of `G` inside `P`, up to `p–a, p–b`
  have hinner : ∀ v ∈ P, v ≠ U.k₁ → ∀ w ∈ G.verts, G.mult s(v, w) ≠ 0 → w ∈ P ∨ (v = p ∧ (w = a ∨ w = b)) := by
    intro v hv hv1 w hw hm
    have hv2 : v ≠ U.k₂ := fun h => h2P (by rw [← h]; exact hv)
    obtain ⟨-, -, hcl'⟩ := hU.closed_of_inner hB (hPS hv) hv1 hv2
    have hwS := hcl' w hw hm
    apply hcl v hv w (by rw [hHv]; exact hwS)
    rw [SubObj.core_mult_of_mem G U (hPS hv) hwS (hadj v w hv1 hv2)]; exact hm
  -- only `k₁` has bonds leaving `X₀`
  have hcross : ∀ z ∈ X₀, ∀ w ∈ G.verts \ X₀, G.mult s(z, w) ≠ 0 → z = U.k₁ := by
    intro z hz w hw hm
    by_contra hz1
    have hzKP : z ∈ Km \ P := by
      rcases Finset.mem_insert.mp hz with h | h
      · exact absurd h hz1
      · exact h
    obtain ⟨hzK, hzP⟩ := Finset.mem_sdiff.mp hzKP
    obtain ⟨hwV, hwX⟩ := Finset.mem_sdiff.mp hw
    have hza : z ≠ a := (hR.ne_of_mem (Or.inl hzK)).1
    have hzb : z ≠ b := (hR.ne_of_mem (Or.inl hzK)).2
    have hzp : z ≠ p := fun h => hzP (by rw [h]; exact hpP)
    have hzxp : z ≠ xp := fun h => hR.not_mem_both hzK (by rw [h]; exact hR.xp_mem)
    have hzyp : z ≠ yp := fun h => hR.not_mem_both hzK (by rw [h]; exact hR.yp_mem)
    by_cases hwa : w = a
    · have hn : ¬ (z = xm ∨ z = xp) := by
        rintro (h | h)
        · exact hzp (h.trans hxm)
        · exact hzxp h
      rw [hwa, Sym2.eq_swap, hR.mult_a, if_neg hzb, if_neg hn] at hm
      exact hm rfl
    by_cases hwb : w = b
    · have hn : ¬ (z = ym ∨ z = yp) := by
        rintro (h | h)
        · exact hzp (h.trans hym)
        · exact hzyp h
      rw [hwb, Sym2.eq_swap, hR.mult_b, if_neg hza, if_neg hn] at hm
      exact hm rfl
    rcases hR.mem_poles hwV hwa hwb with hwK | hwK
    · have hwP : w ∈ P := by
        by_contra hwP
        exact hwX (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hwK, hwP⟩))
      have hw1 : w ≠ U.k₁ := fun h => hwX (by rw [h]; exact Finset.mem_insert_self _ _)
      rcases hinner w hwP hw1 z (hKmV hzK) (by rw [Sym2.eq_swap]; exact hm) with h | ⟨-, h | h⟩
      · exact hzP h
      · exact hza h
      · exact hzb h
    · exact hm (hR.noBond z hzK w hwK)
  have hcut : cut G X₀ = ∑ w ∈ G.verts \ X₀, G.mult s(U.k₁, w) :=
    cut_eq_of_boundary G (Finset.mem_insert_self _ _) hcross
  -- the bonds of `k₁` leaving `X₀` are its two bonds in `U°`
  set N := (insert a (insert b P)).erase U.k₁ with hN
  have hNsub : N ⊆ G.verts \ X₀ := by
    intro w hw
    obtain ⟨hw1, hw⟩ := Finset.mem_erase.mp hw
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rcases Finset.mem_insert.mp hw with h | hw
      · rw [h]; exact hR.a_verts
      rcases Finset.mem_insert.mp hw with h | hw
      · rw [h]; exact hR.b_verts
      · exact hSV (hPS hw)
    · intro hwX
      rcases Finset.mem_insert.mp hwX with h | h
      · exact hw1 h
      obtain ⟨hwK, hwP⟩ := Finset.mem_sdiff.mp h
      rcases Finset.mem_insert.mp hw with h | hw
      · rw [h] at hwK; exact haK hwK
      rcases Finset.mem_insert.mp hw with h | hw
      · rw [h] at hwK; exact hbK hwK
      · exact hwP hw
  have hzero_out : ∀ w ∈ G.verts \ X₀, w ∉ N → G.mult s(U.k₁, w) = 0 := by
    intro w hw hwN
    obtain ⟨hwV, hwX⟩ := Finset.mem_sdiff.mp hw
    have hw1 : w ≠ U.k₁ := fun h => hwX (by rw [h]; exact Finset.mem_insert_self _ _)
    have hwa : w ≠ a := fun h =>
      hwN (Finset.mem_erase.mpr ⟨hw1, by rw [h]; exact Finset.mem_insert_self _ _⟩)
    have hwb : w ≠ b := fun h =>
      hwN (Finset.mem_erase.mpr ⟨hw1, by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩)
    have hwP : w ∉ P := fun h =>
      hwN (Finset.mem_erase.mpr ⟨hw1, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)⟩)
    rcases hR.mem_poles hwV hwa hwb with hwK | hwK
    · exact absurd (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hwK, hwP⟩)) hwX
    · exact hR.noBond _ hk₁K w hwK
  have hNS : N ⊆ U.atoms := by
    intro w hw
    obtain ⟨-, hw⟩ := Finset.mem_erase.mp hw
    rcases Finset.mem_insert.mp hw with h | hw
    · rw [h]; exact haS
    rcases Finset.mem_insert.mp hw with h | hw
    · rw [h]; exact hbS
    · exact hPS hw
  have hk2N : U.k₂ ∉ N := by
    intro hw
    obtain ⟨-, hw⟩ := Finset.mem_erase.mp hw
    rcases Finset.mem_insert.mp hw with h | hw
    · exact h2a h
    rcases Finset.mem_insert.mp hw with h | hw
    · exact h2b h
    · exact h2P hw
  have hloop : (U.core G).mult s(U.k₁, U.k₁) = 0 := Nat.le_zero.mp (hl U.k₁ ▸ core_mult_le G U _)
  have hsum1 : ∑ w ∈ G.verts \ X₀, G.mult s(U.k₁, w) = ∑ w ∈ N, G.mult s(U.k₁, w) :=
    (Finset.sum_subset hNsub (fun w hw hwN => hzero_out w hw hwN)).symm
  have hsum2 : ∑ w ∈ N, G.mult s(U.k₁, w) = ∑ w ∈ N, (U.core G).mult s(U.k₁, w) := by
    apply Finset.sum_congr rfl
    intro w hw
    have hw2 : w ≠ U.k₂ := fun h => hk2N (by rw [← h]; exact hw)
    exact (SubObj.core_mult_of_mem G U hU.k₁_mem (hNS hw) (hadj' w hw2)).symm
  have hsum3 : ∑ w ∈ N, (U.core G).mult s(U.k₁, w) = ∑ w ∈ U.atoms, (U.core G).mult s(U.k₁, w) := by
    apply Finset.sum_subset hNS
    intro w hwS hwN
    by_contra hm
    apply hwN
    have hw1 : w ≠ U.k₁ := by
      intro h; rw [h] at hm; exact hm hloop
    refine Finset.mem_erase.mpr ⟨hw1, ?_⟩
    rcases hcl U.k₁ hkP w (by rw [hHv]; exact hwS) hm with h | ⟨-, h | h⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hdeg : ∑ w ∈ U.atoms, (U.core G).mult s(U.k₁, w) = 2 := by
    have h := hBH.2.2.2.1
    unfold deg at h
    rw [hHv, hloop, add_zero] at h; exact h
  have hHl : (U.core G).Loopless := fun v => Nat.le_zero.mp (hl v ▸ core_mult_le G U _)
  obtain ⟨n, n', hnn⟩ := hBH.nbrs_joint (Or.inl rfl)
  have hnout : ∀ x, x ∈ nbrs (U.core G) U.k₁ → x ∉ X₀ := by
    intro x hx hxX
    have hxV := mem_verts_of_mem_nbrs hx
    have hx1 : x ≠ U.k₁ := by
      intro h; rw [h] at hx; exact not_mem_nbrs_self hHl U.k₁ hx
    have hm : (U.core G).mult s(U.k₁, x) ≠ 0 := by
      have := count_nbrs (U.core G) U.k₁ x
      rw [if_pos hxV, if_neg (Ne.symm hx1), add_zero] at this
      rw [← this]; exact Multiset.count_ne_zero.mpr hx
    rcases hcl U.k₁ hkP x hxV hm with h | ⟨-, h | h⟩
    · rcases Finset.mem_insert.mp hxX with h' | h'
      · exact hx1 h'
      · exact (Finset.mem_sdiff.mp h').2 h
    · exact haX (by rw [← h]; exact hxX)
    · exact hbX (by rw [← h]; exact hxX)
  refine ⟨X₀, hX₀V, by rw [hcut, hsum1, hsum2, hsum3, hdeg], n, n', hnn, ?_, ?_⟩
  · exact ⟨fun _ => hnout n (by rw [hnn]; simp), fun _ => Finset.mem_insert_self _ _⟩
  · exact ⟨fun _ => hnout n' (by rw [hnn]; simp), fun _ => Finset.mem_insert_self _ _⟩

end Gap

end WaveTurbulence.TVine.Core
