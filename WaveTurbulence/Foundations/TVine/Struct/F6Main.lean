/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.F6
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F6), U level: the theorem (packet L3)

**`f6U`**: two vine-like sub-objects of a T-vine whose atom sets overlap without nesting are double bonds (kinds `[I]`)
sharing exactly one atom. See `Struct/F6.lean` for the cases.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem kinds_card_I {G : UMultigraph V} {U : SubObj V} (hU : IsVineLikeU G U [.I]) : U.atoms.card = 2 := by
  have h := chain_single_inv hU.2
  have := card_isVineXU_I h
  rwa [induce_verts] at this

theorem eq_I_of_reverse {ks : List EnlKind} (h : ks.reverse = [.I]) : ks = [.I] := by
  rw [← List.reverse_reverse ks, h]; rfl

/-- Orient a member so that a given joint is its second joint. -/
theorem orient_end {G : UMultigraph V} {U : SubObj V} {ks : List EnlKind} (hU : IsVineLikeU G U ks) {k : V}
    (hk : k = U.k₁ ∨ k = U.k₂) : ∃ U' : SubObj V, ∃ ks' : List EnlKind, IsVineLikeU G U' ks' ∧
      U'.atoms = U.atoms ∧ U'.k₂ = k ∧ U'.hyper = U.hyper ∧ (ks' = [.I] → ks = [.I]) := by
  rcases hk with rfl | rfl
  · exact ⟨U.swap, ks.reverse, IsVineLikeU.swap' hU, rfl, rfl, rfl, eq_I_of_reverse⟩
  · exact ⟨U, ks, hU, rfl, rfl, rfl, id⟩

/-- Orient a member so that a given joint is its first joint. -/
theorem orient_start {G : UMultigraph V} {U : SubObj V} {ks : List EnlKind} (hU : IsVineLikeU G U ks) {k : V}
    (hk : k = U.k₁ ∨ k = U.k₂) : ∃ U' : SubObj V, ∃ ks' : List EnlKind, IsVineLikeU G U' ks' ∧
      U'.atoms = U.atoms ∧ U'.k₁ = k ∧ U'.hyper = U.hyper ∧ (ks' = [.I] → ks = [.I]) ∧
      (U'.k₂ = U.k₁ ∨ U'.k₂ = U.k₂) ∧ (ks = [.I, .I] → ks' = [.I, .I]) := by
  rcases hk with rfl | rfl
  · exact ⟨U, ks, hU, rfl, rfl, rfl, id, Or.inr rfl, id⟩
  · exact ⟨U.swap, ks.reverse, IsVineLikeU.swap' hU, rfl, rfl, rfl, eq_I_of_reverse, Or.inl rfl, fun h => by rw [h]; rfl⟩

theorem subset_interior_of_sub {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) {U : SubObj V}
    (hU : IsSubObjU G U) {K : Finset V} (hK : K ⊆ U.atoms) : K ⊆ Core.interior G j₁ j₂ := fun x hx =>
  Finset.mem_erase.mpr ⟨fun h => (joints_out hT hU).2 (h ▸ hK hx),
    Finset.mem_erase.mpr ⟨fun h => (joints_out hT hU).1 (h ▸ hK hx), hU.1.subset (hK hx)⟩⟩

/-- **N2 Theorem 1.15 (F6), U level.** -/
theorem f6U (I : Thm115Inputs.{u}) {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) {U W : SubObj V}
    {ksU ksW : List EnlKind} (hU : IsVineLikeU G U ksU) (hW : IsVineLikeU G W ksW)
    (hne : (U.atoms ∩ W.atoms).Nonempty) (hUW : ¬ U.atoms ⊆ W.atoms) (hWU : ¬ W.atoms ⊆ U.atoms) :
    ksU = [.I] ∧ ksW = [.I] ∧ (U.atoms ∩ W.atoms).card = 1 := by
  classical
  have hB := hT.1
  have hAV : U.atoms ⊆ G.verts := hU.1.1.subset
  have hBV : W.atoms ⊆ G.verts := hW.1.1.subset
  obtain ⟨p, hp⟩ := hne
  have hp' : p ∈ W.atoms ∩ U.atoms := by rw [Finset.inter_comm]; exact hp
  obtain ⟨q', hq'A, hq'B⟩ := Finset.not_subset.mp hUW
  obtain ⟨q, hqB, hqA⟩ := Finset.not_subset.mp hWU
  have hqR : q ∈ W.atoms \ U.atoms := Finset.mem_sdiff.mpr ⟨hqB, hqA⟩
  have hq'Q : q' ∈ U.atoms \ W.atoms := Finset.mem_sdiff.mpr ⟨hq'A, hq'B⟩
  by_cases hUin : U.k₁ ∈ W.atoms ∧ U.k₂ ∈ W.atoms <;> by_cases hWin : W.k₁ ∈ U.atoms ∧ W.k₂ ∈ U.atoms
  · -- all four joints in `P`: two disjoint pendant 2-poles
    exfalso
    have h1 := cutQ_two hT hU.1 hW.1 hUin hWin hq'Q
    have h2 := cutQ_two hT hW.1 hU.1 hWin hUin hqR
    refine pendantPoles_holds G j₁ j₂ _ _ hT (subset_interior_of_sub hT hU.1 Finset.sdiff_subset)
      (subset_interior_of_sub hT hW.1 Finset.sdiff_subset) ?_ ⟨q', hq'Q⟩ ⟨q, hqR⟩ h1 h2
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  · exfalso
    obtain ⟨k, hk, -, -, -, huniq⟩ := one_joint hT hW.1 hU.1 hWin hp' hq'Q
    exact cut_atom_false hT hW.1 hU.1 hUin hq'Q (Finset.mem_inter.mp hk).1 huniq
  · exfalso
    obtain ⟨k, hk, -, -, -, huniq⟩ := one_joint hT hU.1 hW.1 hUin hp hqR
    exact cut_atom_false hT hU.1 hW.1 hWin hqR (Finset.mem_inter.mp hk).1 huniq
  -- one joint of each in `P`
  obtain ⟨kA, hkA, hkAj, hUb, hsumA, huA⟩ := one_joint hT hU.1 hW.1 hUin hp hqR
  obtain ⟨kB, hkB, hkBj, hWb, hsumB, huB⟩ := one_joint hT hW.1 hU.1 hWin hp' hq'Q
  have hkB' : kB ∈ U.atoms ∩ W.atoms := by rw [Finset.inter_comm]; exact hkB
  by_cases hk : kA = kB
  · -- scenario (b): a concatenation at `k`
    subst hk
    set k := kA
    have hkAU := (Finset.mem_inter.mp hkA).1
    have hkAW := (Finset.mem_inter.mp hkA).2
    -- `P = {k}`
    set P' := (U.atoms ∩ W.atoms).erase k
    have hdeg : ∑ w ∈ G.verts, G.mult s(k, w) ≤ 4 := by
      have := deg_four hT hU.1 hkAU; unfold deg at this; omega
    have hP'0 : ∑ y ∈ P', G.mult s(k, y) = 0 := by
      have hd1 : Disjoint (W.atoms \ U.atoms) (U.atoms \ W.atoms) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
      have hd2 : Disjoint ((W.atoms \ U.atoms) ∪ (U.atoms \ W.atoms)) P' := by
        rw [Finset.disjoint_left]; intro x hx hx'
        have hxP := (Finset.mem_erase.mp hx').2
        rcases Finset.mem_union.mp hx with h | h
        · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hxP).1
        · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hxP).2
      have hsub : (W.atoms \ U.atoms) ∪ (U.atoms \ W.atoms) ∪ P' ⊆ G.verts := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact hBV (Finset.mem_sdiff.mp h).1
          · exact hAV (Finset.mem_sdiff.mp h).1
        · exact hAV (Finset.mem_inter.mp (Finset.mem_erase.mp h).2).1
      have := Finset.sum_le_sum_of_subset (f := fun y => G.mult s(k, y)) hsub
      rw [Finset.sum_union hd2, Finset.sum_union hd1] at this
      omega
    have hcl : ∀ u ∈ P', ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ P' := by
      intro u hu w hw hm
      have huk := (Finset.mem_erase.mp hu).1
      have huP := (Finset.mem_erase.mp hu).2
      have hU1 : ¬ (u = U.k₁ ∨ u = U.k₂) := fun h => huk (huA u huP h)
      have hW1 : ¬ (u = W.k₁ ∨ u = W.k₂) := fun h => huk (huB u (by rw [Finset.inter_comm]; exact huP) h)
      push_neg at hU1 hW1
      have hwA := mem_of_inner_bond hB hU.1 (Finset.mem_inter.mp huP).1 hU1.1 hU1.2 hw hm
      have hwB := mem_of_inner_bond hB hW.1 (Finset.mem_inter.mp huP).2 hW1.1 hW1.2 hw hm
      refine Finset.mem_erase.mpr ⟨fun hwk => ?_, Finset.mem_inter.mpr ⟨hwA, hwB⟩⟩
      subst hwk
      have := (Finset.sum_eq_zero_iff.mp hP'0) u hu
      rw [Sym2.eq_swap] at this
      exact hm this
    have hP'e : P' = ∅ := by
      by_contra hne
      have := eq_of_closed' hB.2.2.2.2.2.2 (fun x hx => hAV (Finset.mem_inter.mp (Finset.mem_erase.mp hx).2).1)
        (Finset.nonempty_iff_ne_empty.mpr hne) hcl
      have hj : j₁ ∈ P' := by show j₁ ∈ (U.atoms ∩ W.atoms).erase k; rw [this]; exact hB.1
      exact (joints_out hT hU.1).1 (Finset.mem_inter.mp (Finset.mem_erase.mp hj).2).1
    have hPk : U.atoms ∩ W.atoms = {k} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hxk
        have : x ∈ P' := Finset.mem_erase.mpr ⟨hxk, hx⟩
        rw [hP'e] at this; simp at this
      · rintro rfl; exact hkA
    -- the concatenation
    obtain ⟨U', ksU', hU', hU'a, hU'k, hU'h, hU'I⟩ := orient_end hU hkAj
    obtain ⟨W', ksW', hW', hW'a, hW'k, hW'h, hW'I, -, -⟩ := orient_start hW hkBj
    have hall := concat_allowed I hT hU' hW' (hU'h.trans hUb) (hW'h.trans hWb) (hU'k.trans hW'k.symm)
      (by rw [hU'a, hW'a, hW'k]; exact hPk)
    obtain ⟨h1, h2⟩ := allowed_append hall (chain_ne_nil hU'.2) (chain_ne_nil hW'.2)
    exact ⟨hU'I h1, hW'I h2, by rw [hPk]; rfl⟩
  · -- `kA ≠ kB`: `W` is a VC:I+I whose far double bond concatenates with `U`
    exfalso
    have hkAU := (Finset.mem_inter.mp hkA).1
    have hkAW := (Finset.mem_inter.mp hkA).2
    have hkBU := (Finset.mem_inter.mp hkB').1
    have hkBW := (Finset.mem_inter.mp hkB').2
    have hkAnW : ¬ (kA = W.k₁ ∨ kA = W.k₂) := fun h => hk (huB kA (by rw [Finset.inter_comm]; exact hkA) h)
    push_neg at hkAnW
    have hqkA : q ≠ kA := fun h => hqA (h ▸ hkAU)
    have hqkB : q ≠ kB := fun h => hqA (h ▸ hkBU)
    have hcardB : 3 ≤ W.atoms.card := by
      have : ({kA, kB, q} : Finset V) ⊆ W.atoms := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hkAW
        · exact hkBW
        · exact hqB
      have h3 := Finset.card_le_card this
      rwa [Finset.card_insert_of_notMem (by simp [hk, Ne.symm hqkA]),
        Finset.card_pair (Ne.symm hqkB)] at h3
    have hksW := (subObj_single I _ G j₁ j₂ rfl hT W ksW hW).1
    rcases hksW with rfl | rfl | rfl
    · have := kinds_card_I hW; omega
    · -- `ksW = [I, I]`
      obtain ⟨W', ksW', hW', hW'a, hW'k, hW'h, -, hW'k2, hW'II⟩ := orient_start hW hkBj
      have hks' := hW'II rfl
      subst hks'
      have hch : ChainU (W'.core G) W.atoms kB W'.k₂ ([.I] ++ [.I]) := by
        have := hW'.2; rw [hW'a, hW'k] at this; exact this
      obtain ⟨S', T, c, h1, hkT, hST, hab, hBeq⟩ := chain_append_inv (List.cons_ne_nil _ _) hch
      set c' := W'.k₂
      have hc'nA : c' ∉ U.atoms := by
        intro h
        have hj : c' = W.k₁ ∨ c' = W.k₂ := by rcases hW'k2 with h' | h' <;> simp [h']
        have := huB c' (Finset.mem_inter.mpr ⟨(hBeq ▸ Finset.mem_union_right _ (by
          have := hkT.1.2.1; rwa [induce_verts] at this) : c' ∈ W.atoms), h⟩) hj
        exact hW'.1.2.2.2.2.1 (hW'k.trans this.symm)
      have hcT : c ∈ T := by have := hkT.1.1; rwa [induce_verts] at this
      have hc'T : c' ∈ T := by have := hkT.1.2.1; rwa [induce_verts] at this
      have hcc' : c ≠ c' := hkT.1.2.2.1
      have hT2 : T = {c, c'} := by
        have hcardT : T.card = 2 := by have := card_isVineXU_I hkT; rwa [induce_verts] at this
        exact (Finset.eq_of_subset_of_card_le
          (Finset.insert_subset hcT (Finset.singleton_subset_iff.mpr hc'T))
          (by rw [hcardT, Finset.card_pair hcc'])).symm
      have hS'2 : S' = {kB, c} := by
        have hcardS : S'.card = 2 := by
          have := card_isVineXU_I (chain_single_inv h1); rwa [induce_verts] at this
        have hm := ChainU.ends_mem h1
        exact (Finset.eq_of_subset_of_card_le
          (Finset.insert_subset hm.1 (Finset.singleton_subset_iff.mpr hm.2))
          (by rw [hcardS, Finset.card_pair (ChainU.ne h1)])).symm
      have hcA : c = kA := by
        have : kA ∈ S' ∪ T := hBeq ▸ hkAW
        rw [hS'2, hT2] at this
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with (h | h) | (h | h)
        · exact absurd h hk
        · exact h.symm
        · exact h.symm
        · exact absurd (h ▸ hkAU) hc'nA
      -- the double bond `Y = {kA, c'}`
      have hTB : T ⊆ W.atoms := hBeq ▸ Finset.subset_union_right
      have hWcore : W'.core G = induce G W.atoms := by rw [core_eq_induce (hW'h.trans hWb), hW'a]
      have hYW : induce G T = induce (W'.core G) T := by
        rw [hWcore]
        exact (ChainU.induce_congr' (H := G) fun u hu w hw => Core.induce_mult_of_mem G (hTB hu) (hTB hw)).symm
      have hTT : induce (induce G T) T = induce G T :=
        ChainU.induce_congr' (H := G) fun u hu w hw => Core.induce_mult_of_mem G hu hw
      set Y : SubObj V := ⟨T, c, c', false⟩
      have hYcore : Y.core G = induce G T := core_eq_induce rfl
      have hY : IsVineLikeU G Y [.I] := by
        refine ⟨⟨Finset.ssubset_of_subset_of_ssubset hTB hW.1.1, fun h => by simp [Y] at h, ?_⟩, ?_⟩
        · rw [hYcore, hYW]; exact hkT.1
        · refine .single ?_
          show IsVineKindU .I (induce (Y.core G) T) c c'
          rw [hYcore, hTT, hYW]; exact hkT
      obtain ⟨U', ksU', hU', hU'a, hU'k, hU'h, hU'I⟩ := orient_end hU hkAj
      have hall := concat_allowed I hT hU' hY (hU'h.trans hUb) rfl (hU'k.trans hcA.symm) (by
        show U'.atoms ∩ T = {c}
        rw [hU'a, hT2]
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, rfl | rfl⟩
          · rfl
          · exact absurd hx hc'nA
        · rintro rfl; exact ⟨hcA ▸ hkAU, Or.inl rfl⟩)
      obtain ⟨h1', -⟩ := allowed_append hall (chain_ne_nil hU'.2) (List.cons_ne_nil _ _)
      have hcardA := kinds_card_I (hU'I h1' ▸ hU)
      have : ({kA, kB, q'} : Finset V) ⊆ U.atoms := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hkAU
        · exact hkBU
        · exact hq'A
      have h3 := Finset.card_le_card this
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hk, fun h => hq'B (h ▸ hkAW)⟩),
        Finset.card_pair (show kB ≠ q' from fun h => hq'B (h ▸ hkBW))] at h3
      omega
    · -- `ksW = [T]`: `kA` would be a cut atom of the T-vine `W°`
      have hTW : IsTVineU (W.core G) W.k₁ W.k₂ := by
        have := chain_single_inv hW.2
        rw [← core_verts G W, induce_self] at this
        exact this
      have hint : kA ∈ Core.interior (W.core G) W.k₁ W.k₂ :=
        Finset.mem_erase.mpr ⟨hkAnW.2, Finset.mem_erase.mpr ⟨hkAnW.1, by rw [core_verts]; exact hkAW⟩⟩
      have hc := noCutVertex_holds (W.core G) W.k₁ W.k₂ hTW kA hint
      set S0 := (U.atoms ∩ W.atoms).erase kA
      have hS0 : S0 ⊆ (W.core G).verts.erase kA := by
        intro x hx
        rw [core_verts]
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, (Finset.mem_inter.mp (Finset.mem_erase.mp hx).2).2⟩
      have hS0ne : S0.Nonempty := ⟨kB, Finset.mem_erase.mpr ⟨Ne.symm hk, hkB'⟩⟩
      have hcl : ∀ x ∈ S0, ∀ w ∈ (W.core G).verts.erase kA, (W.core G).mult s(x, w) ≠ 0 → w ∈ S0 := by
        intro x hx w hw hm
        rw [core_verts] at hw
        have hxk := (Finset.mem_erase.mp hx).1
        have hxP := (Finset.mem_erase.mp hx).2
        have hm' : G.mult s(x, w) ≠ 0 := fun h => hm (Nat.le_zero.mp (h ▸ core_le G W _))
        refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_inter.mpr ⟨?_, (Finset.mem_erase.mp hw).2⟩⟩
        by_contra hwA
        exact hxk (huA x hxP (joint_of_out hB hU.1 (Finset.mem_inter.mp hxP).1 (hBV (Finset.mem_erase.mp hw).2) hwA hm'))
      have := eq_of_closed' hc hS0 hS0ne hcl
      have hqS : q ∈ S0 := by
        rw [this, core_verts]; exact Finset.mem_erase.mpr ⟨hqkA, hqB⟩
      exact hqA (Finset.mem_inter.mp (Finset.mem_erase.mp hqS).2).1

end WaveTurbulence.TVine.Struct
