/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Statements
public import Mathlib.Data.ZMod.Basic

/-!
# Parity (N2 Lemma 1.10) and even cuts

* `even_sum_deg_add_cut`: `Σ_{v ∈ Y} deg v + cut Y` is even (handshake, mod 2);
* `even_cut_of_even_deg`, `IsBlockU.even_cut`: in a block (degrees 2 and 4) every cut is even;
* `deg_eraseBond`: removing one copy of a bond `x–y` lowers the degrees of `x` and `y` by one;
* `parity_holds : ParityStatement` (N2 Lemma 1.10).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- An off-diagonal double sum of a symmetric function is even. -/
theorem even_sum_offDiag (Y : Finset V) (f : V → V → ℕ) (hf : ∀ v w, f v w = f w v) :
    Even (∑ p ∈ Y.offDiag, f p.1 p.2) := by
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p hp _ => ?_) (fun p hp => ?_)
    (fun p _ => Prod.swap_swap p)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hf p.2 p.1, h2]
  · rw [Finset.mem_offDiag] at hp
    intro h
    apply hp.2.2
    have := congrArg Prod.snd h
    simpa using this
  · rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩

/-- The diagonal part of a double sum. -/
theorem sum_diag_eq (Y : Finset V) (f : V → V → ℕ) : ∑ p ∈ Y.diag, f p.1 p.2 = ∑ v ∈ Y, f v v := by
  refine Finset.sum_nbij' Prod.fst (fun v => (v, v)) (fun p hp => ?_) (fun v hv => ?_) (fun p hp => ?_)
    (fun v _ => rfl) (fun p hp => ?_)
  · exact (Finset.mem_diag.mp hp).1
  · exact Finset.mem_diag.mpr ⟨hv, rfl⟩
  · have := (Finset.mem_diag.mp hp).2
    ext <;> simp [this]
  · have := (Finset.mem_diag.mp hp).2
    simp [← this]

/-- **Handshake parity**: `Σ_{v ∈ Y} deg v + cut Y` is even. -/
theorem even_sum_deg_add_cut (H : UMultigraph V) {Y : Finset V} (hY : Y ⊆ H.verts) :
    Even (∑ v ∈ Y, deg H v + cut H Y) := by
  have hsplit : ∀ v, ∑ w ∈ H.verts, H.mult s(v, w) =
      ∑ w ∈ Y, H.mult s(v, w) + ∑ w ∈ H.verts \ Y, H.mult s(v, w) := by
    intro v
    rw [add_comm, Finset.sum_sdiff hY]
  have hdeg : ∑ v ∈ Y, deg H v =
      ∑ v ∈ Y, ∑ w ∈ Y, H.mult s(v, w) + cut H Y + ∑ v ∈ Y, H.mult s(v, v) := by
    simp only [deg, hsplit, Finset.sum_add_distrib, cut]
  have hprod : ∑ v ∈ Y, ∑ w ∈ Y, H.mult s(v, w) =
      ∑ v ∈ Y, H.mult s(v, v) + ∑ p ∈ Y.offDiag, H.mult s(p.1, p.2) := by
    rw [← Finset.sum_product' (f := fun v w => H.mult s(v, w)), ← Finset.diag_union_offDiag,
      Finset.sum_union (Finset.disjoint_diag_offDiag Y), sum_diag_eq Y (fun v w => H.mult s(v, w))]
  obtain ⟨k, hk⟩ := even_sum_offDiag Y (fun v w => H.mult s(v, w)) (fun v w => by rw [Sym2.eq_swap])
  refine ⟨∑ v ∈ Y, H.mult s(v, v) + cut H Y + k, ?_⟩
  rw [hdeg, hprod, hk]
  ring

/-- If every degree in `Y` is even, so is `cut Y`. -/
theorem even_cut_of_even_deg (H : UMultigraph V) {Y : Finset V} (hY : Y ⊆ H.verts)
    (hdeg : ∀ v ∈ Y, Even (deg H v)) : Even (cut H Y) := by
  have h := even_sum_deg_add_cut H hY
  have hs : Even (∑ v ∈ Y, deg H v) := Finset.even_sum _ hdeg
  exact (Nat.even_add.mp h).mp hs

/-- In a block every cut is even (all degrees are 2 or 4). -/
theorem IsBlockU.even_cut {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {Y : Finset V}
    (hY : Y ⊆ G.verts) : Even (cut G Y) := by
  apply even_cut_of_even_deg G hY
  intro v hv
  by_cases h1 : v = j₁
  · rw [h1, hB.2.2.2.1]; decide
  by_cases h2 : v = j₂
  · rw [h2, hB.2.2.2.2.1]; decide
  rw [hB.2.2.2.2.2.1 v (hY hv) h1 h2]; decide

/-- Removing one copy of the bond `x–y` (`x ≠ y`) lowers the degrees of `x` and `y` by one. -/
theorem deg_eraseBond (G : UMultigraph V) {x y : V} (hxy : x ≠ y) (hx : x ∈ G.verts) (hy : y ∈ G.verts)
    (hm : G.mult s(x, y) ≠ 0) (v : V) :
    deg (eraseBond G s(x, y)) v + (if v = x ∨ v = y then 1 else 0) = deg G v := by
  have hmult : ∀ w, (eraseBond G s(x, y)).mult s(v, w) =
      if s(v, w) = s(x, y) then G.mult s(v, w) - 1 else G.mult s(v, w) := fun w => rfl
  have hloop : (eraseBond G s(x, y)).mult s(v, v) = G.mult s(v, v) := by
    rw [hmult, if_neg]
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hxy (h1.symm.trans h2)
    · exact hxy (h2.symm.trans h1)
  unfold deg
  rw [show (eraseBond G s(x, y)).verts = G.verts from rfl, hloop]
  by_cases hv : v = x ∨ v = y
  · rw [if_pos hv]
    -- the other endpoint
    obtain ⟨o, ho, hoV, hiff⟩ : ∃ o, s(v, o) = s(x, y) ∧ o ∈ G.verts ∧ ∀ w, s(v, w) = s(x, y) ↔ w = o := by
      rcases hv with rfl | rfl
      · exact ⟨y, rfl, hy, fun w => Sym2.congr_right⟩
      · exact ⟨x, Sym2.eq_swap, hx, fun w => by rw [Sym2.eq_swap (a := x), Sym2.congr_right]⟩
    rw [← Finset.add_sum_erase _ _ hoV, ← Finset.add_sum_erase _ _ hoV, hmult, if_pos ho]
    have hrest : ∑ w ∈ G.verts.erase o, (eraseBond G s(x, y)).mult s(v, w) =
        ∑ w ∈ G.verts.erase o, G.mult s(v, w) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hmult, if_neg (fun h => (Finset.ne_of_mem_erase hw) ((hiff w).mp h))]
    rw [hrest, ho]
    have : 1 ≤ G.mult s(x, y) := Nat.one_le_iff_ne_zero.mpr hm
    omega
  · rw [if_neg hv, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [hmult, if_neg]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hv (Or.inl h1)
    · exact hv (Or.inr h1)

/-- **N2 Lemma 1.10** (parity). -/
theorem parity_holds : ParityStatement.{u} := by
  intro V _ G U X hU
  obtain ⟨hsub, hadj, hB⟩ := hU
  set H := U.edges G with hH
  have hHV : H.verts = U.atoms := rfl
  have hY : X ∩ U.atoms ⊆ H.verts := by rw [hHV]; exact Finset.inter_subset_right
  have hhand := even_sum_deg_add_cut H hY
  have hk₁ := hB.1
  have hk₂ := hB.2.1
  have hk := hB.2.2.1
  constructor
  · intro hb
    have hcore : U.core G = H := by simp [SubObj.core, hb, hH]
    rw [hcore] at hB
    exact even_cut_of_even_deg H hY fun v hv => by
      have hvV : v ∈ H.verts := hY hv
      by_cases h1 : v = U.k₁
      · rw [h1, hB.2.2.2.1]; decide
      by_cases h2 : v = U.k₂
      · rw [h2, hB.2.2.2.2.1]; decide
      rw [hB.2.2.2.2.2.1 v hvV h1 h2]; decide
  · intro hh
    have hcore : U.core G = eraseBond H s(U.k₁, U.k₂) := by simp [SubObj.core, hh, hH]
    rw [hcore] at hB hk₁ hk₂
    have hk₁H : U.k₁ ∈ H.verts := hk₁
    have hk₂H : U.k₂ ∈ H.verts := hk₂
    have hmH : H.mult s(U.k₁, U.k₂) ≠ 0 := by
      have hin : s(U.k₁, U.k₂) ∈ U.atoms.sym2 := by
        rw [Finset.mem_sym2_iff]; intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        exacts [hk₁H, hk₂H]
      show (if s(U.k₁, U.k₂) ∈ U.atoms.sym2 then G.mult s(U.k₁, U.k₂) else 0) ≠ 0
      rw [if_pos hin]; exact hadj hh
    have hd := deg_eraseBond H hk hk₁H hk₂H hmH
    -- parity of `Σ deg H` over `Y` is the number of joints of `U` in `Y`
    have heven : Even (∑ v ∈ X ∩ U.atoms, deg (eraseBond H s(U.k₁, U.k₂)) v) := by
      apply Finset.even_sum
      intro v hv
      have hvV : v ∈ (eraseBond H s(U.k₁, U.k₂)).verts := hY hv
      by_cases h1 : v = U.k₁
      · rw [h1, hB.2.2.2.1]; decide
      by_cases h2 : v = U.k₂
      · rw [h2, hB.2.2.2.2.1]; decide
      rw [hB.2.2.2.2.2.1 v hvV h1 h2]; decide
    have hsum : ∑ v ∈ X ∩ U.atoms, deg H v = ∑ v ∈ X ∩ U.atoms, deg (eraseBond H s(U.k₁, U.k₂)) v +
        ∑ v ∈ X ∩ U.atoms, (if v = U.k₁ ∨ v = U.k₂ then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => (hd v).symm
    have hk₁A : U.k₁ ∈ U.atoms := hk₁H
    have hk₂A : U.k₂ ∈ U.atoms := hk₂H
    have hcount : ∑ v ∈ X ∩ U.atoms, (if v = U.k₁ ∨ v = U.k₂ then 1 else 0) =
        (if U.k₁ ∈ X then 1 else 0) + (if U.k₂ ∈ X then 1 else 0) := by
      have hsplit : ∀ v, (if v = U.k₁ ∨ v = U.k₂ then 1 else 0) =
          (if v = U.k₁ then 1 else 0) + (if v = U.k₂ then 1 else 0) := by
        intro v
        by_cases h1 : v = U.k₁
        · subst h1; rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hk]
        · rw [if_neg h1, zero_add]
          by_cases h2 : v = U.k₂
          · rw [if_pos (Or.inr h2), if_pos h2]
          · rw [if_neg (by tauto), if_neg h2]
      rw [Finset.sum_congr rfl fun v _ => hsplit v, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq']
      simp only [Finset.mem_inter, hk₁A, hk₂A, and_true]
    rw [hsum, hcount] at hhand
    -- parity bookkeeping
    have h3 := Nat.even_add.mp hhand
    have h4 : Even (∑ v ∈ X ∩ U.atoms, deg (eraseBond H s(U.k₁, U.k₂)) v +
        ((if U.k₁ ∈ X then 1 else 0) + (if U.k₂ ∈ X then 1 else 0))) ↔
        Even ((if U.k₁ ∈ X then 1 else 0) + (if U.k₂ ∈ X then 1 else 0)) := by
      rw [Nat.even_add]
      exact ⟨fun h => h.mp heven, fun h => ⟨fun _ => h, fun _ => heven⟩⟩
    have hc := h3.symm.trans h4
    rw [← Nat.not_even_iff_odd, hc]
    by_cases h1 : U.k₁ ∈ X <;> by_cases h2 : U.k₂ ∈ X <;> simp [h1, h2, Nat.even_iff]

end WaveTurbulence.TVine.Core
