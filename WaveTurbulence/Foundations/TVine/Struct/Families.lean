/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.RemoveAll
public import WaveTurbulence.Foundations.TVine.Struct.IIData
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F5) for families, U level, sources' semantics (packet L3)

N2 L404–L419 (`research-gamma-half-2/NOTES.md`), induction on `|B| + |F|`:
* base `|B| ≤ 13`: L2's `FamiliesBaseStatement` (N2's semantics removes more: `connected_removeAll_of_removeAllN`);
* a deletable rung containing no joint of a member: N2 Lemma 1.14(e) (`PhiRemovalInput`) and the induction
  hypothesis for `B/R` and `Φ(F)` (sub-objects by 1.14(b));
* a member is the double bond of a deletable rung `R = {a, b}` (`step1_transfer`): `B` minus that double bond is
  `B/[crossed]R` with its two new bonds subdivided by `a` and `b`;
* otherwise (N2 Lemma 1.11) every deletable rung carries a side hyper-block member; two disjoint ones give two
  disjoint joint-free pendant 2-poles, contradicting N3 Lemma 6.2. So `D(B) ≤ 1` and `|B| ≤ 13` (L2's size bound).

**`families`**: for a T-vine `G` and pairwise atom-disjoint sub-objects `Us`, `removeAll G Us` is connected.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem removeAll_perm (G : UMultigraph V) {Us Us' : List (SubObj V)} (hp : Us.Perm Us')
    (hsub : ∀ U ∈ Us, U.atoms ⊆ G.verts) (hdisj : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms)) :
    removeAll G Us = removeAll G Us' := by
  have hsub' : ∀ U ∈ Us', U.atoms ⊆ G.verts := fun U hU => hsub U (hp.mem_iff.mpr hU)
  have hdisj' : Us'.Pairwise (fun U W => Disjoint U.atoms W.atoms) :=
    hp.pairwise hdisj (fun h => h.symm)
  obtain ⟨hv, hm⟩ := removeAll_eq G Us hsub hdisj
  obtain ⟨hv', hm'⟩ := removeAll_eq G Us' hsub' hdisj'
  have hin : Checker.innerAll Us = Checker.innerAll Us' := by
    ext x; rw [mem_innerAll, mem_innerAll]
    exact ⟨fun ⟨U, hU, hx⟩ => ⟨U, hp.mem_iff.mp hU, hx⟩, fun ⟨U, hU, hx⟩ => ⟨U, hp.mem_iff.mpr hU, hx⟩⟩
  refine Core.ext (by rw [hv, hv', hin]) fun e => ?_
  rw [hm, hm', hin, (hp.map _).sum_eq]

theorem inner_eq_empty_of_pair {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) {a b : V}
    (hA : U.atoms = {a, b}) : U.inner = ∅ := by
  have h1 := k₁_mem hU
  have h2 := k₂_mem hU
  have hne := hU.2.2.2.2.1
  rw [hA] at h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  unfold SubObj.inner
  rw [hA]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  rintro ⟨hx2, hx1, hx⟩
  rcases hx with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- An atom bonded to an atom outside `S(W)` is not inner in `W`. -/
theorem not_mem_inner_of_bond {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {W : SubObj V}
    (hW : IsSubObjU G W) {x y : V} (hy : y ∈ G.verts) (hyW : y ∉ W.atoms) (hm : 1 ≤ G.mult s(x, y)) :
    x ∉ W.inner := by
  intro hx
  have hxA : x ∈ W.atoms := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
  have hx₁ : x ≠ W.k₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
  have hx₂ : x ≠ W.k₂ := (Finset.mem_erase.mp hx).1
  have hA : W.atoms ⊆ G.verts := hW.1.subset
  have h4 : deg (W.core G) x = 4 := hW.2.2.2.2.2.2.2.1 x (by rw [core_verts]; exact hxA) hx₁ hx₂
  have hle := deg_core_add_le hA hxA (T := {y}) (by simp [hy, hyW])
  simp only [Finset.sum_singleton] at hle
  have hdeg : deg G x ≤ 4 := by
    by_cases h1 : x = j₁
    · rw [h1, hB.2.2.2.1]; omega
    by_cases h2 : x = j₂
    · rw [h2, hB.2.2.2.2.1]; omega
    rw [hB.2.2.2.2.2.1 x (hA hxA) h1 h2]
  omega

/-- **Step 1 of (F5)**: a member that is the double bond of a rung `R = {a, b}`. If `B/[crossed]R` minus the other
members is connected, so is `B` minus all members. -/
theorem step1_transfer {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (hB : IsBlockU G j₁ j₂) (hR : IsRungAt G a b xm xp ym yp Km Kp) {U₀ : SubObj V} (hU₀ : IsSubObjU G U₀)
    (hU₀a : U₀.atoms = {a, b}) {Ws : List (SubObj V)} (hWs : ∀ W ∈ Ws, IsSubObjU G W)
    (hWd : ∀ W ∈ Ws, Disjoint U₀.atoms W.atoms) (hWp : Ws.Pairwise (fun U W => Disjoint U.atoms W.atoms))
    (hA : Connected (removeAll (rungDel G a b xm xp ym yp false) Ws)) :
    Connected (removeAll G (U₀ :: Ws)) := by
  set G' := rungDel G a b xm xp ym yp false with hG'
  have hG'v : G'.verts = (G.verts.erase a).erase b := hR.verts_rungDel false
  have haW : ∀ W ∈ Ws, a ∉ W.atoms := fun W hW h =>
    Finset.disjoint_left.mp (hWd W hW) (by rw [hU₀a]; simp) h
  have hbW : ∀ W ∈ Ws, b ∉ W.atoms := fun W hW h =>
    Finset.disjoint_left.mp (hWd W hW) (by rw [hU₀a]; simp) h
  have hsubG : ∀ W ∈ U₀ :: Ws, W.atoms ⊆ G.verts := by
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact hU₀.1.subset
    · exact (hWs W hW).1.subset
  have hdisjG : (U₀ :: Ws).Pairwise (fun U W => Disjoint U.atoms W.atoms) := List.pairwise_cons.mpr ⟨hWd, hWp⟩
  have hsubG' : ∀ W ∈ Ws, W.atoms ⊆ G'.verts := by
    intro W hW x hx
    rw [hG'v]
    refine Finset.mem_erase.mpr ⟨fun h => hbW W hW (h ▸ hx), Finset.mem_erase.mpr
      ⟨fun h => haW W hW (h ▸ hx), (hWs W hW).1.subset hx⟩⟩
  obtain ⟨hBv, hBm⟩ := removeAll_eq G (U₀ :: Ws) hsubG hdisjG
  obtain ⟨hAv, hAm⟩ := removeAll_eq G' Ws hsubG' hWp
  have hin : Checker.innerAll (U₀ :: Ws) = Checker.innerAll Ws := by
    show U₀.inner ∪ Checker.innerAll Ws = _
    rw [inner_eq_empty_of_pair hU₀ hU₀a, Finset.empty_union]
  set A := removeAll G' Ws
  set B := removeAll G (U₀ :: Ws)
  have hAv' : ∀ x, x ∈ A.verts ↔ x ∈ G.verts ∧ x ≠ a ∧ x ≠ b ∧ x ∉ Checker.innerAll Ws := by
    intro x
    rw [hAv, hG'v, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_erase]; tauto
  have hBv' : ∀ x, x ∈ B.verts ↔ x ∈ G.verts ∧ x ∉ Checker.innerAll Ws := by
    intro x; rw [hBv, hin, Finset.mem_sdiff]
  have hAB : ∀ x ∈ A.verts, x ∈ B.verts := fun x hx => by
    obtain ⟨h1, -, -, h4⟩ := (hAv' x).mp hx
    exact (hBv' x).mpr ⟨h1, h4⟩
  -- rail ends are not inner atoms of the other members
  have hnotin : ∀ x, x ∈ G.verts → (1 ≤ G.mult s(x, a) ∨ 1 ≤ G.mult s(x, b)) → x ∉ Checker.innerAll Ws := by
    intro x hx hxab hin'
    obtain ⟨W, hW, hxW⟩ := mem_innerAll.mp hin'
    rcases hxab with h | h
    · exact not_mem_inner_of_bond hB (hWs W hW) hR.a_mem (haW W hW) h hxW
    · exact not_mem_inner_of_bond hB (hWs W hW) hR.b_mem (hbW W hW) h hxW
  have hKm : Km ⊆ (G.verts.erase a).erase b := hR.union ▸ Finset.subset_union_left
  have hKp : Kp ⊆ (G.verts.erase a).erase b := hR.union ▸ Finset.subset_union_right
  have hmemK : ∀ x ∈ (G.verts.erase a).erase b, x ∈ G.verts ∧ x ≠ a ∧ x ≠ b := fun x hx =>
    ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2, (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1,
      (Finset.mem_erase.mp hx).1⟩
  have hrailA : ∀ x, x ∈ (G.verts.erase a).erase b → (1 ≤ G.mult s(x, a) ∨ 1 ≤ G.mult s(x, b)) → x ∈ A.verts := by
    intro x hx hab
    obtain ⟨h1, h2, h3⟩ := hmemK x hx
    exact (hAv' x).mpr ⟨h1, h2, h3, hnotin x h1 hab⟩
  have hxmA : xm ∈ A.verts := hrailA xm (hKm hR.xm_mem) (Or.inl (by rw [Sym2.eq_swap, hR.a_xm]))
  have hxpA : xp ∈ A.verts := hrailA xp (hKp hR.xp_mem) (Or.inl (by rw [Sym2.eq_swap, hR.a_xp]))
  have hymA : ym ∈ A.verts := hrailA ym (hKm hR.ym_mem) (Or.inr (by rw [Sym2.eq_swap, hR.b_ym]))
  have hypA : yp ∈ A.verts := hrailA yp (hKp hR.yp_mem) (Or.inr (by rw [Sym2.eq_swap, hR.b_yp]))
  have haB : a ∈ B.verts := (hBv' a).mpr ⟨hR.a_mem, fun h => by
    obtain ⟨W, hW, hx⟩ := mem_innerAll.mp h
    exact haW W hW (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2⟩
  have hbB : b ∈ B.verts := (hBv' b).mpr ⟨hR.b_mem, fun h => by
    obtain ⟨W, hW, hx⟩ := mem_innerAll.mp h
    exact hbW W hW (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2⟩
  -- the rails survive in `B`
  have hrailB : ∀ c x, (c = a ∨ c = b) → c ∈ B.verts → x ∈ A.verts → G.mult s(c, x) = 1 →
      AdjIn B B.verts c x := by
    intro c x hc hcB hxA hm
    refine ⟨hcB, hAB x hxA, ?_⟩
    have hxne : x ≠ a ∧ x ≠ b := ⟨((hAv' x).mp hxA).2.1, ((hAv' x).mp hxA).2.2.1⟩
    rw [mult_removeAll_of_out G (U₀ :: Ws) hsubG hdisjG (by
        rw [← hBv]; exact Finset.mem_sym2_iff.mpr fun z hz => by
          rcases Sym2.mem_iff.mp hz with h | h
          · rw [h]; exact hcB
          · rw [h]; exact hAB x hxA) (by
        intro W hW hmem
        have hx := Finset.mem_sym2_iff.mp hmem x (Sym2.mem_mk_right c x)
        have hc' := Finset.mem_sym2_iff.mp hmem c (Sym2.mem_mk_left c x)
        rcases List.mem_cons.mp hW with rfl | hW
        · rw [hU₀a] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · exact hxne.1 h
          · exact hxne.2 h
        · rcases hc with rfl | rfl
          · exact haW W hW hc'
          · exact hbW W hW hc')]
    omega
  have haxm := hrailB a xm (Or.inl rfl) haB hxmA hR.a_xm
  have haxp := hrailB a xp (Or.inl rfl) haB hxpA hR.a_xp
  have hbym := hrailB b ym (Or.inr rfl) hbB hymA hR.b_ym
  have hbyp := hrailB b yp (Or.inr rfl) hbB hypA hR.b_yp
  have hsymm : ∀ p q, AdjIn B B.verts p q → AdjIn B B.verts q p := fun p q h =>
    ⟨h.2.1, h.1, by rw [Sym2.eq_swap]; exact h.2.2⟩
  -- every edge of `A` is a path of `B`
  have hlift : ∀ p q, AdjIn A A.verts p q → Relation.ReflTransGen (AdjIn B B.verts) p q := by
    intro p q hpq
    obtain ⟨hp, hq, hm⟩ := hpq
    obtain ⟨hpG, hpa, hpb, hpin⟩ := (hAv' p).mp hp
    obtain ⟨hqG, hqa, hqb, hqin⟩ := (hAv' q).mp hq
    by_cases hx : s(p, q) = s(xm, xp)
    · rcases Sym2.eq_iff.mp hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .tail (.single (hsymm _ _ haxm)) haxp
      · exact .tail (.single (hsymm _ _ haxp)) haxm
    by_cases hy : s(p, q) = s(ym, yp)
    · rcases Sym2.eq_iff.mp hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .tail (.single (hsymm _ _ hbym)) hbyp
      · exact .tail (.single (hsymm _ _ hbyp)) hbym
    refine .single ⟨hAB p hp, hAB q hq, ?_⟩
    have hpqA : s(p, q) ∈ A.verts.sym2 := Finset.mem_sym2_iff.mpr fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hp
      · exact hq
    have hpqB : s(p, q) ∈ B.verts.sym2 := Finset.mem_sym2_iff.mpr fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hAB _ hp
      · exact hAB _ hq
    have hG'm : G'.mult s(p, q) = G.mult s(p, q) := by
      rw [hG', rungDel_mult, if_neg (by
        rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
        · exact hpa h.symm
        · exact hqa h.symm
        · exact hpb h.symm
        · exact hqb h.symm)]
      have : (rungAdds xm xp ym yp false).count s(p, q) = 0 := by
        rw [Multiset.count_eq_zero]
        show s(p, q) ∉ ({s(xm, xp), s(ym, yp)} : Multiset (Sym2 V))
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
        exact ⟨hx, hy⟩
      rw [this, add_zero]
    have hcores : (Ws.map fun W => (W.core G').mult s(p, q)) = Ws.map fun W => (W.core G).mult s(p, q) :=
      List.map_congr_left fun W _ => core_mult_congr W hG'm
    have hU₀m : (U₀.core G).mult s(p, q) = 0 := by
      refine core_mult_of_not_mem G U₀ fun h => ?_
      have := Finset.mem_sym2_iff.mp h p (Sym2.mem_mk_left p q)
      rw [hU₀a] at this; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hpa h
      · exact hpb h
    have hmA := hm
    rw [hAm, ← hAv, if_pos hpqA, hcores, hG'm] at hmA
    rw [hBm, ← hBv, if_pos hpqB, List.map_cons, List.sum_cons, hU₀m, zero_add]
    exact hmA
  -- assemble
  have hproj : ∀ x ∈ B.verts, ∃ x' ∈ A.verts, Relation.ReflTransGen (AdjIn B B.verts) x x' := by
    intro x hx
    by_cases hxa : x = a
    · subst hxa; exact ⟨xm, hxmA, .single haxm⟩
    by_cases hxb : x = b
    · subst hxb; exact ⟨ym, hymA, .single hbym⟩
    obtain ⟨h1, h2⟩ := (hBv' x).mp hx
    exact ⟨x, (hAv' x).mpr ⟨h1, hxa, hxb, h2⟩, .refl⟩
  have hsymmR : ∀ p q, Relation.ReflTransGen (AdjIn B B.verts) p q → Relation.ReflTransGen (AdjIn B B.verts) q p :=
    fun p q h => by
      induction h with
      | refl => exact .refl
      | tail _ hbc ih => exact .head (hsymm _ _ hbc) ih
  intro x hx y hy
  obtain ⟨x', hx'A, hxx'⟩ := hproj x hx
  obtain ⟨y', hy'A, hyy'⟩ := hproj y hy
  have hpath : Relation.ReflTransGen (AdjIn B B.verts) x' y' := by
    have h := hA x' hx'A y' hy'A
    clear hyy' hy'A
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.trans (hlift _ _ hbc)
  exact (hxx'.trans hpath).trans (hsymmR _ _ hyy')

end WaveTurbulence.TVine.Struct
