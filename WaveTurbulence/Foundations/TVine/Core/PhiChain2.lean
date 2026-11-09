/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiChain

/-!
# N2 Lemma 1.14(c′), chain level: deleting a rung inside a vine chain

In a block `H` with joint `c` carrying a vine chain from `c`, a rung `R = {a, b}` with no junction or end in `R`
lies inside exactly one ingredient. Given the ingredient step (`IngConcl`: the ingredient keeps its kind, or it is
the 4-atom Q-block and becomes a double bond), `chain_rungDel` deletes `R` in the whole chain: either the chain
survives with the same kinds, or one (II) ingredient becomes (I) and we record the prefix before it (`QPrefix`).

* `ConnOn.of_induce`, `ConnOn.union`, `ChainU.connOn`;
* `ConnOn.subset_Km`: a connected set avoiding the rung lies in the pole of any of its atoms;
* `RungCore.rails_mem`, `rungDel_mult_off`, `rungDel_mult_on_off`, `RungCore.mult_rails_zero`;
* `IngConcl`, `QPrefix`, `ChainDelConcl`, `chain_rungDel`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section Conn

variable {H : UMultigraph V}

theorem ConnOn.of_induce {T : Finset V} (h : Connected (induce H T)) : ConnOn H T := by
  intro u hu w hw
  refine Relation.ReflTransGen.mono (fun x y hxy => ?_) u w (h u hu w hw)
  obtain ⟨hx, hy, hm⟩ := hxy
  exact ⟨hx, hy, by rwa [induce_mult_of_mem H (S := T) hx hy] at hm⟩

theorem ConnOn.union {S T : Finset V} {b : V} (hS : ConnOn H S) (hT : ConnOn H T) (hbS : b ∈ S) (hbT : b ∈ T) :
    ConnOn H (S ∪ T) := by
  have toB : ∀ u ∈ S ∪ T, Relation.ReflTransGen (AdjIn H (S ∪ T)) u b := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact Relation.ReflTransGen.mono (fun x y ⟨hx, hy, hm⟩ =>
        ⟨Finset.mem_union_left _ hx, Finset.mem_union_left _ hy, hm⟩) u b (hS u h b hbS)
    · exact Relation.ReflTransGen.mono (fun x y ⟨hx, hy, hm⟩ =>
        ⟨Finset.mem_union_right _ hx, Finset.mem_union_right _ hy, hm⟩) u b (hT u h b hbT)
  have hsymm : ∀ x y, AdjIn H (S ∪ T) x y → AdjIn H (S ∪ T) y x :=
    fun x y ⟨hx, hy, hm⟩ => ⟨hy, hx, by rwa [Sym2.eq_swap]⟩
  have hrev : ∀ x y, Relation.ReflTransGen (AdjIn H (S ∪ T)) x y → Relation.ReflTransGen (AdjIn H (S ∪ T)) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hxy ih => exact Relation.ReflTransGen.head (hsymm _ _ hxy) ih
  intro u hu w hw
  exact (toB u hu).trans (hrev _ _ (toB w hw))

theorem ChainU.connOn {S : Finset V} {c d : V} {ks : List EnlKind} (h : ChainU H S c d ks) : ConnOn H S := by
  induction h with
  | single hv => exact ConnOn.of_induce hv.isBlockU.2.2.2.2.2.2
  | append hch hv _ _ ih => exact ih.union (ConnOn.of_induce hv.isBlockU.2.2.2.2.2.2) hch.ends_mem.2 hv.isBlockU.1

variable {a b xm xp ym yp : V} {Km Kp : Finset V}

/-- A connected set avoiding the rung lies in the pole of any of its atoms. -/
theorem ConnOn.subset_Km (hR : RungCore H a b xm xp ym yp Km Kp) {P : Finset V} (hP : ConnOn H P)
    (hPV : P ⊆ H.verts) (haP : a ∉ P) (hbP : b ∉ P) {p : V} (hpP : p ∈ P) (hpK : p ∈ Km) : P ⊆ Km := by
  suffices key : ∀ v, Relation.ReflTransGen (AdjIn H P) p v → v ∈ Km from fun v hv => key v (hP p hpP v hv)
  intro v h
  induction h with
  | refl => exact hpK
  | @tail x y _ hxy ih =>
    obtain ⟨-, hy, hm⟩ := hxy
    have hya : y ≠ a := fun h => haP (by rw [← h]; exact hy)
    have hyb : y ≠ b := fun h => hbP (by rw [← h]; exact hy)
    rcases hR.mem_poles (hPV hy) hya hyb with h | h
    · exact h
    · exact absurd (hR.noBond x ih y h) hm

/-- Rails of a rung lie in any set closed around the rung atoms. -/
theorem RungCore.rails_mem (hR : RungCore H a b xm xp ym yp Km Kp) {T : Finset V}
    (hcla : ∀ w ∈ H.verts, H.mult s(a, w) ≠ 0 → w ∈ T)
    (hclb : b ∈ T → ∀ w ∈ H.verts, H.mult s(b, w) ≠ 0 → w ∈ T) :
    b ∈ T ∧ xm ∈ T ∧ xp ∈ T ∧ ym ∈ T ∧ yp ∈ T := by
  have hxmb : xm ≠ b := (hR.ne_of_mem (Or.inl hR.xm_mem)).2
  have hxpb : xp ≠ b := (hR.ne_of_mem (Or.inr hR.xp_mem)).2
  have hyma : ym ≠ a := (hR.ne_of_mem (Or.inl hR.ym_mem)).1
  have hypa : yp ≠ a := (hR.ne_of_mem (Or.inr hR.yp_mem)).1
  have hbT : b ∈ T := hcla b hR.b_verts (by rw [hR.mult_a]; simp)
  refine ⟨hbT, hcla xm (hR.mem_verts (Or.inl hR.xm_mem)).1 (by rw [hR.mult_a]; simp [hxmb]),
    hcla xp (hR.mem_verts (Or.inr hR.xp_mem)).1 (by rw [hR.mult_a]; simp [hxpb]),
    hclb hbT ym (hR.mem_verts (Or.inl hR.ym_mem)).1 (by rw [hR.mult_b]; simp [hyma]),
    hclb hbT yp (hR.mem_verts (Or.inr hR.yp_mem)).1 (by rw [hR.mult_b]; simp [hypa])⟩

/-- Multiplicities of the deletion away from the rung, at a pair with an end off the rails (or a diagonal). -/
theorem rungDel_mult_off (hR : RungCore H a b xm xp ym yp Km Kp) (μ : Bool) {u w : V}
    (hua : u ≠ a) (hub : u ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (hoff : (u ≠ xm ∧ u ≠ xp ∧ u ≠ ym ∧ u ≠ yp) ∨ (w ≠ xm ∧ w ≠ xp ∧ w ≠ ym ∧ w ≠ yp) ∨ u = w) :
    (rungDel H a b xm xp ym yp μ).mult s(u, w) = H.mult s(u, w) := by
  rw [rungDel_mult, if_neg (by
    rintro (h | h) <;> rcases Sym2.mem_iff.mp h with h | h
    exacts [hua h.symm, hwa h.symm, hub h.symm, hwb h.symm])]
  rcases hoff with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | rfl
  · rw [Multiset.count_eq_zero.mpr (fun hm => rungAdds_not_mem h1 h2 h3 h4 μ _ hm (Sym2.mem_mk_left u w)),
      add_zero]
  · rw [Multiset.count_eq_zero.mpr (fun hm => rungAdds_not_mem h1 h2 h3 h4 μ _ hm (Sym2.mem_mk_right u w)),
      add_zero]
  · rw [hR.rungAdds_count_diag, add_zero]

/-- The deletion does not change the bonds inside a set `T` avoiding the rung and meeting the rails' set `R` in at
most one atom. -/
theorem rungDel_mult_on_off (hR : RungCore H a b xm xp ym yp Km Kp) (μ : Bool) {T R : Finset V} {j : V}
    (hTR : ∀ x ∈ T, x ∈ R → x = j) (hxm : xm ∈ R) (hxp : xp ∈ R) (hym : ym ∈ R) (hyp : yp ∈ R)
    (haT : a ∉ T) (hbT : b ∉ T) :
    ∀ u ∈ T, ∀ w ∈ T, (rungDel H a b xm xp ym yp μ).mult s(u, w) = H.mult s(u, w) := by
  have hoff : ∀ x ∈ T, x ≠ j → x ≠ xm ∧ x ≠ xp ∧ x ≠ ym ∧ x ≠ yp := by
    intro x hx hxj
    refine ⟨fun h => hxj (hTR x hx (by rw [h]; exact hxm)), fun h => hxj (hTR x hx (by rw [h]; exact hxp)),
      fun h => hxj (hTR x hx (by rw [h]; exact hym)), fun h => hxj (hTR x hx (by rw [h]; exact hyp))⟩
  intro u hu w hw
  have hua : u ≠ a := fun h => haT (by rw [← h]; exact hu)
  have hub : u ≠ b := fun h => hbT (by rw [← h]; exact hu)
  have hwa : w ≠ a := fun h => haT (by rw [← h]; exact hw)
  have hwb : w ≠ b := fun h => hbT (by rw [← h]; exact hw)
  by_cases huw : u = w
  · exact rungDel_mult_off hR μ hua hub hwa hwb (Or.inr (Or.inr huw))
  · by_cases huj : u = j
    · have hwj : w ≠ j := fun h => huw (huj.trans h.symm)
      exact rungDel_mult_off hR μ hua hub hwa hwb (Or.inr (Or.inl (hoff w hw hwj)))
    · exact rungDel_mult_off hR μ hua hub hwa hwb (Or.inl (hoff u hu huj))

/-- Two atoms carrying opposite rail pairs are not bonded. -/
theorem RungCore.mult_rails_zero (hR : RungCore H a b xm xp ym yp Km Kp) {p q : V}
    (h : (xm = p ∧ ym = p ∧ xp = q ∧ yp = q) ∨ (xm = q ∧ ym = q ∧ xp = p ∧ yp = p)) : H.mult s(p, q) = 0 := by
  rcases h with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
  · exact hR.noBond p (by rw [← h1]; exact hR.xm_mem) q (by rw [← h3]; exact hR.xp_mem)
  · rw [Sym2.eq_swap]; exact hR.noBond q (by rw [← h1]; exact hR.xm_mem) p (by rw [← h3]; exact hR.xp_mem)

end Conn

/-- **The ingredient step**: the ingredient `X` (joints `p, q`) keeps its kind after deleting the rung, or it is the
4-atom Q-block `p, a, b, q` with rails at `p` and `q` and becomes the double bond (I). -/
def IngConcl (k : EnlKind) (X : UMultigraph V) (p q a b xm xp ym yp : V) (μ : Bool) : Prop :=
  IsVineKindU k (rungDel X a b xm xp ym yp μ) p q ∨
    (k = .II ∧ IsVineKindU .I (rungDel X a b xm xp ym yp μ) p q ∧ X.verts = {p, a, b, q} ∧
      ((xm = p ∧ ym = p ∧ xp = q ∧ yp = q) ∨ (xm = q ∧ ym = q ∧ xp = p ∧ yp = p)))

/-- **Prefix data of the Q-block case**: the atoms `P` of the chain before the Q-block (from `c` to its joint `p`),
closed in `H` except for the two bonds `p–a, p–b`, inside the pole of `p` (which carries both rails of its side). -/
def QPrefix (H : UMultigraph V) (a b xm xp ym yp : V) (Km Kp : Finset V) (S : Finset V) (c d : V) : Prop :=
  ∃ (P : Finset V) (p : V), P ⊆ S ∧ c ∈ P ∧ p ∈ P ∧ a ∉ P ∧ b ∉ P ∧ d ∉ P ∧
    (∀ v ∈ P, ∀ w ∈ H.verts, H.mult s(v, w) ≠ 0 → w ∈ P ∨ (v = p ∧ (w = a ∨ w = b))) ∧
    ((P ⊆ Km ∧ xm = p ∧ ym = p) ∨ (P ⊆ Kp ∧ xp = p ∧ yp = p))

/-- The conclusion of `chain_rungDel`. -/
def ChainDelConcl (H : UMultigraph V) (a b xm xp ym yp : V) (Km Kp : Finset V) (μ : Bool) (S : Finset V)
    (c d : V) (ks : List EnlKind) : Prop :=
  ChainU (rungDel H a b xm xp ym yp μ) ((S.erase a).erase b) c d ks ∨
    ∃ i : Fin ks.length, ks.get i = .II ∧
      ChainU (rungDel H a b xm xp ym yp μ) ((S.erase a).erase b) c d (ks.set i .I) ∧
      QPrefix H a b xm xp ym yp Km Kp S c d

section Chain

variable {H : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem qPrefix_mk (hR : RungCore H a b xm xp ym yp Km Kp) {P S : Finset V} {c d p q : V} (hPS : P ⊆ S)
    (hcP : c ∈ P) (hpP : p ∈ P) (haP : a ∉ P) (hbP : b ∉ P) (hdP : d ∉ P) (hconn : ConnOn H P)
    (hPV : P ⊆ H.verts) (hcl : ∀ v ∈ P, ∀ w ∈ H.verts, H.mult s(v, w) ≠ 0 → w ∈ P ∨ (v = p ∧ (w = a ∨ w = b)))
    (hrails : (xm = p ∧ ym = p ∧ xp = q ∧ yp = q) ∨ (xm = q ∧ ym = q ∧ xp = p ∧ yp = p)) :
    QPrefix H a b xm xp ym yp Km Kp S c d := by
  refine ⟨P, p, hPS, hcP, hpP, haP, hbP, hdP, hcl, ?_⟩
  rcases hrails with ⟨h1, h2, -, -⟩ | ⟨-, -, h3, h4⟩
  · exact Or.inl ⟨hconn.subset_Km hR hPV haP hbP hpP (by rw [← h1]; exact hR.xm_mem), h1, h2⟩
  · exact Or.inr ⟨hconn.subset_Km hR.swapPoles hPV haP hbP hpP (by rw [← h3]; exact hR.xp_mem), h3, h4⟩

theorem erase_erase_union_right {S T : Finset V} (haT : a ∉ T) (hbT : b ∉ T) :
    ((S ∪ T).erase a).erase b = ((S.erase a).erase b) ∪ T := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union]
  constructor
  · rintro ⟨hxb, hxa, hx | hx⟩
    · exact Or.inl ⟨hxb, hxa, hx⟩
    · exact Or.inr hx
  · rintro (⟨hxb, hxa, hx⟩ | hx)
    · exact ⟨hxb, hxa, Or.inl hx⟩
    · exact ⟨fun h => hbT (by rw [← h]; exact hx), fun h => haT (by rw [← h]; exact hx), Or.inr hx⟩

theorem erase_erase_union_left {S T : Finset V} (haS : a ∉ S) (hbS : b ∉ S) :
    ((S ∪ T).erase a).erase b = S ∪ ((T.erase a).erase b) := by
  rw [Finset.union_comm, erase_erase_union_right haS hbS, Finset.union_comm]

/-- **Deleting a rung inside a vine chain** (from the joint `c` of the block `H`), given the ingredient step. -/
theorem chain_rungDel (hl : H.Loopless) {e : V} (hR : RungCore H a b xm xp ym yp Km Kp) (μ : Bool)
    (hing : ∀ (k : EnlKind) (T : Finset V) (p q : V), IsVineKindU k (induce H T) p q → a ∈ T → b ∈ T →
      xm ∈ T → xp ∈ T → ym ∈ T → yp ∈ T → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IngConcl k (induce H T) p q a b xm xp ym yp μ)
    {S : Finset V} {c d : V} {ks : List EnlKind} (h : ChainU H S c d ks) :
    IsBlockU H c e → a ∈ S → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      ChainDelConcl H a b xm xp ym yp Km Kp μ S c d ks := by
  induction h with
  | @single T p q k hv =>
    intro hB haT hap haq hbp hbq
    have hBT := hv.isBlockU
    have hTV : T ⊆ H.verts := hBT.verts_subset_of_induce
    have hclT : ∀ v ∈ T, v ≠ p → v ≠ q → ∀ w ∈ H.verts, H.mult s(v, w) ≠ 0 → w ∈ T :=
      fun v hv hvp hvq => (interior_closed hB hTV hv (hBT.2.2.2.2.2.1 v hv hvp hvq)).2.2
    obtain ⟨hbT, hxm, hxp, hym, hyp⟩ :=
      hR.rails_mem (hclT a haT hap haq) (fun hbT => hclT b hbT hbp hbq)
    have hind := induce_rungDel hR haT hbT hxm hxp hym hyp μ
    rcases hing k T p q hv haT hbT hxm hxp hym hyp hap haq hbp hbq with hk | ⟨rfl, hI, hTv, hrails⟩
    · left
      exact .single (by rw [hind]; exact hk)
    · right
      refine ⟨⟨0, by simp⟩, rfl, .single (k := .I) (by rw [hind]; exact hI), ?_⟩
      have hTv' : T = {p, a, b, q} := hTv
      have hpq := hBT.2.2.1
      refine qPrefix_mk hR (P := {p}) (q := q) (Finset.singleton_subset_iff.mpr hBT.1) (Finset.mem_singleton_self p)
        (Finset.mem_singleton_self p) (by simpa using hap) (by simpa using hbp) (by simpa using hpq.symm)
        (fun u hu w hw => by
          rw [Finset.mem_singleton] at hu hw; rw [hu, hw])
        (Finset.singleton_subset_iff.mpr (hTV hBT.1)) ?_ hrails
      intro v hv w hw hm
      rw [Finset.mem_singleton] at hv
      subst hv
      have hwT := closed_of_deg_eq H hTV hBT.1 (by rw [hBT.2.2.2.1, hB.2.2.2.1]) w hw hm
      rw [hTv'] at hwT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwT
      rcases hwT with h | h | h | h
      · exact Or.inl (by rw [h]; exact Finset.mem_singleton_self _)
      · exact Or.inr ⟨rfl, Or.inl h⟩
      · exact Or.inr ⟨rfl, Or.inr h⟩
      · exact absurd (by rw [h]; exact hR.mult_rails_zero hrails) hm
  | @append S T c b' d ks k hch hv hST hcd ih =>
    intro hB haST hac had hbc hbd
    have hBT := hv.isBlockU
    have hTV : T ⊆ H.verts := hBT.verts_subset_of_induce
    have hSV : S ⊆ H.verts := hch.subset
    have hb'S : b' ∈ S := hch.ends_mem.2
    have hcS : c ∈ S := hch.ends_mem.1
    have hb'T : b' ∈ T := hBT.1
    have hdT : d ∈ T := hBT.2.1
    have hb'd : b' ≠ d := hBT.2.2.1
    have hST' : ∀ x ∈ S, x ∈ T → x = b' := by
      intro x hxS hxT
      have : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hxS, hxT⟩
      rw [hST] at this; exact Finset.mem_singleton.mp this
    have hdS : d ∉ S := fun h => hb'd (hST' d h hdT).symm
    have hab' : b' ≠ a := hch.junction_ne_a hl hB hR hv hST
    have hbb' : b' ≠ b := hch.junction_ne_a hl hB hR.swapAB hv hST
    have hfull : ChainU H (S ∪ T) c d (ks ++ [k]) := .append hch hv hST hcd
    have hclS := hch.prefix_closed hl hB
    by_cases haS : a ∈ S
    · -- the rung lies in the prefix; the last ingredient is unchanged
      obtain ⟨hbS, hxm, hxp, hym, hyp⟩ := hR.rails_mem (hclS a haS hab'.symm)
        (fun hbS => hclS b hbS hbb'.symm)
      have haT : a ∉ T := fun h => hab' (hST' a haS h).symm
      have hbT : b ∉ T := fun h => hbb' (hST' b hbS h).symm
      have hsameT := rungDel_mult_on_off hR μ (T := T) (R := S) (j := b') (fun x hxT hxS => hST' x hxS hxT)
        hxm hxp hym hyp haT hbT
      have hindT : induce (rungDel H a b xm xp ym yp μ) T = induce H T := ChainU.induce_congr' hsameT
      have hS'T : ((S.erase a).erase b) ∩ T = {b'} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨-, -, hx⟩, hxT⟩; exact hST' x hx hxT
        · rintro rfl; exact ⟨⟨hbb', hab', hb'S⟩, hb'T⟩
      have hset := erase_erase_union_right (S := S) haT hbT
      rcases ih hB haS hac hab'.symm hbc hbb'.symm with hc | ⟨i, hi, hc, P, p, hPS, hrest⟩
      · left
        rw [hset]
        exact .append hc (by rw [hindT]; exact hv) hS'T hcd
      · right
        have hi' : i.1 < (ks ++ [k]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        refine ⟨⟨i.1, hi'⟩, ?_, ?_, P, p, hPS.trans Finset.subset_union_left, ?_⟩
        · simp only [List.get_eq_getElem] at hi ⊢
          rw [List.getElem_append_left i.2]; exact hi
        · rw [hset, List.set_append, if_pos i.2]
          exact .append hc (by rw [hindT]; exact hv) hS'T hcd
        · obtain ⟨hcP, hpP, haP, hbP, -, hcl, hpole⟩ := hrest
          exact ⟨hcP, hpP, haP, hbP, fun h => hdS (hPS h), hcl, hpole⟩
    · -- the rung lies in the last ingredient; the prefix is unchanged
      have haT : a ∈ T := by
        rcases Finset.mem_union.mp haST with h | h
        · exact absurd h haS
        · exact h
      have hclT : ∀ v ∈ T, v ≠ b' → v ≠ d → ∀ w ∈ H.verts, H.mult s(v, w) ≠ 0 → w ∈ T :=
        fun v hv' hvp hvq => (interior_closed hB hTV hv' (hBT.2.2.2.2.2.1 v hv' hvp hvq)).2.2
      obtain ⟨hbT, hxm, hxp, hym, hyp⟩ := hR.rails_mem (hclT a haT hab'.symm had)
        (fun hbT => hclT b hbT hbb'.symm hbd)
      have hbS : b ∉ S := fun h => hbb' (hST' b h hbT).symm
      have hsameS := rungDel_mult_on_off hR μ (T := S) (R := T) (j := b') hST' hxm hxp hym hyp haS hbS
      have hchS : ChainU (rungDel H a b xm xp ym yp μ) S c b' ks := hch.congr hsameS
      have hind := induce_rungDel hR haT hbT hxm hxp hym hyp μ
      have hST'' : S ∩ ((T.erase a).erase b) = {b'} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, -, -, hxT⟩; exact hST' x hx hxT
        · rintro rfl; exact ⟨hb'S, hbb', hab', hb'T⟩
      have hset := erase_erase_union_left (T := T) haS hbS
      rcases hing k T b' d hv haT hbT hxm hxp hym hyp hab'.symm had hbb'.symm hbd with
        hk | ⟨rfl, hI, hTv, hrails⟩
      · left
        rw [hset]
        exact .append hchS (by rw [hind]; exact hk) hST'' hcd
      · right
        refine ⟨⟨ks.length, by simp⟩, by simp, ?_, ?_⟩
        · rw [hset]
          have : (ks ++ [EnlKind.II]).set ks.length .I = ks ++ [.I] := by simp
          rw [this]
          exact .append hchS (k := .I) (by rw [hind]; exact hI) hST'' hcd
        · have hTv' : T = {b', a, b, d} := hTv
          refine qPrefix_mk hR (P := S) (q := d) Finset.subset_union_left hcS hb'S haS hbS hdS hch.connOn hSV
            ?_ hrails
          intro v hvS w hw hm
          by_cases hvb' : v = b'
          · rw [hvb'] at hm ⊢
            have hwST := hfull.prefix_closed hl hB b' (Finset.mem_union_left _ hb'S) hb'd w hw hm
            rcases Finset.mem_union.mp hwST with h | h
            · exact Or.inl h
            · rw [hTv'] at h
              simp only [Finset.mem_insert, Finset.mem_singleton] at h
              rcases h with h | h | h | h
              · exact Or.inl (by rw [h]; exact hb'S)
              · exact Or.inr ⟨rfl, Or.inl h⟩
              · exact Or.inr ⟨rfl, Or.inr h⟩
              · exact absurd (by rw [h]; exact hR.mult_rails_zero hrails) hm
          · exact Or.inl (hclS v hvS hvb' w hw hm)

end Chain

end WaveTurbulence.TVine.Core
