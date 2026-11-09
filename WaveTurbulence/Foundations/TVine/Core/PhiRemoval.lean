/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Phi

/-!
# N2 Lemma 1.14(e): removal connectivity transfers along rung deletion

`phiRemoval_holds : PhiRemovalStatement`. Proof (N2 Lemma 1.14(e), sources' removal semantics):
* `removeAll_flat`: for pairwise disjoint members the iterated removal is the flat graph `G ∖ ⋃ I(U_i)` with the
  bonds of the `U_i°` subtracted;
* each member is all-in or all-out (`phiAllInOut_holds`); an all-out member lies in one pole and keeps its core
  (`core_rungDel_allOut`); an all-in member's image core gains exactly the two added bonds (`core_rungDel_allIn`);
* with one all-in member the two removed graphs coincide; with none, the removed graph of `G` is the removed graph
  of `G/[μ]R` with the rung re-inserted, and connectivity lifts through the rung.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-! ## Cores -/

theorem induce_mult_le (G : UMultigraph V) (S : Finset V) (e : Sym2 V) : (induce G S).mult e ≤ G.mult e := by
  show (if e ∈ S.sym2 then G.mult e else 0) ≤ _
  split_ifs <;> omega

theorem core_mult_le (G : UMultigraph V) (U : SubObj V) (e : Sym2 V) : (U.core G).mult e ≤ G.mult e := by
  unfold SubObj.core SubObj.edges
  split
  · show (if e = s(U.k₁, U.k₂) then (induce G U.atoms).mult e - 1 else (induce G U.atoms).mult e) ≤ _
    have := induce_mult_le G U.atoms e
    split_ifs <;> omega
  · exact induce_mult_le G U.atoms e

theorem core_mult_supp (G : UMultigraph V) (U : SubObj V) {e : Sym2 V} (h : (U.core G).mult e ≠ 0) :
    e ∈ U.atoms.sym2 := by
  rw [Finset.mem_sym2_iff]
  intro x hx
  have := (U.core G).supp e h x hx
  rwa [SubObj.core_verts] at this

theorem induce_congr {G G' : UMultigraph V} {S : Finset V} (h : ∀ e ∈ S.sym2, G.mult e = G'.mult e) :
    induce G S = induce G' S := by
  apply ext
  · rfl
  intro e
  show (if e ∈ S.sym2 then G.mult e else 0) = (if e ∈ S.sym2 then G'.mult e else 0)
  split_ifs with he
  · exact h e he
  · rfl

theorem core_congr {G G' : UMultigraph V} {U : SubObj V} (h : ∀ e ∈ U.atoms.sym2, G.mult e = G'.mult e) :
    U.core G = U.core G' := by
  unfold SubObj.core SubObj.edges
  rw [induce_congr h]

/-! ## The flat form of a removal -/

/-- The union of the interiors of a family. -/
def remInner : List (SubObj V) → Finset V
  | [] => ∅
  | U :: Us => U.inner ∪ remInner Us

/-- The sum of the core multiplicities of a family. -/
def remCoreSum (G : UMultigraph V) : List (SubObj V) → Sym2 V → ℕ
  | [], _ => 0
  | U :: Us, e => (U.core G).mult e + remCoreSum G Us e

theorem remCoreSum_congr {G G' : UMultigraph V} {Us : List (SubObj V)}
    (h : ∀ U ∈ Us, U.core G = U.core G') (e : Sym2 V) : remCoreSum G Us e = remCoreSum G' Us e := by
  induction Us with
  | nil => rfl
  | cons U Us ih =>
    simp only [remCoreSum]
    rw [h U List.mem_cons_self, ih fun W hW => h W (List.mem_cons_of_mem _ hW)]

theorem SubObj.inner_subset (U : SubObj V) : U.inner ⊆ U.atoms :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

theorem mem_remInner {Us : List (SubObj V)} {x : V} : x ∈ remInner Us ↔ ∃ U ∈ Us, x ∈ U.inner := by
  induction Us with
  | nil => simp [remInner]
  | cons U Us ih =>
    simp only [remInner, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨W, hW, h⟩)
      · exact ⟨U, Or.inl rfl, h⟩
      · exact ⟨W, Or.inr hW, h⟩
    · rintro ⟨W, rfl | hW, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨W, hW, h⟩

/-- **Flat form of an iterated removal** of pairwise disjoint members. -/
theorem removeAll_flat (G : UMultigraph V) (Us : List (SubObj V)) (hsub : ∀ U ∈ Us, U.atoms ⊆ G.verts)
    (hdisj : Us.Pairwise fun U W => Disjoint U.atoms W.atoms) :
    (removeAll G Us).verts = G.verts \ remInner Us ∧
      ∀ e, (removeAll G Us).mult e =
        if e ∈ (G.verts \ remInner Us).sym2 then G.mult e - remCoreSum G Us e else 0 := by
  induction Us generalizing G with
  | nil =>
    refine ⟨by simp [removeAll, remInner], fun e => ?_⟩
    simp only [removeAll, remInner, Finset.sdiff_empty, remCoreSum, Nat.sub_zero]
    split_ifs with he
    · rfl
    · by_contra hne
      exact he (Finset.mem_sym2_iff.mpr fun x hx => G.supp e hne x hx)
  | cons U Us ih =>
    rw [List.pairwise_cons] at hdisj
    set G₁ := removeSub G U with hG₁
    have hG₁V : G₁.verts = G.verts \ U.inner := rfl
    have hsub₁ : ∀ W ∈ Us, W.atoms ⊆ G₁.verts := by
      intro W hW x hx
      rw [hG₁V, Finset.mem_sdiff]
      refine ⟨hsub W (List.mem_cons_of_mem _ hW) hx, fun hxi => ?_⟩
      exact Finset.disjoint_left.mp (hdisj.1 W hW) (U.inner_subset hxi) hx
    obtain ⟨ihV, ihM⟩ := ih G₁ hsub₁ hdisj.2
    have hcores : ∀ W ∈ Us, W.core G₁ = W.core G := by
      intro W hW
      apply core_congr
      intro e he
      show (if e ∈ (G.verts \ U.inner).sym2 then G.mult e - (U.core G).mult e else 0) = G.mult e
      have he' : e ∈ (G.verts \ U.inner).sym2 := by
        rw [Finset.mem_sym2_iff] at he ⊢
        intro x hx; rw [← hG₁V]; exact hsub₁ W hW (he x hx)
      have hU0 : (U.core G).mult e = 0 := by
        by_contra hne
        have h1 := core_mult_supp G U hne
        obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
        exact Finset.disjoint_left.mp (hdisj.1 W hW) (Finset.mem_sym2_iff.mp h1 x hx)
          (Finset.mem_sym2_iff.mp he x hx)
      rw [if_pos he', hU0, Nat.sub_zero]
    have hV : G₁.verts \ remInner Us = G.verts \ remInner (U :: Us) := by
      rw [hG₁V]; ext x; simp only [remInner, Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    refine ⟨by rw [show removeAll G (U :: Us) = removeAll G₁ Us from rfl, ihV, hV], fun e => ?_⟩
    rw [show removeAll G (U :: Us) = removeAll G₁ Us from rfl, ihM e, hV, remCoreSum_congr hcores e]
    split_ifs with he
    · have he₁ : e ∈ (G.verts \ U.inner).sym2 := by
        rw [Finset.mem_sym2_iff] at he ⊢
        intro x hx
        have := he x hx
        simp only [remInner, Finset.mem_sdiff, Finset.mem_union, not_or] at this ⊢
        exact ⟨this.1, this.2.1⟩
      show (if e ∈ (G.verts \ U.inner).sym2 then G.mult e - (U.core G).mult e else 0) - _ = _
      rw [if_pos he₁, remCoreSum, Nat.sub_sub]
    · rfl

/-- At most one member of a disjoint family has a core bond at `e`; the sum is at most `G.mult e`. -/
theorem remCoreSum_le (G : UMultigraph V) (Us : List (SubObj V))
    (hdisj : Us.Pairwise fun U W => Disjoint U.atoms W.atoms) (e : Sym2 V) :
    remCoreSum G Us e ≤ G.mult e := by
  induction Us with
  | nil => simp [remCoreSum]
  | cons U Us ih =>
    rw [List.pairwise_cons] at hdisj
    simp only [remCoreSum]
    by_cases h0 : (U.core G).mult e = 0
    · rw [h0, zero_add]; exact ih hdisj.2
    · have hU := core_mult_supp G U h0
      have hrest : remCoreSum G Us e = 0 := by
        clear ih
        induction Us with
        | nil => rfl
        | cons W Ws ihW =>
          simp only [remCoreSum]
          have hW0 : (W.core G).mult e = 0 := by
            by_contra hne
            have h1 := core_mult_supp G W hne
            obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
            exact Finset.disjoint_left.mp (hdisj.1 W List.mem_cons_self) (Finset.mem_sym2_iff.mp hU x hx)
              (Finset.mem_sym2_iff.mp h1 x hx)
          rw [hW0, zero_add]
          exact ihW ⟨fun W' hW' => hdisj.1 W' (List.mem_cons_of_mem _ hW'), (List.pairwise_cons.mp hdisj.2).2⟩
      rw [hrest, add_zero]; exact core_mult_le G U e

theorem remCoreSum_eq_zero (G : UMultigraph V) {Us : List (SubObj V)} {x : V} (hx : ∀ U ∈ Us, x ∉ U.atoms)
    {e : Sym2 V} (hxe : x ∈ e) : remCoreSum G Us e = 0 := by
  induction Us with
  | nil => rfl
  | cons U Us ih =>
    simp only [remCoreSum]
    have h0 : (U.core G).mult e = 0 := by
      by_contra hne
      exact hx U List.mem_cons_self (Finset.mem_sym2_iff.mp (core_mult_supp G U hne) x hxe)
    rw [h0, zero_add, ih fun W hW => hx W (List.mem_cons_of_mem _ hW)]

/-! ## The added bonds -/

theorem rungAdds_mem {xm xp ym yp : V} {μ : Bool} {f : Sym2 V} (hf : f ∈ rungAdds xm xp ym yp μ) :
    ∃ x y, f = s(x, y) ∧ (x = xm ∨ x = ym) ∧ (y = xp ∨ y = yp) := by
  cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton] at hf <;> rcases hf with rfl | rfl
  · exact ⟨xm, xp, rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨ym, yp, rfl, Or.inr rfl, Or.inr rfl⟩
  · exact ⟨xm, yp, rfl, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨ym, xp, Sym2.eq_swap, Or.inr rfl, Or.inl rfl⟩

section Members

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {U : SubObj V} {μ : Bool}

/-- An all-out sub-object lies in one pole. -/
theorem atoms_one_pole (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U) (ha : a ∉ U.atoms)
    (hb : b ∉ U.atoms) : U.atoms ⊆ Km ∨ U.atoms ⊆ Kp := by
  classical
  have hconn : ConnOn (U.core G) U.atoms := by
    have := hU.2.2.2.2.2.2.2.2; unfold Connected at this; rwa [SubObj.core_verts] at this
  have hpole : ∀ x ∈ U.atoms, x ∈ Km ∨ x ∈ Kp := fun x hx =>
    hR.mem_poles (hU.atoms_subset hx) (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))
  have hk := hU.k₁_mem
  have key : ∀ K L : Finset V, (∀ u ∈ K, ∀ w ∈ L, G.mult s(u, w) = 0) → (∀ x ∈ U.atoms, x ∈ K ∨ x ∈ L) →
      U.k₁ ∈ K → U.atoms ⊆ K := by
    intro K L hKL hKLc hkK
    have hT := eq_of_closed' hconn (S := U.atoms.filter (· ∈ K)) (Finset.filter_subset _ _)
      ⟨U.k₁, Finset.mem_filter.mpr ⟨hk, hkK⟩⟩ (by
        intro u hu w hw hm
        obtain ⟨huS, huK⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_filter.mpr ⟨hw, ?_⟩
        rcases hKLc w hw with h | h
        · exact h
        · exact absurd (hKL u huK w h) (fun h0 => hm (Nat.le_zero.mp (h0 ▸ core_mult_le G U _))))
    intro x hx
    have : x ∈ U.atoms.filter (· ∈ K) := by rw [hT]; exact hx
    exact (Finset.mem_filter.mp this).2
  rcases hpole _ hk with h | h
  · exact Or.inl (key Km Kp hR.noBond hpole h)
  · exact Or.inr (key Kp Km (fun u hu w hw => by rw [Sym2.eq_swap]; exact hR.noBond w hw u hu)
      (fun x hx => (hpole x hx).symm) h)

/-- An all-out member keeps its core and its image. -/
theorem core_rungDel_allOut (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U) (ha : a ∉ U.atoms)
    (hb : b ∉ U.atoms) : U.phi a b = U ∧ (U.core (rungDel G a b xm xp ym yp μ)) = U.core G := by
  refine ⟨?_, ?_⟩
  · cases U
    simp only [SubObj.phi, SubObj.mk.injEq, and_true]
    rw [Finset.erase_eq_of_notMem ha, Finset.erase_eq_of_notMem hb]
  · apply core_congr
    intro e he
    have hab : ¬ (a ∈ e ∨ b ∈ e) := by
      rintro (h | h)
      · exact ha (Finset.mem_sym2_iff.mp he a h)
      · exact hb (Finset.mem_sym2_iff.mp he b h)
    rw [rungDel_mult, if_neg hab]
    have : (rungAdds xm xp ym yp μ).count e = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hf
      obtain ⟨x, y, rfl, hx, hy⟩ := rungAdds_mem hf
      have hxK : x ∈ Km := by rcases hx with rfl | rfl; exacts [hR.xm_mem, hR.ym_mem]
      have hyK : y ∈ Kp := by rcases hy with rfl | rfl; exacts [hR.xp_mem, hR.yp_mem]
      have hxU := Finset.mem_sym2_iff.mp he x (Sym2.mem_mk_left x y)
      have hyU := Finset.mem_sym2_iff.mp he y (Sym2.mem_mk_right x y)
      rcases atoms_one_pole hR hU ha hb with h | h
      · exact hR.not_mem_both (h hyU) hyK
      · exact hR.not_mem_both hxK (h hxU)
    rw [this, add_zero]

/-- An all-in member's image core gains exactly the added bonds. -/
theorem core_rungDel_allIn (hU : IsSubObjU G U) (hrails : xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms)
    {e : Sym2 V} (hae : a ∉ e) (hbe : b ∉ e) :
    ((U.phi a b).core (rungDel G a b xm xp ym yp μ)).mult e = (U.core G).mult e + (rungAdds xm xp ym yp μ).count e := by
  have hΦ : ∀ e : Sym2 V, a ∉ e → b ∉ e → (e ∈ ((U.atoms.erase a).erase b).sym2 ↔ e ∈ U.atoms.sym2) := by
    intro e ha hb
    simp only [Finset.mem_sym2_iff, Finset.mem_erase]
    constructor
    · intro h x hx; exact (h x hx).2.2
    · intro h x hx; exact ⟨fun h' => hb (h' ▸ hx), fun h' => ha (h' ▸ hx), h x hx⟩
  have hD : (rungDel G a b xm xp ym yp μ).mult e = G.mult e + (rungAdds xm xp ym yp μ).count e := by
    rw [rungDel_mult, if_neg (by rintro (h | h); exacts [hae h, hbe h])]
  have hA0 : e ∉ U.atoms.sym2 → (rungAdds xm xp ym yp μ).count e = 0 := by
    intro he
    apply Multiset.count_eq_zero.mpr
    intro hf
    obtain ⟨x, y, rfl, hx, hy⟩ := rungAdds_mem hf
    apply he
    rw [Finset.mem_sym2_iff]; intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · rcases hx with rfl | rfl; exacts [hrails.1, hrails.2.2.1]
    · rcases hy with rfl | rfl; exacts [hrails.2.1, hrails.2.2.2]
  have hIΦ : (induce (rungDel G a b xm xp ym yp μ) ((U.atoms.erase a).erase b)).mult e =
      (induce G U.atoms).mult e + (rungAdds xm xp ym yp μ).count e := by
    show (if e ∈ _ then _ else 0) = (if e ∈ _ then _ else 0) + _
    by_cases he : e ∈ U.atoms.sym2
    · rw [if_pos ((hΦ e hae hbe).mpr he), if_pos he, hD]
    · rw [if_neg (mt (hΦ e hae hbe).mp he), if_neg he, hA0 he]
  unfold SubObj.core SubObj.edges SubObj.phi
  simp only
  split
  · rename_i hh
    show (if e = s(U.k₁, U.k₂) then _ - 1 else _) = (if e = s(U.k₁, U.k₂) then _ - 1 else _) + _
    rw [hIΦ]
    split_ifs with hadj
    · have h1 : 1 ≤ (induce G U.atoms).mult e := by
        rw [hadj, induce_mult_of_mem G hU.k₁_mem hU.k₂_mem]
        exact Nat.one_le_iff_ne_zero.mpr (hU.2.1 hh)
      omega
    · rfl
  · exact hIΦ

end Members

theorem SubObj.inner_phi (U : SubObj V) (a b : V) : (U.phi a b).inner = (U.inner.erase a).erase b := by
  simp only [SubObj.inner, SubObj.phi]
  ext x; simp only [Finset.mem_erase]; tauto

/-- The core sums of the images: unchanged, plus the added bonds if a member contains the rung. -/
theorem remCoreSum_phi {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {μ : Bool}
    (hR : RungCore G a b xm xp ym yp Km Kp) {Us : List (SubObj V)}
    (hdisj : Us.Pairwise fun U W => Disjoint U.atoms W.atoms) (hU : ∀ U ∈ Us, IsSubObjU G U)
    (hcls : ∀ U ∈ Us, (a ∈ U.atoms ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms)) {e : Sym2 V} (hae : a ∉ e) (hbe : b ∉ e) :
    remCoreSum (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b) e =
      remCoreSum G Us e + (if ∃ U ∈ Us, a ∈ U.atoms then (rungAdds xm xp ym yp μ).count e else 0) := by
  induction Us with
  | nil => simp [remCoreSum]
  | cons U Us ih =>
    rw [List.pairwise_cons] at hdisj
    simp only [List.map_cons, remCoreSum]
    rw [ih hdisj.2 (fun W hW => hU W (List.mem_cons_of_mem _ hW)) (fun W hW => hcls W (List.mem_cons_of_mem _ hW))]
    rcases hcls U List.mem_cons_self with ⟨ha, hrails⟩ | ⟨ha, hb⟩
    · rw [core_rungDel_allIn (hU U List.mem_cons_self) hrails hae hbe]
      have hnone : ¬ ∃ W ∈ Us, a ∈ W.atoms := by
        rintro ⟨W, hW, haW⟩
        exact Finset.disjoint_left.mp (hdisj.1 W hW) ha haW
      rw [if_neg hnone, if_pos ⟨U, List.mem_cons_self, ha⟩]
      ring
    · rw [(core_rungDel_allOut (μ := μ) hR (hU U List.mem_cons_self) ha hb).1,
        (core_rungDel_allOut (μ := μ) hR (hU U List.mem_cons_self) ha hb).2]
      have hiff : (∃ W ∈ U :: Us, a ∈ W.atoms) ↔ ∃ W ∈ Us, a ∈ W.atoms := by
        constructor
        · rintro ⟨W, hW, haW⟩
          rcases List.mem_cons.mp hW with rfl | hW
          · exact absurd haW ha
          · exact ⟨W, hW, haW⟩
        · rintro ⟨W, hW, haW⟩; exact ⟨W, List.mem_cons_of_mem _ hW, haW⟩
      rw [if_congr hiff rfl rfl]
      ring

/-- **N2 Lemma 1.14(e)** (removal connectivity, sources' removal semantics). -/
theorem phiRemoval_holds : PhiRemovalStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp Us μ hB hl hR hmem hdisj hconn
  have hR' := hR.1
  have hRc := hR'.toCore
  have hUs : ∀ U ∈ Us, IsSubObjU G U := fun U hU => (hmem U hU).1
  have hcls0 : ∀ U ∈ Us, (a ∈ U.inner ∧ b ∈ U.inner ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧
      yp ∈ U.atoms) ∨ (a ∉ U.atoms ∧ b ∉ U.atoms) := by
    intro U hU
    obtain ⟨hU', h1, h2, h3, h4⟩ := hmem U hU
    exact phiAllInOut_holds G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hR hU' h1 h2 h3 h4
  have hcls : ∀ U ∈ Us, (a ∈ U.atoms ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms) := by
    intro U hU
    rcases hcls0 U hU with ⟨ha, -, h⟩ | h
    · exact Or.inl ⟨U.inner_subset ha, h⟩
    · exact Or.inr h
  have hDV : (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := hRc.verts_rungDel μ
  have hsubG : ∀ U ∈ Us, U.atoms ⊆ G.verts := fun U hU => (hUs U hU).atoms_subset
  have hsubD : ∀ W ∈ Us.map (fun U => U.phi a b), W.atoms ⊆ (rungDel G a b xm xp ym yp μ).verts := by
    intro W hW
    obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hW
    rw [hDV]; intro x hx
    simp only [SubObj.phi, Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hx.2.1, hsubG U hU hx.2.2⟩
  have hdisjΦ : (Us.map fun U => U.phi a b).Pairwise fun U W => Disjoint U.atoms W.atoms := by
    rw [List.pairwise_map]
    exact hdisj.imp fun h => Finset.disjoint_of_subset_left
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      (Finset.disjoint_of_subset_right ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) h)
  obtain ⟨hHV, hHM⟩ := removeAll_flat G Us hsubG hdisj
  obtain ⟨hH'V, hH'M⟩ := removeAll_flat _ _ hsubD hdisjΦ
  have hinnerΦ : remInner (Us.map fun U => U.phi a b) = ((remInner Us).erase a).erase b := by
    ext x
    rw [mem_remInner]
    simp only [Finset.mem_erase, mem_remInner, List.mem_map]
    constructor
    · rintro ⟨W, ⟨U, hU, rfl⟩, hx⟩
      rw [SubObj.inner_phi] at hx; simp only [Finset.mem_erase] at hx
      exact ⟨hx.1, hx.2.1, U, hU, hx.2.2⟩
    · rintro ⟨h1, h2, U, hU, hx⟩
      exact ⟨U.phi a b, ⟨U, hU, rfl⟩, by rw [SubObj.inner_phi]; simp [h1, h2, hx]⟩
  have hDm : ∀ e, a ∉ e → b ∉ e → (rungDel G a b xm xp ym yp μ).mult e =
      G.mult e + (rungAdds xm xp ym yp μ).count e := fun e ha hb => by
    rw [rungDel_mult, if_neg (by rintro (h | h); exacts [ha h, hb h])]
  by_cases hin : ∃ U ∈ Us, a ∈ U.atoms
  · -- one all-in member: the two removed graphs coincide
    obtain ⟨U₀, hU₀, haU₀⟩ := hin
    have hab : a ∈ U₀.inner ∧ b ∈ U₀.inner := by
      rcases hcls0 U₀ hU₀ with h | h
      · exact ⟨h.1, h.2.1⟩
      · exact absurd haU₀ h.1
    have haI : a ∈ remInner Us := mem_remInner.mpr ⟨U₀, hU₀, hab.1⟩
    have hbI : b ∈ remInner Us := mem_remInner.mpr ⟨U₀, hU₀, hab.2⟩
    have hVeq : (rungDel G a b xm xp ym yp μ).verts \ remInner (Us.map fun U => U.phi a b) =
        G.verts \ remInner Us := by
      rw [hDV, hinnerΦ]; ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hxb, hxa, hx⟩, hn⟩; exact ⟨hx, fun h => hn ⟨hxb, hxa, h⟩⟩
      · rintro ⟨hx, hn⟩
        exact ⟨⟨fun h => hn (h ▸ hbI), fun h => hn (h ▸ haI), hx⟩, fun h => hn h.2.2⟩
    have heq : removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b) = removeAll G Us := by
      apply ext
      · rw [hH'V, hHV, hVeq]
      · intro e
        rw [hH'M, hHM, hVeq]
        split_ifs with he
        · have hae : a ∉ e := fun h => (Finset.mem_sdiff.mp (Finset.mem_sym2_iff.mp he a h)).2 haI
          have hbe : b ∉ e := fun h => (Finset.mem_sdiff.mp (Finset.mem_sym2_iff.mp he b h)).2 hbI
          rw [hDm e hae hbe, remCoreSum_phi hRc hdisj hUs hcls hae hbe, if_pos ⟨U₀, hU₀, haU₀⟩,
            Nat.add_sub_add_right]
        · rfl
    rw [heq] at hconn; exact hconn
  · -- all members are all-out: lift connectivity through the rung
    have hout : ∀ U ∈ Us, a ∉ U.atoms ∧ b ∉ U.atoms := by
      intro U hU
      rcases hcls U hU with h | h
      · exact absurd ⟨U, hU, h.1⟩ hin
      · exact h
    have haI : a ∉ remInner Us := fun h => by
      obtain ⟨U, hU, hx⟩ := mem_remInner.mp h; exact (hout U hU).1 (U.inner_subset hx)
    have hbI : b ∉ remInner Us := fun h => by
      obtain ⟨U, hU, hx⟩ := mem_remInner.mp h; exact (hout U hU).2 (U.inner_subset hx)
    have hnotI : ∀ x w, w ∈ G.verts → G.mult s(x, w) ≠ 0 → (w = a ∨ w = b) → x ∉ remInner Us := by
      intro x w hw hm hwab hxI
      obtain ⟨U, hU, hxU⟩ := mem_remInner.mp hxI
      simp only [SubObj.inner, Finset.mem_erase] at hxU
      obtain ⟨-, -, hcl⟩ := (hUs U hU).closed_of_inner hB hxU.2.2 hxU.2.1 hxU.1
      have := hcl w hw hm
      rcases hwab with rfl | rfl
      · exact (hout U hU).1 this
      · exact (hout U hU).2 this
    have hm1 : ∀ {x y : V}, G.mult s(x, y) = 1 → G.mult s(y, x) ≠ 0 := fun h => by
      rw [Sym2.eq_swap, h]; omega
    have hxmI := hnotI xm a hR'.a_mem (hm1 hR'.a_xm) (Or.inl rfl)
    have hxpI := hnotI xp a hR'.a_mem (hm1 hR'.a_xp) (Or.inl rfl)
    have hymI := hnotI ym b hR'.b_mem (hm1 hR'.b_ym) (Or.inr rfl)
    have hypI := hnotI yp b hR'.b_mem (hm1 hR'.b_yp) (Or.inr rfl)
    have hxmV := (hRc.mem_verts (Or.inl hRc.xm_mem)).1
    have hxpV := (hRc.mem_verts (Or.inr hRc.xp_mem)).1
    have hymV := (hRc.mem_verts (Or.inl hRc.ym_mem)).1
    have hypV := (hRc.mem_verts (Or.inr hRc.yp_mem)).1
    -- bonds at `a`, `b` survive the removal
    have hHab : ∀ x w, (x = a ∨ x = b) → w ∈ G.verts \ remInner Us →
        (removeAll G Us).mult s(x, w) = G.mult s(x, w) := by
      intro x w hx hw
      have hxV : x ∈ G.verts \ remInner Us := by
        rcases hx with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨hR'.a_mem, haI⟩
        · exact Finset.mem_sdiff.mpr ⟨hR'.b_mem, hbI⟩
      rw [hHM, if_pos (by
        rw [Finset.mem_sym2_iff]; intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption)]
      have : remCoreSum G Us s(x, w) = 0 := by
        rcases hx with rfl | rfl
        · exact remCoreSum_eq_zero G (fun U hU => (hout U hU).1) (Sym2.mem_mk_left _ w)
        · exact remCoreSum_eq_zero G (fun U hU => (hout U hU).2) (Sym2.mem_mk_left _ w)
      rw [this, Nat.sub_zero]
    have hVH' : (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)).verts =
        ((G.verts \ remInner Us).erase a).erase b := by
      rw [hH'V, hDV, hinnerΦ]; ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
    -- bonds of the image graph come from `G ∖ ⋃ U` or are added bonds
    have hstep : ∀ u w, u ∈ (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)).verts →
        w ∈ (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)).verts →
        (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)).mult s(u, w) ≠ 0 →
        (removeAll G Us).mult s(u, w) ≠ 0 ∨ (rungAdds xm xp ym yp μ).count s(u, w) ≠ 0 := by
      intro u w hu hw hm
      rw [hVH'] at hu hw
      simp only [Finset.mem_erase, Finset.mem_sdiff] at hu hw
      have hae : a ∉ s(u, w) := by
        intro h; rcases Sym2.mem_iff.mp h with h | h
        exacts [hu.2.1 h.symm, hw.2.1 h.symm]
      have hbe : b ∉ s(u, w) := by
        intro h; rcases Sym2.mem_iff.mp h with h | h
        exacts [hu.1 h.symm, hw.1 h.symm]
      have hin' : s(u, w) ∈ (G.verts \ remInner Us).sym2 := by
        rw [Finset.mem_sym2_iff]; intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact Finset.mem_sdiff.mpr hu.2.2
        · exact Finset.mem_sdiff.mpr hw.2.2
      have hin'' : s(u, w) ∈ ((rungDel G a b xm xp ym yp μ).verts \
          remInner (Us.map fun U => U.phi a b)).sym2 := by
        rw [← hH'V, hVH', Finset.mem_sym2_iff]; intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · simp [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2]
        · simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]
      rw [hH'M, if_pos hin'', hDm _ hae hbe, remCoreSum_phi hRc hdisj hUs hcls hae hbe, if_neg hin,
        add_zero] at hm
      rw [hHM, if_pos hin']
      omega
    -- the closed-set argument
    apply connected_of_closed
    intro X hX hne hcl
    rw [hHV] at hX hcl ⊢
    have haV : a ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hR'.a_mem, haI⟩
    have hbV : b ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hR'.b_mem, hbI⟩
    have hxmV' : xm ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hxmV, hxmI⟩
    have hxpV' : xp ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hxpV, hxpI⟩
    have hymV' : ym ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hymV, hymI⟩
    have hypV' : yp ∈ G.verts \ remInner Us := Finset.mem_sdiff.mpr ⟨hypV, hypI⟩
    have hcl' : ∀ u ∈ X, ∀ w ∈ G.verts \ remInner Us, G.mult s(u, w) ≠ 0 → (u = a ∨ u = b) → w ∈ X := by
      intro u hu w hw hm hab
      exact hcl u hu w hw (by rw [hHab u w hab hw]; exact hm)
    have hab : a ∈ X ↔ b ∈ X := ⟨fun h => hcl' a h b hbV (by rw [hR'.mult_ab]; omega) (Or.inl rfl),
      fun h => hcl' b h a haV (by rw [Sym2.eq_swap, hR'.mult_ab]; omega) (Or.inr rfl)⟩
    have hrails : a ∈ X → xm ∈ X ∧ xp ∈ X ∧ ym ∈ X ∧ yp ∈ X := by
      intro ha
      have hb := hab.mp ha
      exact ⟨hcl' a ha xm hxmV' (by rw [hR'.a_xm]; omega) (Or.inl rfl),
        hcl' a ha xp hxpV' (by rw [hR'.a_xp]; omega) (Or.inl rfl),
        hcl' b hb ym hymV' (by rw [hR'.b_ym]; omega) (Or.inr rfl),
        hcl' b hb yp hypV' (by rw [hR'.b_yp]; omega) (Or.inr rfl)⟩
    have hback : ∀ x, (x = xm ∨ x = xp ∨ x = ym ∨ x = yp) → x ∈ X → a ∈ X := by
      rintro x (rfl | rfl | rfl | rfl) hx
      · exact hcl x hx a haV (by rw [Sym2.eq_swap, hHab a x (Or.inl rfl) hxmV', hR'.a_xm]; omega)
      · exact hcl x hx a haV (by rw [Sym2.eq_swap, hHab a x (Or.inl rfl) hxpV', hR'.a_xp]; omega)
      · exact hab.mpr (hcl x hx b hbV (by rw [Sym2.eq_swap, hHab b x (Or.inr rfl) hymV', hR'.b_ym]; omega))
      · exact hab.mpr (hcl x hx b hbV (by rw [Sym2.eq_swap, hHab b x (Or.inr rfl) hypV', hR'.b_yp]; omega))
    have hxma : xm ≠ a := (hRc.ne_of_mem (Or.inl hRc.xm_mem)).1
    have hxmb : xm ≠ b := (hRc.ne_of_mem (Or.inl hRc.xm_mem)).2
    set X' := (X.erase a).erase b with hX'
    have hX'V : X' ⊆ (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)).verts := by
      rw [hVH']; intro x hx
      simp only [hX', Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, hx.2.1, hX hx.2.2⟩
    have hne' : X'.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      by_cases hxab : x = a ∨ x = b
      · have ha : a ∈ X := by rcases hxab with rfl | rfl; exacts [hx, hab.mpr hx]
        exact ⟨xm, by simp [hX', hxma, hxmb, (hrails ha).1]⟩
      · exact ⟨x, by simp only [hX', Finset.mem_erase]
                     exact ⟨fun h => hxab (Or.inr h), fun h => hxab (Or.inl h), hx⟩⟩
    have hall := eq_of_closed' hconn hX'V hne' (by
      intro u hu w hw hm
      have huV := hX'V hu
      have hwV := hw
      simp only [hX', Finset.mem_erase] at hu
      rw [hVH'] at hwV
      simp only [Finset.mem_erase] at hwV
      simp only [hX', Finset.mem_erase]
      refine ⟨hwV.1, hwV.2.1, ?_⟩
      rcases hstep u w huV hw hm with h | h
      · exact hcl u hu.2.2 w hwV.2.2 h
      · obtain ⟨x, y, hxy, hx, hy⟩ := rungAdds_mem (Multiset.count_ne_zero.mp h)
        have haX : a ∈ X := by
          rcases Sym2.eq_iff.mp hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact hback u (by rcases hx with rfl | rfl <;> simp) hu.2.2
          · exact hback u (by rcases hy with rfl | rfl <;> simp) hu.2.2
        obtain ⟨h1, h2, h3, h4⟩ := hrails haX
        rcases Sym2.eq_iff.mp hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · rcases hy with rfl | rfl <;> assumption
        · rcases hx with rfl | rfl <;> assumption)
    apply Finset.Subset.antisymm hX
    intro v hv
    have hsub : ∀ y, y ≠ a → y ≠ b → y ∈ G.verts \ remInner Us → y ∈ X := by
      intro y h1 h2 h3
      have : y ∈ X' := by rw [hall, hVH']; simp [h1, h2, h3]
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
    have haX : a ∈ X := hback xm (Or.inl rfl) (hsub xm hxma hxmb hxmV')
    by_cases hva : v = a
    · exact hva ▸ haX
    by_cases hvb : v = b
    · exact hvb ▸ hab.mp haX
    exact hsub v hva hvb hv

end WaveTurbulence.TVine.Core
