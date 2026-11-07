/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Final1
public import WaveTurbulence.Foundations.FinalCount.CutRank
/-! **FINALCOUNT-G3**: the component invariant `CompBeta` (every non-ghost atom lies in a component that has a
`β`-atom or an atom of odd degree), preserved by cuts and by the removal of components. This gives "each even
component has at least one `β`-atom" (DH23 L1811, proof L1815: "Such a component can only be formed after a
`β`-cut"). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {D₀ : Type*}

section cutsc
variable {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}

/-- `a` lies in the component of `v` or of `v₂` after the cut. -/
def NearCut (M : Molecule V D) (v v₂ : V) (x₁ x₂ : D) (a : V) : Prop :=
  (M.cut v v₂ x₁ x₂).SameComponent a v ∨ (M.cut v v₂ x₁ x₂).SameComponent a v₂

theorem cut_adj_split (hcd : M.IsCutData v v₂ x₁ x₂) {x y : V} (h : M.Adj x y) :
    (M.cut v v₂ x₁ x₂).SameComponent x y ∨ (NearCut M v v₂ x₁ x₂ x ∧ NearCut M v v₂ x₁ x₂ y) := by
  obtain ⟨z, hz1, hz2⟩ := h
  have hp : (M.cut v v₂ x₁ x₂).atom z = x ∨ (x = v ∧ (M.cut v v₂ x₁ x₂).atom z = v₂) := by
    rw [cut_atom]; split_ifs with h1
    · right; exact ⟨hz1.symm.trans h1.1, rfl⟩
    · left; exact hz1
  have hq : (M.cut v v₂ x₁ x₂).atom (M.mate z) = y ∨ (y = v ∧ (M.cut v v₂ x₁ x₂).atom (M.mate z) = v₂) := by
    rw [cut_atom]; split_ifs with h1
    · right; exact ⟨hz2.symm.trans h1.1, rfl⟩
    · left; exact hz2
  have hadj : (M.cut v v₂ x₁ x₂).Adj ((M.cut v v₂ x₁ x₂).atom z) ((M.cut v v₂ x₁ x₂).atom (M.mate z)) :=
    ⟨z, rfl, rfl⟩
  have hsc := fun a b (h : (M.cut v v₂ x₁ x₂).Adj a b) =>
    (Relation.EqvGen.rel _ _ h : (M.cut v v₂ x₁ x₂).SameComponent a b)
  have refl := fun a => (Relation.EqvGen.refl a : (M.cut v v₂ x₁ x₂).SameComponent a a)
  have symm := fun {a b} (h : (M.cut v v₂ x₁ x₂).SameComponent a b) =>
    (Relation.EqvGen.symm _ _ h : (M.cut v v₂ x₁ x₂).SameComponent b a)
  rcases hp with hp | ⟨rfl, hp⟩ <;> rcases hq with hq | ⟨rfl, hq⟩
  · left; rw [hp, hq] at hadj; exact hsc _ _ hadj
  · right; rw [hp, hq] at hadj
    exact ⟨Or.inr (hsc _ _ hadj), Or.inl (refl _)⟩
  · right; rw [hp, hq] at hadj
    exact ⟨Or.inl (refl _), Or.inr (symm (hsc _ _ hadj))⟩
  · right; exact ⟨Or.inl (refl _), Or.inl (refl _)⟩

theorem nearCut_trans {a b : V} (h : (M.cut v v₂ x₁ x₂).SameComponent a b) (hb : NearCut M v v₂ x₁ x₂ b) :
    NearCut M v v₂ x₁ x₂ a := by
  rcases hb with hb | hb
  · exact Or.inl (Relation.EqvGen.trans _ _ _ h hb)
  · exact Or.inr (Relation.EqvGen.trans _ _ _ h hb)

theorem nearCut_symm {a b : V} (h : (M.cut v v₂ x₁ x₂).SameComponent a b) (ha : NearCut M v v₂ x₁ x₂ a) :
    NearCut M v v₂ x₁ x₂ b :=
  nearCut_trans (Relation.EqvGen.symm _ _ h) ha

theorem cut_sc_split (hcd : M.IsCutData v v₂ x₁ x₂) {a b : V} (h : M.SameComponent a b) :
    (M.cut v v₂ x₁ x₂).SameComponent a b ∨ (NearCut M v v₂ x₁ x₂ a ∧ NearCut M v v₂ x₁ x₂ b) := by
  induction h with
  | rel x y hr => exact cut_adj_split hcd hr
  | refl x => exact Or.inl (Relation.EqvGen.refl x)
  | symm x y _ ih =>
    rcases ih with h | ⟨h1, h2⟩
    · exact Or.inl (Relation.EqvGen.symm _ _ h)
    · exact Or.inr ⟨h2, h1⟩
  | trans x y z _ _ ih1 ih2 =>
    rcases ih1 with h1 | ⟨h1, h1'⟩ <;> rcases ih2 with h2 | ⟨h2, h2'⟩
    · exact Or.inl (Relation.EqvGen.trans _ _ _ h1 h2)
    · exact Or.inr ⟨nearCut_trans h1 h2, h2'⟩
    · exact Or.inr ⟨h1, nearCut_symm h2 h1'⟩
    · exact Or.inr ⟨h1, h2'⟩

/-- An isolated atom is alone in its component. -/
theorem sc_isolated (N : Molecule V D) {u : V} (hu : N.deg u = 0) {x : V} (h : N.SameComponent x u) : x = u := by
  have hno : ∀ y, ¬ N.Adj u y ∧ ¬ N.Adj y u := by
    intro y
    have : N.dartsAt u = ∅ := Finset.card_eq_zero.1 hu
    constructor
    · rintro ⟨z, hz, _⟩
      have : z ∈ N.dartsAt u := (mem_dartsAt N u z).2 hz
      simp_all
    · rintro ⟨z, _, hz⟩
      have hm : N.mate z ∈ N.dartsAt u := (mem_dartsAt N u _).2 hz
      simp_all
  have key : ∀ p q, N.SameComponent p q → (p = q ∨ (p ≠ u ∧ q ≠ u)) := by
    intro p q hpq
    induction hpq with
    | rel a b hr =>
      right; refine ⟨?_, ?_⟩
      · rintro rfl; exact (hno b).1 hr
      · rintro rfl; exact (hno a).2 hr
    | refl a => left; rfl
    | symm a b _ ih => rcases ih with h | ⟨h1, h2⟩; exact Or.inl h.symm; exact Or.inr ⟨h2, h1⟩
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨h1, h1'⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨h2, h2'⟩
        · exact Or.inr ⟨h1, h1'⟩
        · exact Or.inr ⟨h1, h2'⟩
  rcases key x u h with h1 | ⟨_, h2⟩
  · exact h1
  · exact absurd rfl h2

end cutsc


/-- Every non-ghost atom lies in a component with a `β`-atom or an *imperfect* atom (`contrib ≠ 0`: an `ε`-atom of
degree `≠ 4` or an `α`/`β`-atom of degree `≠ 2`). So a perfect component contains a `β`-atom (TARGET `finalmol`). -/
def CompBeta (s : St.{u} V D₀) : Prop :=
  ∀ a ∈ s.M.atoms, s.cls a ≠ .ghost →
    ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ (s.cls b = .beta ∨ contrib s b ≠ 0)

section cutst
variable {s : St.{u} V D₀} {v v₂ : V} {x₁ x₂ : s.D}

theorem cutSt_cls_v (c₁ c₂ : Cls) (h : v₂ ≠ v) : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls v = c₁ := by
  show Function.update (Function.update s.cls v c₁) v₂ c₂ v = c₁
  rw [Function.update_of_ne h.symm, Function.update_self]

theorem cutSt_cls_v₂ (c₁ c₂ : Cls) : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls v₂ = c₂ := by
  show Function.update (Function.update s.cls v c₁) v₂ c₂ v₂ = c₂
  rw [Function.update_self]

theorem cutSt_cls_other (c₁ c₂ : Cls) {a : V} (h1 : a ≠ v) (h2 : a ≠ v₂) :
    (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = s.cls a := by
  show Function.update (Function.update s.cls v c₁) v₂ c₂ a = s.cls a
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem contrib_cutSt_other (c₁ c₂ : Cls) {a : V} (hcd : s.M.IsCutData v v₂ x₁ x₂) (h1 : a ≠ v) (h2 : a ≠ v₂) :
    contrib (s.cutSt v v₂ x₁ x₂ c₁ c₂) a = contrib s a := by
  unfold contrib
  rw [cutSt_cls_other c₁ c₂ h1 h2]
  show _ - (((s.M.cut v v₂ x₁ x₂).deg a : ℕ) : ℤ) = _
  rw [cut_deg_other hcd h1 h2]

theorem CompBeta.cutβ (hC : CompBeta s) (hcd : s.M.IsCutData v v₂ x₁ x₂) (c₂ : Cls)
    (h₂ : c₂ = .beta ∨ (c₂ = .ghost ∧ s.M.deg v = 2)) :
    CompBeta (s.cutSt v v₂ x₁ x₂ .beta c₂) := by
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hcd.1)
  intro a ha hg
  have ha' : a ∈ insert v₂ s.M.atoms := ha
  have hvN : v ∈ (s.cutSt v v₂ x₁ x₂ .beta c₂).M.atoms := Finset.mem_insert_of_mem hcd.1
  by_cases h1 : a = v₂
  · subst h1
    rw [cutSt_cls_v₂] at hg
    have : c₂ = .beta := by rcases h₂ with h | h; exact h; exact absurd h.1 hg
    refine ⟨a, ha, Relation.EqvGen.refl _, Or.inl ?_⟩
    rw [cutSt_cls_v₂, this]
  · by_cases h2 : a = v
    · subst h2
      exact ⟨a, hvN, Relation.EqvGen.refl _, Or.inl (cutSt_cls_v _ _ hne)⟩
    · have haM : a ∈ s.M.atoms := (Finset.mem_insert.1 ha').resolve_left h1
      obtain ⟨b, hb, hab, hprop⟩ := hC a haM (by rwa [cutSt_cls_other _ _ h2 h1] at hg)
      have hb2 : b ≠ v₂ := fun e => hv₂ (e ▸ hb)
      rcases cut_sc_split hcd hab with h | ⟨hn, _⟩
      · by_cases hbv : b = v
        · subst hbv
          exact ⟨b, hvN, h, Or.inl (cutSt_cls_v _ _ hne)⟩
        · refine ⟨b, Finset.mem_insert_of_mem hb, h, ?_⟩
          rw [cutSt_cls_other _ _ hbv hb2, contrib_cutSt_other _ _ hcd hbv hb2]; exact hprop
      · rcases hn with hn | hn
        · exact ⟨v, hvN, hn, Or.inl (cutSt_cls_v _ _ hne)⟩
        · rcases h₂ with h | ⟨h, hd⟩
          · exact ⟨v₂, Finset.mem_insert_self _ _, hn, Or.inl (by rw [cutSt_cls_v₂, h])⟩
          · exfalso
            have hdeg0 : (s.M.cut v v₂ x₁ x₂).deg v₂ = 0 := by
              have := cut_deg_v₂ hcd; omega
            exact h1 (sc_isolated _ hdeg0 hn)

theorem CompBeta.cutα (hC : CompBeta s) (hcd : s.M.IsCutData v v₂ x₁ x₂) (c : Cls) (hc : c.IsAB)
    (hε : s.cls v = .eps) (hα : (s.M.cut v v₂ x₁ x₂).SameComponent v v₂) (h3 : 3 ≤ s.M.deg v) :
    CompBeta (s.cutSt v v₂ x₁ x₂ c c) := by
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hcd.1)
  have hdeg2 := cut_deg_v₂ hcd
  have hvN : v ∈ (s.cutSt v v₂ x₁ x₂ c c).M.atoms := Finset.mem_insert_of_mem hcd.1
  have hv₂N : v₂ ∈ (s.cutSt v v₂ x₁ x₂ c c).M.atoms := Finset.mem_insert_self _ _
  -- all M-connections survive
  have hsc : ∀ {x y : V}, s.M.SameComponent x y → (s.M.cut v v₂ x₁ x₂).SameComponent x y := by
    intro x y h
    rcases cut_sc_split hcd h with h | ⟨hx, hy⟩
    · exact h
    · have hxv : (s.M.cut v v₂ x₁ x₂).SameComponent x v := by
        rcases hx with hx | hx
        · exact hx
        · exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ hα)
      have hyv : (s.M.cut v v₂ x₁ x₂).SameComponent y v := by
        rcases hy with hy | hy
        · exact hy
        · exact Relation.EqvGen.trans _ _ _ hy (Relation.EqvGen.symm _ _ hα)
      exact Relation.EqvGen.trans _ _ _ hxv (Relation.EqvGen.symm _ _ hyv)
  have hwit : ∀ a ∈ s.M.atoms, s.cls a ≠ .ghost →
      ∃ b ∈ (s.cutSt v v₂ x₁ x₂ c c).M.atoms, (s.cutSt v v₂ x₁ x₂ c c).M.SameComponent a b ∧
        ((s.cutSt v v₂ x₁ x₂ c c).cls b = .beta ∨ contrib (s.cutSt v v₂ x₁ x₂ c c) b ≠ 0) := by
    intro a haM hg
    obtain ⟨b, hb, hab, hprop⟩ := hC a haM hg
    have hb2 : b ≠ v₂ := fun e => hv₂ (e ▸ hb)
    have hN := hsc hab
    by_cases hbv : b = v
    · subst hbv
      have hodd : contrib s b ≠ 0 := by
        rcases hprop with h | h
        · rw [hε] at h; exact absurd h (by simp)
        · exact h
      refine ⟨v₂, hv₂N, Relation.EqvGen.trans _ _ _ hN hα, Or.inr ?_⟩
      have hcb := Cls.base_eq_two hc
      unfold contrib at hodd ⊢
      rw [cutSt_cls_v₂, hε] at *
      show c.base - (((s.M.cut b v₂ x₁ x₂).deg v₂ : ℕ) : ℤ) ≠ 0
      simp only [Cls.base] at hodd
      omega
    · refine ⟨b, Finset.mem_insert_of_mem hb, hN, ?_⟩
      rw [cutSt_cls_other _ _ hbv hb2, contrib_cutSt_other _ _ hcd hbv hb2]; exact hprop
  intro a ha hg
  have ha' : a ∈ insert v₂ s.M.atoms := ha
  by_cases h1 : a = v₂
  · subst h1
    obtain ⟨b, hb, hvb, hprop⟩ := hwit v hcd.1 (by rw [hε]; simp)
    exact ⟨b, hb, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hα) hvb, hprop⟩
  · exact hwit a ((Finset.mem_insert.1 ha').resolve_left h1)
      (by by_cases h2 : a = v
          · subst h2; rw [hε]; simp
          · rwa [cutSt_cls_other _ _ h2 h1] at hg)

end cutst

theorem CompBeta.delSt {s : St.{u} V D₀} (hC : CompBeta s) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) :
    CompBeta (s.delSt P h) := by
  intro a ha hg
  obtain ⟨haM, haP⟩ := Finset.mem_filter.1 (show a ∈ s.M.atoms.filter P from ha)
  obtain ⟨b, hb, hab, hprop⟩ := hC a haM hg
  have hbP : P b := (PClosed.sc_iff s.M P h hab).1 haP
  refine ⟨b, Finset.mem_filter.2 ⟨hb, hbP⟩, restrictP_sc_of s.M P h hab haP, ?_⟩
  show (s.cls b = .beta) ∨ contrib (s.delSt P h) b ≠ 0
  have : contrib (s.delSt P h) b = contrib s b := by
    unfold contrib
    show _ - (((restrictP s.M P h).deg b : ℕ) : ℤ) = _
    rw [restrictP_deg s.M P h hbP]; rfl
  rw [this]; exact hprop

theorem CompBeta.withCls {s : St.{u} V D₀} (hC : CompBeta s) (c : V → Cls)
    (hagree : ∀ a ∈ s.M.atoms, (c a = .ghost ↔ s.cls a = .ghost))
    (hbase : ∀ a ∈ s.M.atoms, (c a).base = (s.cls a).base)
    (hpart : ∀ b ∈ s.M.atoms, s.cls b = .beta → c b ≠ .beta →
      ∃ b' ∈ s.M.atoms, s.M.SameComponent b b' ∧ c b' = .beta) :
    CompBeta (s.withCls c) := by
  intro a ha hg
  have hg' : s.cls a ≠ .ghost := fun e => hg ((hagree a ha).2 e)
  obtain ⟨b, hb, hab, hprop⟩ := hC a ha hg'
  by_cases hcb : c b = .beta
  · exact ⟨b, hb, hab, Or.inl hcb⟩
  · rcases hprop with h | h
    · obtain ⟨b', hb', hbb', hc'⟩ := hpart b hb h hcb
      exact ⟨b', hb', Relation.EqvGen.trans _ _ _ hab hbb', Or.inl hc'⟩
    · refine ⟨b, hb, hab, Or.inr ?_⟩
      have : contrib (s.withCls c) b = contrib s b := by
        unfold contrib
        show (c b).base - _ = _
        rw [hbase b hb]; rfl
      rw [this]; exact h

end WaveTurbulence.FinalCountG3
