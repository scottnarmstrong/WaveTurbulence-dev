/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Chain
public import WaveTurbulence.Foundations.FinalCount.G3Final2
public import WaveTurbulence.Foundations.FinalCount.Prop95Statement
public import WaveTurbulence.Foundations.FinalCount.G3BalS
/-! **FINALCOUNT-G3: the `chains` conclusion of DH23 Prop 9.5** (L1807): in an even component with an `ε`-atom the
`α`/`β`-atoms form chains with two *distinct* `ε`-atoms at the ends.  Distinctness is `NoBetaCut` (an `ε`-atom with
both ends of a chain would admit a `β`-cut). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem mem_chainOf {s : St.{u} V D₀} {a c : V} :
    c ∈ chainOf s a ↔ c ∈ s.M.atoms ∧ s.cls c ≠ .eps ∧
      Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ s.cls y ≠ .eps) a c := by
  unfold chainOf; simp [Finset.mem_filter]

theorem chain_rtg {s : St.{u} V D₀} {a c : V} (h : Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ s.cls y ≠ .eps) a c)
    (ha : a ∈ chainOf s a) : Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ y ∈ chainOf s a) a c := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c' hab hs ih =>
    refine ih.tail ⟨hs.1, ?_⟩
    rw [mem_chainOf]
    refine ⟨?_, hs.2, hab.tail hs⟩
    obtain ⟨z, -, hz⟩ := hs.1
    exact hz ▸ s.M.atom_mem _

theorem chain_sc {s : St.{u} V D₀} {a c : V} (h : Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ s.cls y ≠ .eps) a c) :
    s.M.SameComponent a c := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hs ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hs.1)



theorem gapAt_ne_zero_of_LG {L γ η : ℝ} {r : Mom d} (h : Molecule.gapKind L γ η r = .LG) : r ≠ 0 := by
  intro h0
  unfold Molecule.gapKind at h
  simp [h0] at h

theorem not_alpha_of_closed {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {e v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData e v₂ x₁ x₂) (S : Finset V) (heS : e ∈ S) (hv₂S : v₂ ∉ S)
    (hcl : PClosed (M.cut e v₂ x₁ x₂) (fun a => a ∈ S)) : ¬ M.IsAlphaCut e v₂ x₁ x₂ := by
  intro h
  rw [isAlphaCut_iff M hcd] at h
  exact hv₂S ((PClosed.sc_iff (M.cut e v₂ x₁ x₂) (fun a => a ∈ S) hcl h).1 heS)

theorem chainEnds_of [Infinite V] {s : St.{u} V D₀}
    (hab : ∀ c ∈ s.M.atoms, s.cls c ≠ .eps → s.M.deg c ≤ 2) (hdr : ∀ c ∈ s.M.atoms, 1 ≤ s.M.deg c)
    (hB : BalS s) {a : V} (ha : a ∈ s.M.atoms)
    (hN : ∀ e ∈ s.M.atoms, s.cls e = .eps → s.M.SameComponent a e → ∀ v₂ x₁ x₂,
      s.M.IsCutData e v₂ x₁ x₂ → s.M.IsAlphaCut e v₂ x₁ x₂)
    (hev : EvenComp s.M a) (hne : s.cls a ≠ .eps)
    (hex : ∃ b ∈ compAtoms s.M a, s.cls b = .eps) : ChainEnds s a := by
  set C := chainOf s a with hC
  have haC : a ∈ C := mem_chainOf.2 ⟨ha, hne, Relation.ReflTransGen.refl⟩
  have hbal : ∀ c ∈ C, s.M.outdeg c = 1 ∧ s.M.indeg c = 1 := by
    intro c hc
    obtain ⟨hcm, hcne, hr⟩ := mem_chainOf.1 hc
    have h1 := hab c hcm hcne
    have h2 := hdr c hcm
    have h3 := hev c hcm (chain_sc hr)
    have h4 : s.M.deg c = 2 := by
      obtain ⟨k, hk⟩ := h3; omega
    exact hB.2 c hcm hcne h4
  have hconn : ∀ c ∈ C, Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ y ∈ C) a c :=
    fun c hc => chain_rtg (mem_chainOf.1 hc).2.2 haC
  have hexit : ∃ x, s.M.atom x ∈ C ∧ s.M.atom (s.M.mate x) ∉ C := by
    by_contra hno
    push_neg at hno
    have hcl : PClosed s.M (fun a => a ∈ C) := fun x hx => hno x hx
    obtain ⟨b, hb, hbe⟩ := hex
    have hbm := (Finset.mem_filter.1 hb)
    have := (PClosed.sc_iff s.M (fun a => a ∈ C) hcl hbm.2).1 haC
    exact (mem_chainOf.1 this).2.1 hbe
  obtain ⟨ho, hi⟩ := boundary_card s.M haC hbal hconn hexit
  obtain ⟨d₂, hd₂⟩ := Finset.card_eq_one.1 ho
  obtain ⟨d₁, hd₁⟩ := Finset.card_eq_one.1 hi
  have hd₂m : d₂ ∈ outBd s.M C := by rw [hd₂]; exact Finset.mem_singleton_self _
  have hd₁m : d₁ ∈ inBd s.M C := by rw [hd₁]; exact Finset.mem_singleton_self _
  simp only [outBd, inBd, Finset.mem_filter, Finset.mem_univ, true_and] at hd₂m hd₁m
  have hepsB : ∀ x, s.M.atom x ∈ C → s.M.atom (s.M.mate x) ∉ C → s.cls (s.M.atom (s.M.mate x)) = .eps := by
    intro x hx hx'
    by_contra hcne
    apply hx'
    obtain ⟨-, -, hr⟩ := mem_chainOf.1 hx
    exact mem_chainOf.2 ⟨s.M.atom_mem _, hcne, hr.tail ⟨⟨x, rfl, rfl⟩, hcne⟩⟩
  -- distinct ends
  have hdist : s.M.atom (s.M.mate d₁) ≠ s.M.atom (s.M.mate d₂) := by
    intro heq
    set e := s.M.atom (s.M.mate d₁) with he
    have heps : s.cls e = .eps := hepsB d₁ hd₁m.2.1 hd₁m.2.2
    have heC : e ∉ C := hd₁m.2.2
    have heM : e ∈ s.M.atoms := s.M.atom_mem _
    obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset (insert e s.M.atoms)
    have hv₂a : v₂ ∉ s.M.atoms := fun h => hv₂ (Finset.mem_insert_of_mem h)
    have hv₂e : v₂ ≠ e := fun h => hv₂ (h ▸ Finset.mem_insert_self _ _)
    set x₁ := s.M.mate d₂ with hx₁
    set x₂ := s.M.mate d₁ with hx₂
    have hcd : s.M.IsCutData e v₂ x₁ x₂ := by
      refine ⟨heM, hv₂a, heq.symm ▸ rfl, rfl, ?_, ?_, ?_⟩
      · intro h
        have h' : s.M.mate d₁ = d₂ := by rw [← hx₂, h, hx₁, s.M.mate_mate]
        have h2 : s.M.atom d₂ ∈ C := hd₂m.2.1
        exact heC (by show s.M.atom x₂ ∈ C; rw [hx₂, h']; exact h2)
      · rw [hx₁, s.M.out_mate, hd₂m.1]; rfl
      · rw [hx₂, s.M.out_mate, hd₁m.1]; rfl
    have hcl : PClosed (s.M.cut e v₂ x₁ x₂) (fun a => a ∈ insert e C) := by
      intro z hz
      have hz' : (s.M.cut e v₂ x₁ x₂).atom z ∈ insert e C := hz
      show (s.M.cut e v₂ x₁ x₂).atom (s.M.mate z) ∈ insert e C
      have hNa : ∀ y, (s.M.cut e v₂ x₁ x₂).atom y =
          if s.M.atom y = e ∧ y ≠ x₁ ∧ y ≠ x₂ then v₂ else s.M.atom y := fun y => rfl
      have hv₂S : v₂ ∉ insert e C := fun h =>
        (Finset.mem_insert.1 h).elim (fun h => hv₂e h) (fun h => hv₂a (mem_chainOf.1 h).1)
      have hCe : ∀ y, y ∈ C → y ≠ e := fun y hy h => heC (h ▸ hy)
      have hkeep : ∀ y, s.M.atom y ∈ C → (s.M.cut e v₂ x₁ x₂).atom y = s.M.atom y := by
        intro y hy
        rw [hNa, if_neg]
        exact fun h => hCe _ hy h.1
      have hd₂C : (s.M.cut e v₂ x₁ x₂).atom d₂ ∈ insert e C := by
        rw [hkeep d₂ hd₂m.2.1]; exact Finset.mem_insert_of_mem hd₂m.2.1
      have hd₁C : (s.M.cut e v₂ x₁ x₂).atom d₁ ∈ insert e C := by
        rw [hkeep d₁ hd₁m.2.1]; exact Finset.mem_insert_of_mem hd₁m.2.1
      have hx₁N : (s.M.cut e v₂ x₁ x₂).atom x₁ = e := by
        rw [hNa, if_neg (fun h => h.2.1 rfl)]; exact heq.symm
      have hx₂N : (s.M.cut e v₂ x₁ x₂).atom x₂ = e := by
        rw [hNa, if_neg (fun h => h.2.2 rfl)]
      by_cases hmv : s.M.atom z = e ∧ z ≠ x₁ ∧ z ≠ x₂
      · rw [hNa, if_pos hmv] at hz'; exact absurd hz' hv₂S
      · rw [hNa, if_neg hmv] at hz'
        rcases Finset.mem_insert.1 hz' with hA | hB
        · have : z = x₁ ∨ z = x₂ := by
            by_contra hn
            push_neg at hn
            exact hmv ⟨hA, hn.1, hn.2⟩
          rcases this with rfl | rfl
          · rw [hx₁, s.M.mate_mate]; exact hd₂C
          · rw [hx₂, s.M.mate_mate]; exact hd₁C
        · by_cases hm : s.M.atom (s.M.mate z) ∈ C
          · rw [hkeep _ hm]; exact Finset.mem_insert_of_mem hm
          · by_cases hoz : s.M.out z = true
            · have hzm : z ∈ outBd s.M C := by simp [outBd, hoz, hB, hm]
              rw [hd₂] at hzm
              rw [Finset.mem_singleton.1 hzm, ← hx₁, hx₁N]; exact Finset.mem_insert_self _ _
            · have hoz' : s.M.out z = false := by simpa using hoz
              have hzm : z ∈ inBd s.M C := by simp [inBd, hoz', hB, hm]
              rw [hd₁] at hzm
              rw [Finset.mem_singleton.1 hzm, ← hx₂, hx₂N]; exact Finset.mem_insert_self _ _
    exact not_alpha_of_closed hcd (insert e C) (Finset.mem_insert_self _ _)
      (fun h => (Finset.mem_insert.1 h).elim (fun h => hv₂e h) (fun h => hv₂a (mem_chainOf.1 h).1)) hcl
      (hN e heM heps (Relation.EqvGen.trans _ _ _ (chain_sc (mem_chainOf.1 hd₁m.2.1).2.2)
        (Relation.EqvGen.rel _ _ ⟨d₁, rfl, rfl⟩)) v₂ x₁ x₂ hcd)
  refine ⟨d₁, d₂, ?_, hd₁m.2.1, hd₂m.2.1, hepsB d₁ hd₁m.2.1 hd₁m.2.2, hepsB d₂ hd₂m.2.1 hd₂m.2.2, hdist, ?_⟩
  · intro h; rw [h] at hd₁m; rw [hd₁m.1] at hd₂m; exact absurd hd₂m.1 (by simp)
  · intro e he1 he2
    have he1 : s.M.atom e ∈ C := he1
    have he2 : s.M.atom (s.M.mate e) ∉ C := he2
    by_cases hoe : s.M.out e = true
    · right
      have : e ∈ outBd s.M C := by simp [outBd, hoe, he1, he2]
      rw [hd₂] at this; exact Finset.mem_singleton.1 this
    · left
      have hoe' : s.M.out e = false := by simpa using hoe
      have : e ∈ inBd s.M C := by simp [inBd, hoe', he1, he2]
      rw [hd₁] at this; exact Finset.mem_singleton.1 this

end WaveTurbulence.FinalCountG3
