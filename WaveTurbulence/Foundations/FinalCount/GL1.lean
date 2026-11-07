/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RunN
public import WaveTurbulence.Foundations.FinalCount.G3FinalE4
/-! **G3-LOWDEG (R48), part 1**: the standing hypothesis `SubHypL` (no `deg3`), the class-change state `betaSt`
(the cut of a degree-`2` `ε`-atom along both its bonds, TARGET Remark after `defcut`, with the isolated half deleted), and
the index drop `Good R → Good (R-1)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **The standing hypotheses of the LOW case** on `M_sub`: `SubHyp` without `3 ≤ deg` (atoms of degree `1, 2` allowed;
`deg_pos` excludes only the single-atom molecule of degree `0`, which is treated separately: `A ≤ 1`). Loops stay excluded
(they are handled by `unloop`, see GL loops, or by the exact smoothing of NOTES Q2(b)). -/
structure SubHypL (R : ℕ) (M₀ : Molecule V D₀) : Prop where
  bounds : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2
  count : M₀.bonds.card + R = 2 * M₀.atoms.card
  noloop : ∀ x, M₀.atom x ≠ M₀.atom (M₀.mate x)
  conn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b
  one_le : 1 ≤ R
  deg_pos : ∀ a ∈ M₀.atoms, 1 ≤ M₀.deg a

theorem SubHyp.toL (h : SubHyp R M₀) : SubHypL R M₀ where
  bounds := h.bounds
  count := h.count
  noloop := h.noloop
  conn := h.conn
  one_le := h.one_le
  deg_pos := fun a ha => by have := h.deg3 a ha; omega

theorem SubHypL.inv (h : SubHypL R M₀) : Inv.{_, _, _} R (St.init M₀) := by
  have hD := card_darts_eq_two_bonds M₀
  refine ⟨h.bounds, fun a ha _ => h.deg_pos a ha, fun a ha hne => absurd rfl hne, ?_, h.noloop⟩
  · show ∑ a ∈ M₀.atoms, (Cls.eps).base = _
    simp only [Cls.base, Finset.sum_const, smul_eq_mul]
    have := h.count
    have hD' : Fintype.card (St.init M₀).D = Fintype.card D₀ := rfl
    rw [hD']
    simp
    omega

theorem SubHypL.good (h : SubHypL R M₀) : Good R (St.init M₀) := ⟨h.inv, St.init_clean M₀⟩

theorem SubHypL.compBeta (h : SubHypL R M₀) : CompBeta (St.init M₀) := by
  intro a ha _
  have hg := h.good
  have hsum := hg.sum_contrib
  have hne : ∃ b ∈ M₀.atoms, contrib (St.init M₀) b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ b ∈ (St.init M₀).M.atoms, contrib (St.init M₀) b = 0 :=
      Finset.sum_eq_zero fun b hb => hcon b hb
    have h1 := h.one_le
    omega
  obtain ⟨b, hb, hb0⟩ := hne
  exact ⟨b, hb, h.conn a ha b hb, Or.inr hb0⟩

/-- The state after the cut of the degree-`2` `ε`-atom `v` along both its bonds, with the isolated half deleted:
same molecule, same darts, `v` is a `β`-atom. -/
noncomputable def St.betaSt (s : St.{u} V D₀) (v : V) : St.{u} V D₀ := s.withCls (Function.update s.cls v .beta)

theorem St.betaSt_cls (s : St.{u} V D₀) (v a : V) : (s.betaSt v).cls a = Function.update s.cls v .beta a := rfl
theorem St.betaSt_M (s : St.{u} V D₀) (v : V) : (s.betaSt v).M = s.M := rfl
theorem St.betaSt_D (s : St.{u} V D₀) (v : V) : (s.betaSt v).D = s.D := rfl
theorem St.betaSt_down (s : St.{u} V D₀) (v : V) : (s.betaSt v).down = s.down := rfl

section good
variable {s : St.{u} V D₀}

/-- **The index drops by one** under the cut of a degree-`2` `ε`-atom (the isolated half carries no dart and is deleted). -/
theorem Good.betaSt (hg : Good R s) {v : V} (hv : v ∈ s.M.atoms) (hε : s.cls v = .eps) (hd : s.M.deg v = 2) :
    1 ≤ R ∧ Good (R - 1) (s.betaSt v) := by
  have hc : contrib s v = 2 := by unfold contrib; rw [hε, hd]; simp [Cls.base]
  have hsum := hg.sum_contrib
  have hge : contrib s v ≤ ∑ a ∈ s.M.atoms, contrib s a :=
    Finset.single_le_sum (f := contrib s) (fun b hb => hg.contrib_nonneg hb) hv
  have hR : 1 ≤ R := by omega
  refine ⟨hR, ?_, ?_⟩
  · have hI := hg.1
    have hcl : ∀ a, (s.betaSt v).cls a = if a = v then Cls.beta else s.cls a := by
      intro a; by_cases h : a = v
      · rw [if_pos h, h]; simp [St.betaSt_cls]
      · rw [if_neg h]; simp [St.betaSt_cls, Function.update_of_ne h]
    refine ⟨hI.bounds, ?_, ?_, ?_, hI.noloop⟩
    · intro a ha hae
      by_cases h : a = v
      · rw [hcl, if_pos h] at hae; exact absurd hae (by simp)
      · rw [hcl, if_neg h] at hae; exact hI.eps a ha hae
    · intro a ha hne
      by_cases h : a = v
      · subst h
        refine ⟨by show s.M.deg a ≤ 2; omega, fun hg' => ?_, fun _ => by show 1 ≤ s.M.deg a; omega⟩
        rw [hcl, if_pos rfl] at hg'; exact absurd hg' (by simp)
      · rw [hcl, if_neg h] at hne ⊢
        exact hI.ab a ha hne
    · show ∑ a ∈ s.M.atoms, ((s.betaSt v).cls a).base = _
      have hrep := sum_replace (s := s.M.atoms) (f := fun a => (s.cls a).base)
        (g := fun a => ((s.betaSt v).cls a).base) hv (fun a _ ha' => by rw [hcl, if_neg ha'])
      have h1 : ((s.betaSt v).cls v).base = 2 := by rw [hcl, if_pos rfl]; rfl
      have h2 : (s.cls v).base = 4 := by rw [hε]; rfl
      rw [h1, h2] at hrep
      have := hI.phi
      show _ = (Fintype.card s.D : ℤ) + 2 * ((R - 1 : ℕ) : ℤ)
      have : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
      rw [this]
      linarith
  · intro a ha
    show (s.betaSt v).cls a ≠ .ghost
    rw [St.betaSt_cls]
    by_cases h : a = v
    · rw [h, Function.update_self]; simp
    · rw [Function.update_of_ne h]; exact hg.2 a ha
end good
end WaveTurbulence.FinalCountG3
