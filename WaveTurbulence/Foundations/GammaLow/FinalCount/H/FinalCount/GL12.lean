/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL12`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 12**: `Prop95ConclL` and `HRunL.prop95L`, the LOW analogue of `Prop95ConclN` / `HRunN.prop95N`
(TARGET `finalmol`).  Differences: `FinalStructL` (no `Flat`: `ε`-atoms of degree `1, 2` allowed), the chains clause is claimed
for components whose `ε`-atoms are all non-tame of degree `≥ 3`.  The proof is adapted from `HRunN.prop95N` (G3ConclN, sha256 in
COPIED-SHA256SUMS). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- No triple bonds at the end of the LOW run. -/
theorem HRunL.noTriple [Infinite V] {C : CollData M₀} {hf : HSt V D₀} (hr : HRunL C L γ η w κ (HSt.init M₀) hf)
    (hS : SubHypL R M₀) (obl : SubproOblG C L γ η w κ) (hT3 : TripleDesig C)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {R' : ℕ} (hg : Good R' hf.s) : NoTripleBond hf.s.M := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1c, a2, -, a3, -, a4, -, a5, -⟩ := hr
  have n1 : NoTripleBond h₁.s.M := noTripleBond_of_stopL hS h0 obl hT3 a1 n1c
  have e2 : EpsLe h₁.s h₂.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans (by
      obtain ⟨v, x₁, x₂, hD, rfl⟩ := hs.data
      exact EpsLe.betaSt v)) a2 (EpsLe.refl _)
  have e3 : EpsLe h₁.s h₃.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep2.step.epsLe) a3 e2
  have e4 : EpsLe h₁.s h₄.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep3.step.epsLe) a4 e3
  have e : EpsLe h₁.s hf.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.step.epsLe) a5 e4
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hda : 3 ≤ hf.s.M.deg a := (hcon.trans' (le_refl _)).trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ hf.s.M.deg b := by
    have : hf.s.M.bondsBetween a b = hf.s.M.bondsBetween b a := by
      unfold Molecule.bondsBetween
      simp only [Sym2.eq_swap]
    rw [this] at hcon
    exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : hf.s.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : hf.s.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a1, -⟩, ⟨b1, -⟩, hle⟩ := e a ha b hb hea heb
  exact absurd (hcon.trans hle) (by have := n1 a a1 b b1 hab; omega)

/-- **DH23 Prop 9.5 / TARGET `finalmol` for the LOW run (after Operations 1-4).** -/
theorem HRunL.prop95L [Infinite V] {C : CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunL C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (obl : SubproOblG C L γ η w κ)
    (hT3 : TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclL L γ η w κ Tm R hf := by
  obtain ⟨R', hR', hI⟩ := hr.inv (InvL.init hS h0)
  have hgR' := hI.good
  have hst : FinalStructL R hf.s := FinalStructL.of_good hR' hgR' hI.comp
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, hsgl, a5, n5⟩ := id hr
  have heps : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → Tm a ∨ ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG := by
    intro a ha hae
    by_cases hT : Tm a
    · exact Or.inl hT
    right
    intro x y hx hy hox hoy hxy
    have hrel := hI.rel
    obtain ⟨ha3, hae3⟩ := HRunN.eps_back a5 a ha hae
    have hnsg : ¬ SGat M₀ L γ η w κ a := hsgl a ha3 hae3
    have hx0 : M₀.atom (hf.s.down x) = a := by rw [hrel.eps x (by rw [hx]; exact hae), hx]
    have hy0 : M₀.atom (hf.s.down y) = a := by rw [hrel.eps y (by rw [hy]; exact hae), hy]
    have hox0 : M₀.out (hf.s.down x) = false := by rw [hrel.out]; exact hox
    have hoy0 : M₀.out (hf.s.down y) = true := by rw [hrel.out]; exact hoy
    have hxy0 : hf.s.down y ≠ M₀.mate (hf.s.down x) := by
      intro e
      have := hS.noloop (hf.s.down x)
      rw [← e, hx0, hy0] at this
      exact this rfl
    have haM : a ∈ M₀.atoms := hx0 ▸ M₀.atom_mem _
    have hgap : Molecule.gapAt L w (κ ∘ hf.s.down) x y = Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y) := rfl
    rw [hgap]
    by_contra hne
    have hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) = .SG ∨
        Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) = .ZG := by
      rcases hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (hf.s.down x) (hf.s.down y)) with _ | _ | _
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd hk hne
    rcases hk with hk | hk
    · exact hnsg ⟨hf.s.down x, hf.s.down y, hx0, hy0, hox0, hoy0, hxy0, hk⟩
    · rcases hdeg a haM _ _ hx0 hy0 hox0 hoy0 hxy0 hk with hsg | hTm
      · exact hnsg hsg
      · exact hT hTm
  exact
  { struct := hst
    label := by
      intro a ha ρ kp hc
      obtain ⟨hl, p, vis, hrec, hp, hkp, -, -⟩ := (hI.hrec.ok a ha).1 ρ kp hc
      refine ⟨hl, hkp, fun x y hx hy hox hoy _ => ?_⟩
      obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg a ha (by rw [hc]; simp) x y hx hy hox hoy
      rw [hrec] at hrec'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
      obtain ⟨rfl, rfl⟩ := hrec'
      unfold GapSim
      rw [norm_gap_of_pm hn]
      exact hp
    eps_LG := heps
    no_triple := hr.noTriple hS obl hT3 h0 hgR'
    cycles := hr.cycles hS obl h0
    chains := by
      intro a ha hev hne hex hT
      refine chainEnds_of hst.ab_deg (fun c hc => (hst.deg_range c hc).1) hI.bal ha
        (fun e he hce hae v₂ x₁ x₂ hcd => ?_) hev hne hex
      have hhT := hT e (Finset.mem_filter.2 ⟨he, hae⟩) hce
      exact n5 e he hhT.2 v₂ x₁ x₂ hcd
        (gapAt_ne_zero_of_LG ((heps e he hce).resolve_left hhT.1
          x₁ x₂ hcd.2.2.1 hcd.2.2.2.1 hcd.2.2.2.2.2.1 hcd.2.2.2.2.2.2 hcd.2.2.2.2.1))
    bal := hI.bal
    noloop := hI.noloop
    alpha_sg := by
      intro b hb ρ kp hc x y hx hy hox hoy
      obtain ⟨-, p, vis, hrec, -, -, -, hsg⟩ := (hI.hrec.ok b hb).1 ρ kp hc
      obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg b hb (by rw [hc]; simp) x y hx hy hox hoy
      rw [hrec] at hrec'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
      obtain ⟨rfl, rfl⟩ := hrec'
      rw [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_gap_of_pm hn)]
      exact hsg
    dartGap := by
      intro a ha hne x y hx hy hox hoy
      obtain ⟨p, vis, hrec, hn⟩ := hI.gap.dg a ha hne x y hx hy hox hoy
      exact ⟨pgap L w κ p, ⟨p, vis, hrec, rfl⟩, hn⟩
    noBetaCut := n5
    N1 := fun b hb hcb => hI.hrec.N1 hb hcb
    N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum =>
      hI.hrec.N2 hL hη h1 h2 hb c1 c2 cb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum }

end WaveTurbulence.GammaLow.FinalCount.H
