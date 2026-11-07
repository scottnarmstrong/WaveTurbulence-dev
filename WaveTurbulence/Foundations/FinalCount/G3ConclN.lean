/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CycN
public import WaveTurbulence.Foundations.FinalCount.G3TripleThm
public import WaveTurbulence.Foundations.FinalCount.G3FinalE4
/-! **FINALCOUNT-G3 (R29 items 2-3): `Prop95ConclN`**, the conclusions of DH23 Prop 9.5 / TARGET `finalmol` for the state after
Operations 1--4 (`HRunN`), and `HRunN.prop95N`.  Differences from `Prop95ConclE` (t = 0): `ε`-atoms are LG or tame (`Tm`, TARGET
`subpro` (3)); `chains` only for components without tame atoms (A2); `noBetaCut` is the nonzero-gap `NoBetaCut`;
`cycles` uses `NoEligibleTriangle`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

structure Prop95ConclN (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Tm : V → Prop) (R : ℕ) (hf : HSt V D₀) : Prop where
  struct : FinalStructE R 0 hf.s
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  /-- every `ε`-atom is LG, or tame -/
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → Tm a ∨ ∀ x y : hf.s.D, hf.s.M.atom x = a →
    hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  no_triple : NoTripleBond hf.s.M
  cycles : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) →
    CycleShape hf.s a
  /-- chains, for even components without tame atoms (A2) -/
  chains : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps →
    (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
    (∀ e ∈ compAtoms hf.s.M a, hf.s.cls e = .eps → ¬ Tm e) → ChainEnds hf.s a
  bal : BalS hf.s
  noloop : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)
  alpha_sg : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
    hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG
  dartGap : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → ∃ g, AtomGap L w κ hf a g ∧
      (Molecule.gapAt L w (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L w (κ ∘ hf.s.down) x y = -g)
  noBetaCut : NoBetaCut L w κ hf.s
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖


/-- No triple bonds at the end of a run: Step 1 stops at `NoTripleCut`, so `NoTripleBond` holds after it (R37(b), THEOREM
`noTripleBond_of_stop`); later steps only cut. -/
theorem HRunN.noTriple [Infinite V] {C : CollData M₀} {hf : HSt V D₀} (hr : HRunN C L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀) (obl : SubproOblG C L γ η w κ) (hT3 : TripleDesig C)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {R' : ℕ} (hg : Good R' hf.s) : NoTripleBond hf.s.M := by
  obtain ⟨h₁, h₂, h₃, a1, n1c, a2, -, a3, -, a4, -⟩ := hr
  have n1 : NoTripleBond h₁.s.M := noTripleBond_of_stop hS h0 obl hT3 a1 n1c
  have e2 : EpsLe h₁.s h₂.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep2.step.epsLe) a2 (EpsLe.refl _)
  have e3 : EpsLe h₁.s h₃.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.toHStep3.step.epsLe) a3 e2
  have e : EpsLe h₁.s hf.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.step.epsLe) a4 e3
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

/-- `ε`-atoms of the end of Step 4 were `ε`-atoms at its start. -/
theorem HRunN.eps_back {h₃ hf : HSt V D₀} (a4 : Relation.ReflTransGen (HStep4 L w κ) h₃ hf) :
    ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → a ∈ h₃.s.M.atoms ∧ h₃.s.cls a = .eps := by
  induction a4 with
  | refl => exact fun a ha hae => ⟨ha, hae⟩
  | tail hab hbc ih =>
    intro a ha hae
    obtain ⟨h1, h2⟩ := step4_eps hbc.step ha hae
    exact ih a h1 h2

/-- **DH23 Prop 9.5 / TARGET `finalmol` for the state after Operations 1--4.** -/
theorem HRunN.prop95N [Infinite V] {C : CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunN C L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀) (obl : SubproOblG C L γ η w κ)
    (hT3 : TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclN L γ η w κ Tm R hf := by
  have hI := hr.invN (InvE.init hS h0)
  obtain ⟨R', hR', hgR'⟩ := hI.good
  have hst : FinalStructE R 0 hf.s := FinalStructE.of_inv hI.good0 hR' hgR' hI.comp hI.flat
  obtain ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, hsgl, a4, n4⟩ := id hr
  have heps : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → Tm a ∨ ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG := by
    intro a ha hae
    by_cases hT : Tm a
    · exact Or.inl hT
    right
    intro x y hx hy hox hoy hxy
    have hrel := hI.rel
    obtain ⟨ha3, hae3⟩ := HRunN.eps_back a4 a ha hae
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
        (fun e he hce hae v₂ x₁ x₂ hcd => n4 e he (hst.eps_deg rfl e he hce) v₂ x₁ x₂ hcd
          (gapAt_ne_zero_of_LG ((heps e he hce).resolve_left (hT e (Finset.mem_filter.2 ⟨he, hae⟩) hce)
            x₁ x₂ hcd.2.2.1 hcd.2.2.2.1 hcd.2.2.2.2.2.1 hcd.2.2.2.2.2.2 hcd.2.2.2.2.1))) hev hne hex
    bal := hI.bal
    noloop := hI.noloop
    alpha_sg := hI.alpha_sg
    dartGap := by
      intro a ha hne x y hx hy hox hoy
      obtain ⟨p, vis, hrec, hn⟩ := hI.gap.dg a ha hne x y hx hy hox hoy
      exact ⟨pgap L w κ p, ⟨p, vis, hrec, rfl⟩, hn⟩
    noBetaCut := n4
    N1 := fun b hb hcb => hI.hrec.N1 hb hcb
    N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum =>
      hI.hrec.N2 hL hη h1 h2 hb c1 c2 cb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum }


/-- **`Prop95ConclAt`** (the form consumed by the `FinalShape`/`FinalDec` mapping) for the state after Operations 1--4. -/
theorem HRunN.prop95At [Infinite V] {C : CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunN C L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀) (obl : SubproOblG C L γ η w κ)
    (hT3 : TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclAt L γ η w κ R hf Tm := by
  have hI := hr.invN (InvE.init hS h0)
  have hN := hr.prop95N hS obl hT3 hdeg h0
  have hst : FinalStruct R hf.s := FinalStruct.of_good (hI.good0 rfl) hI.comp (hI.flat rfl)
  exact
  { struct := hst
    label := hN.label
    eps_LG := fun a ha hae hT => (hN.eps_LG a ha hae).resolve_left (hT a ha (Relation.EqvGen.refl _) hae)
    no_triple := hN.no_triple
    cycles := hN.cycles
    chains := fun a ha hev hne hex hT => hN.chains a ha hev hne hex (fun e he hce => hT e (Finset.mem_filter.1 he).1
      (Finset.mem_filter.1 he).2 hce)
    bal := ⟨hI.bal.1, fun a ha hd => hI.bal.2 a ha (fun he => by have := hst.eps_deg a ha he; omega) hd⟩
    noloop := hN.noloop
    alpha_sg := hN.alpha_sg
    dartGap := hN.dartGap
    noBetaCut := hN.noBetaCut
    N1 := hN.N1
    N2 := hN.N2 }

end WaveTurbulence.FinalCountG3
