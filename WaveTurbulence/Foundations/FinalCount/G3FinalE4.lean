/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalE3
/-! **FINALCOUNT-G3: `Prop95ConclE` and `HRunE.prop95E`** — DH23 Prop 9.5 / TARGET `finalmol` for runs with `t`
tame-atom erasures (corrected form of errata E9). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **Conclusions of Prop 9.5 / TARGET `finalmol` for a run with `t` erasures** (corrected, E9).  Differences from
`Prop95Concl`: `struct` has `R + t` imperfect components; `ε`-atoms are LG or `Tm` (tame); `cycles`/`chains` hold in
components whose `ε`-atoms have degree `≥ 3` (in particular perfect ones); `bal` is claimed for `α`/`β`-atoms;
`noBetaCut` is the strong form (no `β`-cut of any gap). -/
structure Prop95ConclE (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Tm : V → Prop) (R t : ℕ)
    (hf : HSt V D₀) : Prop where
  struct : FinalStructE R t hf.s
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  /-- every `ε`-atom is LG, or tame (then a zero-gap triple is allowed) -/
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → Tm a ∨ ∀ x y : hf.s.D, hf.s.M.atom x = a →
    hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  no_triple : NoTripleBond hf.s.M
  cycles : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) →
    CycleShape hf.s a
  chains : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps →
    (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
    (∀ e ∈ compAtoms hf.s.M a, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e) → ChainEnds hf.s a
  bal : BalS hf.s
  noloop : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)
  alpha_sg : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
    hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG
  dartGap : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → ∃ g, AtomGap L w κ hf a g ∧
      (Molecule.gapAt L w (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L w (κ ∘ hf.s.down) x y = -g)
  noBetaCut : NoBetaCutAll hf.s
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖

/-- **DH23 Prop 9.5 / TARGET `finalmol` (corrected), for a run with `t` tame-atom erasures.** -/
theorem HRunE.prop95E [Infinite V] {Tm : V → Prop} {hf : HSt V D₀} {t : ℕ}
    (hr : HRunE L γ η w κ (HSt.init M₀) hf t) (hS : SubHyp R M₀) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclE L γ η w κ Tm R t hf := by
  have hinit : InvE M₀ R 0 L γ η w κ (HSt.init M₀) := InvE.init hS h0
  have hI := hr.inv hinit
  obtain ⟨R', hR', hgR'⟩ := hI.good
  have hst : FinalStructE R t hf.s := FinalStructE.of_inv hI.good0 hR' hgR' hI.comp hI.flat
  have hab := hst.ab_deg
  have hdr : ∀ c ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg c := fun c hc => (hst.deg_range c hc).1
  have halpha : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
      hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG := by
    intro b hb ρ kp hc x y hx hy hox hoy
    obtain ⟨-, p, vis, hrec, -, -, -, hsg⟩ := (hI.hrec.ok b hb).1 ρ kp hc
    obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg b hb (by rw [hc]; simp) x y hx hy hox hoy
    rw [hrec] at hrec'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
    obtain ⟨rfl, rfl⟩ := hrec'
    rw [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_gap_of_pm hn)]
    exact hsg
  obtain ⟨h₁, h₂, h₃, t₂, a1, n1, a2, n2, a3, hsgl, a4, n4⟩ := id hr
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
    eps_LG := by
      intro a ha hae
      by_cases hT : Tm a
      · exact Or.inl hT
      right
      intro x y hx hy hox hoy hxy
      have hrel := hI.rel
      obtain ⟨ha3, hae3⟩ := HRunE.eps_back a4 a ha hae
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
    no_triple := hr.noTriple hgR'
    cycles := fun a ha hev hne =>
      cycles_of hab hdr hI.bal hI.noloop (hr.noSGTri hinit) halpha ha hev hne
    chains := fun a ha hev hne hex hε3 =>
      chainEnds_of hab hdr hI.bal ha (fun e he hce hae v₂ x₁ x₂ hcd =>
        n4 e he (hε3 e (Finset.mem_filter.2 ⟨he, hae⟩) hce) v₂ x₁ x₂ hcd) hev hne hex
    bal := hI.bal
    noloop := hI.noloop
    alpha_sg := halpha
    dartGap := by
      intro a ha hne x y hx hy hox hoy
      obtain ⟨p, vis, hrec, hn⟩ := hI.gap.dg a ha hne x y hx hy hox hoy
      exact ⟨pgap L w κ p, ⟨p, vis, hrec, rfl⟩, hn⟩
    noBetaCut := n4
    N1 := fun b hb hcb => hI.hrec.N1 hb hcb
    N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum =>
      hI.hrec.N2 hL hη h1 h2 hb c1 c2 cb a1' a2' ab s₁ s₂ hs₁ hs₂ hsum }

end WaveTurbulence.FinalCountG3
