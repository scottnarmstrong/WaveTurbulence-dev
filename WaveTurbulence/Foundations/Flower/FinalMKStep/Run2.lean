/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.Run1

/-! # C1a SURV-STEP (6): the LOW run with re-cuts, part 2 (`HRunLE.noTriple`, `HRunLE.prop95L`)

Copy-thread of main's GL11 `noTripleBond_of_stopL` and GL12 `HRunL.noTriple`/`HRunL.prop95L` (sha256 in
COPIED-SHA256SUMS) to `HRunLE`: Step-1 inductions run over `HStep1LE` (`HStep1LE.aux`, `HStep1LE.epsLe`, `HRunLE.inv1`),
and `SubproOblG` is replaced by its field `HingeSG`. The conclusion is main's `Prop95ConclL` unchanged, so the final-state
lemmas of G3-LOWDEG (GV01–GV13, `Prop95ConclL.toAtL`) apply to the run with re-cuts as they are. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- No triple bond after Step 1 with re-cuts (main's `noTripleBond_of_stopL`, GL11, R37(b)). -/
theorem noTripleBond_of_stopLE [Infinite V] {C : CollData M₀} {h₁ : HSt V D₀} (hS : SubHypL R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hHg : HingeSG C L γ η w κ) (hT : TripleDesig C)
    (a1 : Relation.ReflTransGen (HStep1LE C L γ η w κ) (HSt.init M₀) h₁) (n1 : NoTripleCut C L γ η w κ h₁) :
    NoTripleBond h₁.s.M := by
  obtain ⟨R', hR', i1⟩ := HRunLE.inv1 a1 (InvL.init hS h0)
  have hA : AncRel M₀ h₁.s h₁.anc :=
    (rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hr => HStep1LE.aux hs hr) a1 (RunAux.init C)).2.1
  have e : EpsLe (HSt.init M₀).s h₁.s :=
    rtgH (P := fun h => EpsLe (HSt.init M₀).s h.s) (fun _ _ hs he => he.trans (HStep1LE.epsLe hs)) a1 (EpsLe.refl _)
  have hg := i1.good
  have hD := i1.rel
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hbs : h₁.s.M.bondsBetween b a = h₁.s.M.bondsBetween a b := by
    unfold Molecule.bondsBetween; simp only [Sym2.eq_swap]
  have hda : 3 ≤ h₁.s.M.deg a := hcon.trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ h₁.s.M.deg b := by rw [← hbs] at hcon; exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : h₁.s.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : h₁.s.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a0, -⟩, ⟨b0, -⟩, hle⟩ := e a ha b hb hea heb
  obtain ⟨v, c, x, y, hvc, hH, hf, hs, hTA, hmx, hmy⟩ := hT a b a0 b0 hab (hcon.trans hle)
  -- the hinge endpoint `v` and the other endpoint `c`, as atoms of `h₁`
  have key : ∀ v c : V, v ∈ h₁.s.M.atoms → c ∈ h₁.s.M.atoms → h₁.s.cls v = .eps → h₁.s.cls c = .eps → v ≠ c →
      3 ≤ h₁.s.M.bondsBetween v c → 3 ≤ h₁.s.M.deg v → v ∈ C.hinges → ∀ x y, C.first v = some x →
      C.second v = some y → TripleAtM M₀ v x y → M₀.atom (M₀.mate x) = c → M₀.atom (M₀.mate y) = c → False := by
    intro v c hv hc hεv hεc hvc' hb3 hdv hHv x y hf hs hTA hmx hmy
    obtain ⟨hxa, hya, hyx, hxy⟩ := hTA
    obtain ⟨X, hXd, hXa, hXm⟩ := eps_dart_lift hA hD hv hεv hc hεc hxa hmx
    obtain ⟨Y, hYd, hYa, hYm⟩ := eps_dart_lift hA hD hv hεv hc hεc hya hmy
    have hoX : h₁.s.M.out X = M₀.out x := by rw [← hD.out, hXd]
    have hoY : h₁.s.M.out Y = M₀.out y := by rw [← hD.out, hYd]
    have hanc : h₁.anc v = v := hA.eps v hv hεv
    obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset h₁.s.M.atoms
    obtain ⟨x₀, y₀, hx₀, hy₀, -, hsgxy⟩ := hHg v hHv
    have ex : x₀ = x := Option.some.inj (hx₀.symm.trans hf)
    have ey : y₀ = y := Option.some.inj (hy₀.symm.trans hs)
    rw [ex, ey] at hsgxy
    have hdesxy : Desig C v (x, y) := fun _ => ⟨x, y, hf, hs, Or.inl (by simp)⟩
    have hdesyx : Desig C v (y, x) := fun _ => ⟨x, y, hf, hs, Or.inl (by simp [Set.pair_comm])⟩
    have hneX : Y ≠ h₁.s.M.mate X := by
      intro hh; apply hyx
      have := congrArg h₁.s.down hh
      rw [hYd, ← hD.mate, hXd] at this; exact this
    have hneY : X ≠ h₁.s.M.mate Y := by
      intro hh; apply hyx
      have := congrArg h₁.s.down hh
      rw [hXd, ← hD.mate, hYd] at this
      rw [this, M₀.mate_mate]
    cases hox : M₀.out x
    · -- x incoming: (X, Y)
      have hoy : M₀.out y = true := by
        cases h' : M₀.out y
        · exact absurd (hox.trans h'.symm) hxy
        · rfl
      have hc' : h₁.s.M.IsCutData v v₂ X Y := ⟨hv, hv₂, hXa, hYa, hneX, by rw [hoX, hox], by rw [hoY, hoy]⟩
      refine n1 v v₂ X Y hc' hεv hdv (by rw [hanc]; exact hHv) (by rw [hanc]; simpa [St.pr, hXd, hYd] using hdesxy) ⟨c, hvc'.symm, hb3, hXm, hYm⟩ ?_
      show Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h₁.s.down) X Y) = .SG
      have : Molecule.gapAt L w (κ ∘ h₁.s.down) X Y = Molecule.gapAt L w κ x y := by
        unfold Molecule.gapAt Molecule.kvec; simp [Function.comp, hXd, hYd]
      rw [this]; exact hsgxy
    · -- x outgoing: (Y, X)
      have hoy : M₀.out y = false := by
        cases h' : M₀.out y
        · rfl
        · exact absurd (hox.trans h'.symm) hxy
      have hc' : h₁.s.M.IsCutData v v₂ Y X := ⟨hv, hv₂, hYa, hXa, hneY, by rw [hoY, hoy], by rw [hoX, hox]⟩
      refine n1 v v₂ Y X hc' hεv hdv (by rw [hanc]; exact hHv) (by rw [hanc]; simpa [St.pr, hXd, hYd] using hdesyx) ⟨c, hvc'.symm, hb3, hYm, hXm⟩ ?_
      show Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h₁.s.down) Y X) = .SG
      have : Molecule.gapAt L w (κ ∘ h₁.s.down) Y X = -Molecule.gapAt L w κ x y := by
        unfold Molecule.gapAt Molecule.kvec; simp [Function.comp, hXd, hYd]
      rw [this, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg _)]; exact hsgxy
  rcases hvc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key v c ha hb hea heb hab hcon hda hH x y hf hs hTA hmx hmy
  · exact key v c hb ha heb hea hab.symm (by rw [hbs]; exact hcon) hdb hH x y hf hs hTA hmx hmy

/-- No triple bonds at the end of the LOW run with re-cuts (main's `HRunL.noTriple`, GL12). -/
theorem HRunLE.noTriple [Infinite V] {C : CollData M₀} {hf : HSt V D₀} (hr : HRunLE C L γ η w κ (HSt.init M₀) hf)
    (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ) (hT3 : TripleDesig C)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {R' : ℕ} (hg : Good R' hf.s) : NoTripleBond hf.s.M := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1c, a2, -, a3, -, a4, -, a5, -⟩ := hr
  have n1 : NoTripleBond h₁.s.M := noTripleBond_of_stopLE hS h0 hH hT3 a1 n1c
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

/-- **DH23 Prop 9.5 / TARGET `finalmol` for the LOW run with re-cuts** (main's `HRunL.prop95L`, GL12). -/
theorem HRunLE.prop95L [Infinite V] {C : CollData M₀} {Tm : V → Prop} {hf : HSt V D₀}
    (hr : HRunLE C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (hH : HingeSG C L γ η w κ)
    (hT3 : TripleDesig C) (hdeg : DegenSGT M₀ L γ η w κ Tm)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95ConclL L γ η w κ Tm R hf := by
  obtain ⟨R', hR', hI⟩ := HRunLE.inv hr (InvL.init hS h0)
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
    no_triple := HRunLE.noTriple hr hS hH hT3 h0 hgR'
    cycles := HRunLE.cycles hr hS hH h0
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

end WaveTurbulence.Flower.FinalMKStep
