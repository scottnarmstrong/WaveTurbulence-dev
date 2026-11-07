/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CycN
/-! **FINALCOUNT-G3 (R37(b)): `NoTripleBond` after Step 1 is a THEOREM.**  Step 1 now stops at `NoTripleCut` (no `triple` step of
`HStep1C` applies).  From it, the S4 input `TripleDesig` (generic form of `Subpro.triple_in_designated`) and `subpro` (5)
(`hingeSG`) we prove `NoTripleBond h₁.s.M`: a triple bond between two `ε`-atoms has a hinge endpoint whose designated pair lies
inside it, and that pair is an applicable `triple` cut. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- The dart of the current state over a dart of `M_sub` at an `ε`-atom, with its atom and mate. -/
theorem eps_dart_lift {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s) {v c : V}
    (hv : v ∈ s.M.atoms) (hε : s.cls v = .eps) (hc : c ∈ s.M.atoms) (hcε : s.cls c = .eps) {z : D₀}
    (hz : M₀.atom z = v) (hzc : M₀.atom (M₀.mate z) = c) :
    ∃ x : s.D, s.down x = z ∧ s.M.atom x = v ∧ s.M.atom (s.M.mate x) = c := by
  obtain ⟨x, hx⟩ := hA.surj v hv hε z hz
  have h1 : s.M.atom x = v := by
    refine hA.uniq _ (s.M.atom_mem x) v hv hε ?_
    rw [← hA.atom x, hx, hz]
  refine ⟨x, hx, h1, ?_⟩
  refine hA.uniq _ (s.M.atom_mem _) c hc hcε ?_
  rw [← hA.atom, ← hD.mate, hx, hzc]

theorem noTripleBond_of_stop [Infinite V] {C : CollData M₀} {h₁ : HSt V D₀} (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (obl : SubproOblG C L γ η w κ) (hT : TripleDesig C)
    (a1 : Relation.ReflTransGen (HStep1C C L γ η w κ) (HSt.init M₀) h₁) (n1 : NoTripleCut C L γ η w κ h₁) :
    NoTripleBond h₁.s.M := by
  have i1 : InvE M₀ R 0 L γ η w κ h₁ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1C hs) a1 (InvE.init hS h0)
  have hA : AncRel M₀ h₁.s h₁.anc :=
    rtgH (P := fun h => AncRel M₀ h.s h.anc) (fun _ _ hs hr => hs.anc hr) a1 (AncRel.init M₀)
  have e : EpsLe (HSt.init M₀).s h₁.s :=
    rtgH (P := fun h => EpsLe (HSt.init M₀).s h.s) (fun _ _ hs he => by
      rcases hs.cases with h1 | h3
      · exact he.trans h1.step.epsLe
      · exact he.trans h3.toHStep3.step.epsLe) a1 (EpsLe.refl _)
  obtain ⟨R', hR', hg⟩ := i1.good
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
    obtain ⟨x₀, y₀, hx₀, hy₀, -, hsgxy⟩ := obl.hingeSG v hHv
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

end WaveTurbulence.FinalCountG3
