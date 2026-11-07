/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL9
/-! **G3-LOWDEG (R48), part 10**: `cycles` for the LOW run.  `desig_pairL`, `InvL.alpha_sg`, `InvL.gap_ne` are COPIES of
G3CycN `desig_pair`, `InvE.alpha_sg`, `InvE.gap_ne` (sha256 of G3CycN.lean in COPIED-SHA256SUMS) with `SubHyp.bounds` replaced
by the bounds hypothesis and `InvE` by `InvL`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **The recorded pair of any non-`ε` atom is designated** (A1): for two distinct darts `x, y` of a non-`ε` atom `c` of the final
state, the pair `(x, y)` is a designated pair of `anc c` (or its complement). -/
theorem InvL.noloop {h : HSt V D₀} (hI : InvL M₀ R L γ η w κ h) :
    ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := hI.good.1.noloop

theorem desig_pairL {C : CollData M₀} {hf : HSt V D₀} (hb : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2)
    (obl : SubproOblG C L γ η w κ) (hA : AncRel M₀ hf.s hf.anc) (hg : Clean hf.s)
    (hrec : HInv L γ η w κ hf) (hdp : DPInv hf) (hdes : DesRecN C hf) {c : V} (hc : c ∈ hf.s.M.atoms)
    (hne : hf.s.cls c ≠ .eps) {x y : hf.s.D} (hx : hf.s.M.atom x = c) (hy : hf.s.M.atom y = c) (hxy : x ≠ y) :
    Desig C (hf.anc c) (hf.s.pr x y) := by
  obtain ⟨p, vis, hr⟩ : ∃ p vis, hf.crec c = some (p, vis) := by
    have ok := hrec.ok c hc
    rcases hcl : hf.s.cls c with _ | ⟨ρ, kp⟩ | _ | _
    · exact absurd hcl hne
    · obtain ⟨-, p, vis, hr, -⟩ := ok.1 ρ kp hcl
      exact ⟨p, vis, hr⟩
    · obtain ⟨p, vis, hr, -⟩ := ok.2 hcl
      exact ⟨p, vis, hr⟩
    · exact absurd hcl (hg c hc)
  have hAm : hf.anc c ∈ M₀.atoms := hA.mem c hc
  have hdx : hf.s.down x ∈ M₀.dartsAt (hf.anc c) := by
    rw [mem_dartsAt, hA.atom x, hx]
  have hdy : hf.s.down y ∈ M₀.dartsAt (hf.anc c) := by
    rw [mem_dartsAt, hA.atom y, hy]
  have hcard : (M₀.dartsAt (hf.anc c)).card ≤ 4 := deg_le_four M₀ (hb _ hAm)
  have hne' : hf.s.down x ≠ hf.s.down y := fun e => hxy (hA.inj e)
  refine desig_of_sub hcard ?_ (q := hf.s.pr x y) hdx hdy hne' ?_ (hdes c p vis hr)
  · intro hH f' s' hf' hs'
    obtain ⟨f, s, hf0, hs0, ⟨hfa, hsa, hfs, hout⟩, -⟩ := obl.hingeSG _ hH
    have e1 : f' = f := Option.some.inj (hf'.symm.trans hf0)
    have e2 : s' = s := Option.some.inj (hs'.symm.trans hs0)
    subst e1 e2
    exact ⟨(mem_dartsAt _ _ _).2 hfa, (mem_dartsAt _ _ _).2 hsa, fun e => hout (by rw [e])⟩
  · have hsub : ({(hf.s.pr x y).1, (hf.s.pr x y).2} : Set D₀) ⊆ DSet hf.s c := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
    rcases hdp.ok c hc p vis hr with he | hdis
    · left
      rw [he] at hsub
      have h1 : (hf.s.pr x y).1 ∈ ({p.1, p.2} : Set D₀) := hsub (by simp)
      have h2 : (hf.s.pr x y).2 ∈ ({p.1, p.2} : Set D₀) := hsub (by simp)
      have hne2 : (hf.s.pr x y).1 ≠ (hf.s.pr x y).2 := hne'
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 ⊢
      rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hne2
      · rw [e1, e2]
      · rw [e1, e2]; tauto
      · exact absurd (e1.trans e2.symm) hne2
    · right
      exact Set.disjoint_of_subset_left hsub hdis



/-- Dart-level SG gaps of `α`-atoms, from the run invariants. -/
theorem InvL.alpha_sg {h : HSt V D₀} (hI : InvL M₀ R L γ η w κ h) :
    ∀ b ∈ h.s.M.atoms, ∀ ρ kp, h.s.cls b = .alpha ρ kp → ∀ x y : h.s.D, h.s.M.atom x = b →
      h.s.M.atom y = b → h.s.M.out x = false → h.s.M.out y = true →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x y) = .SG := by
  intro b hb ρ kp hc x y hx hy hox hoy
  obtain ⟨-, p, vis, hrec, -, -, -, hsg⟩ := (hI.hrec.ok b hb).1 ρ kp hc
  obtain ⟨p', vis', hrec', hn⟩ := hI.gap.dg b hb (by rw [hc]; simp) x y hx hy hox hoy
  rw [hrec] at hrec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
  obtain ⟨rfl, rfl⟩ := hrec'
  rw [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_gap_of_pm hn)]
  exact hsg

/-- The dart gap of a non-`ε` atom is nonzero (`α`: SG; `β`: N1). -/
theorem InvL.gap_ne {h : HSt V D₀} (hI : InvL M₀ R L γ η w κ h) {b : V} (hb : b ∈ h.s.M.atoms)
    (hne : h.s.cls b ≠ .eps) (hgh : h.s.cls b ≠ .ghost) {x y : h.s.D} (hx : h.s.M.atom x = b)
    (hy : h.s.M.atom y = b) (hox : h.s.M.out x = false) (hoy : h.s.M.out y = true) :
    Molecule.gapAt L w (κ ∘ h.s.down) x y ≠ 0 := by
  rcases hcl : h.s.cls b with _ | ⟨ρ, kp⟩ | _ | _
  · exact absurd hcl hne
  · exact gap_ne_zero_of_SG (hI.alpha_sg b hb ρ kp hcl x y hx hy hox hoy)
  · obtain ⟨g, ⟨p, vis, hr, rfl⟩, hg0⟩ := hI.hrec.N1 hb hcl
    obtain ⟨p', vis', hr', hn⟩ := hI.gap.dg b hb (by rw [hcl]; simp) x y hx hy hox hoy
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    rcases hn with e | e <;> rw [e]
    · exact hg0
    · exact neg_ne_zero.2 hg0
  · exact absurd hcl hgh

/-- **`cycles` for the LOW run** (DH23 Prop 9.5 L1807): a triangle component with two `α`-atoms would be an eligible triangle. -/
theorem HRunL.cycles [Infinite V] {C : CollData M₀} {hf : HSt V D₀}
    (hr : HRunL C L γ η w κ (HSt.init M₀) hf) (hS : SubHypL R M₀) (obl : SubproOblG C L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) → CycleShape hf.s a := by
  obtain ⟨R', hR', hI⟩ := hr.inv (InvL.init hS h0)
  have hgR' := hI.good
  have hst : FinalStructL R hf.s := FinalStructL.of_good hR' hI.good hI.comp
  obtain ⟨⟨hdp, hA, hD⟩, hNE⟩ := hr.final hS obl h0 rfl
  intro a ha hev hne
  refine cycles_of_key hst.ab_deg (fun c hc => (hst.deg_range c hc).1) hI.bal hI.noloop ?_ ha hev hne
  intro T ⟨ρ0, k0, h0'⟩ ⟨ρ1, k1, h1'⟩ hne2
  have hcl : ∀ j : Fin 3, hf.s.cls (T.t j) ≠ .eps → hf.s.cls (T.t j) ≠ .ghost := fun j hj =>
    fun e => hgR'.2 _ (T.t_mem j) e
  have hxy : ∀ j : Fin 3, T.a j ≠ T.b j := fun j e => by
    have := T.out_a j; have h2 := T.out_b j; rw [e] at this; rw [this] at h2; exact absurd h2 (by simp)
  have hne0 : hf.s.cls (T.t 0) ≠ .eps := by rw [h0']; simp
  have hne1 : hf.s.cls (T.t 1) ≠ .eps := by rw [h1']; simp
  refine hNE T ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hI.alpha_sg _ (T.t_mem 0) ρ0 k0 h0' _ _ (T.atom_a 0) (T.atom_b 0) (T.out_a 0) (T.out_b 0)
    · exact hI.alpha_sg _ (T.t_mem 1) ρ1 k1 h1' _ _ (T.atom_a 1) (T.atom_b 1) (T.out_a 1) (T.out_b 1)
  · exact hI.gap_ne (T.t_mem 2) hne2 (hcl 2 hne2) (T.atom_a 2) (T.atom_b 2) (T.out_a 2) (T.out_b 2)
  · intro j
    have hj : hf.s.cls (T.t j) ≠ .eps := by
      fin_cases j
      · exact hne0
      · exact hne1
      · exact hne2
    exact desig_pairL hS.bounds obl hA hgR'.2 hI.hrec hdp hD (T.t_mem j) hj (T.atom_a j) (T.atom_b j) (hxy j)

end WaveTurbulence.FinalCountG3
