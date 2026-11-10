/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RunN
public import WaveTurbulence.Foundations.FinalCount.G3DPRun
/-! **FINALCOUNT-G3 (R29 item 2): `cycles` from `NoEligibleTriangle`** (the hinge step of A1).  A triangle of two `α`-atoms and a third
`α`/`β`-atom is ELIGIBLE: SG at `v₁, v₂` (`α` atoms), nonzero gap at `v₃` (`α` is SG, `β` has a nonzero gap, N1), and the triangle pair
at a hinge atom is a designated pair (`desig_pair`, from `DesRecN` and the dart-set invariant). -/
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

/-- Set-level transfer of `Desig` from the recorded pair `p` to a pair `q` of two distinct darts of the atom, that is either the
same set as `p` or disjoint from it (a degree `≤ 4` atom). -/
theorem desig_of_sub {C : CollData M₀} {A : V} (hcard : (M₀.dartsAt A).card ≤ 4)
    (hfs : A ∈ C.hinges → ∀ f s, C.first A = some f → C.second A = some s →
      f ∈ M₀.dartsAt A ∧ s ∈ M₀.dartsAt A ∧ f ≠ s)
    {p q : D₀ × D₀} (hq1 : q.1 ∈ M₀.dartsAt A) (hq2 : q.2 ∈ M₀.dartsAt A) (hq12 : q.1 ≠ q.2)
    (hdp : ({q.1, q.2} : Set D₀) = {p.1, p.2} ∨ Disjoint ({q.1, q.2} : Set D₀) {p.1, p.2})
    (hp : Desig C A p) : Desig C A q := by
  intro hA
  obtain ⟨f, s, hf, hs, hp'⟩ := hp hA
  refine ⟨f, s, hf, hs, ?_⟩
  rcases hdp with he | hdis
  · rwa [he]
  obtain ⟨hfm, hsm, hfsn⟩ := hfs hA f s hf hs
  rcases hp' with hA' | hB'
  · -- p = {f,s}: q is disjoint from {f,s}, hence the complement
    rw [hA'] at hdis
    right
    have hqf : q.1 ≠ f ∧ q.1 ≠ s ∧ q.2 ≠ f ∧ q.2 ≠ s := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;>
      · have := Set.disjoint_left.1 hdis (show q.1 ∈ ({q.1, q.2} : Set D₀) by simp)
        have h2 := Set.disjoint_left.1 hdis (show q.2 ∈ ({q.1, q.2} : Set D₀) by simp)
        simp_all
    set S : Finset D₀ := {f, s, q.1, q.2} with hS
    have hsub : S ⊆ M₀.dartsAt A := by
      intro z hz
      simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have hScard : S.card = 4 := by
      rw [hS]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hq12]
      · simp [hqf.1.symm, hqf.2.2.1.symm, hqf.2.1.symm, hqf.2.2.2.symm]
      · simp [hfsn, hqf.1.symm, hqf.2.2.1.symm]
    have hEq : S = M₀.dartsAt A := Finset.eq_of_subset_of_card_le hsub (by omega)
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff, Finset.mem_coe]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨hq1, by simp [hqf.1, hqf.2.1]⟩
      · exact ⟨hq2, by simp [hqf.2.2.1, hqf.2.2.2]⟩
    · rintro ⟨hz, hzn⟩
      rw [← hEq] at hz
      simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [not_or] at hzn
      rcases hz with rfl | rfl | rfl | rfl
      · exact absurd rfl hzn.1
      · exact absurd rfl hzn.2
      · exact Or.inl rfl
      · exact Or.inr rfl
  · -- p = complement of {f,s}: q is disjoint from it, so q ⊆ {f,s}
    rw [hB'] at hdis
    left
    have h1 : q.1 = f ∨ q.1 = s := by
      by_contra hn
      push Not at hn
      exact Set.disjoint_left.1 hdis (show q.1 ∈ ({q.1, q.2} : Set D₀) by simp) ⟨hq1, by simp [hn.1, hn.2]⟩
    have h2 : q.2 = f ∨ q.2 = s := by
      by_contra hn
      push Not at hn
      exact Set.disjoint_left.1 hdis (show q.2 ∈ ({q.1, q.2} : Set D₀) by simp) ⟨hq2, by simp [hn.1, hn.2]⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hq12
    · rw [e1, e2]
    · rw [e1, e2]; tauto
    · exact absurd (e1.trans e2.symm) hq12


theorem HRunN.dp {C : CollData M₀} {hf : HSt V D₀} (hr : HRunN C L γ η w κ (HSt.init M₀) hf) : DPInv hf := by
  obtain ⟨h₁, h₂, h₃, a1, _, a2, _, a3, _, a4, _⟩ := hr
  have r0 := AncRel.init M₀
  have i0 : DPInv (HSt.init M₀) := DPInv.init M₀
  have s1 := rtg_dp (fun h h' hs i r => by
    rcases hs.cases with h1 | h3
    · exact ⟨h1.dp i r.inj, h1.anc r⟩
    · exact ⟨h3.toHStep3.dp i r.inj, h3.toHStep3.anc r⟩) a1 i0 r0
  have s2 := rtg_dp (fun h h' hs i r => ⟨hs.toHStep2.dp i r.inj, hs.toHStep2.anc r⟩) a2 s1.1 s1.2
  have s3 := rtg_dp (fun h h' hs i r => ⟨hs.toHStep3.dp i r.inj, hs.toHStep3.anc r⟩) a3 s2.1 s2.2
  exact (rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a4 s3.1 s3.2).1

/-- `NoEligibleTriangle` at the end of a run (preserved by the cuts of Steps 3 and 4). -/
theorem HRunN.noElig {C : CollData M₀} {hf : HSt V D₀} (hr : HRunN C L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    NoEligibleTriangle C L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, a1, -, a2, n2, a3, -, a4, -⟩ := hr
  have i1 : InvE M₀ R 0 L γ η w κ h₁ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1C hs) a1 (InvE.init hS h0)
  have i2 : InvE M₀ R 0 L γ η w κ h₂ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step2 hs.toHStep2) a2 i1
  have k3 := rtgH (P := fun h => InvE M₀ R 0 L γ η w κ h ∧ NoEligibleTriangle C L γ η w κ h)
    (fun h h' hs hP => ⟨hP.1.step3 hs.toHStep3, hP.2.step3 hP.1.noloop hs.toHStep3⟩) a3 ⟨i2, n2⟩
  exact (rtgH (P := fun h => InvE M₀ R 0 L γ η w κ h ∧ NoEligibleTriangle C L γ η w κ h)
    (fun h h' hs hP => ⟨hP.1.step4 hs, hP.2.step4 hP.1.noloop hs⟩) a4 k3).2

/-- **The recorded pair of any non-`ε` atom is designated** (A1): for two distinct darts `x, y` of a non-`ε` atom `c` of the final
state, the pair `(x, y)` is a designated pair of `anc c` (or its complement). -/
theorem desig_pair {C : CollData M₀} {hf : HSt V D₀} (hS : SubHyp R M₀)
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
  have hcard : (M₀.dartsAt (hf.anc c)).card ≤ 4 := deg_le_four M₀ (hS.bounds _ hAm)
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
theorem InvE.alpha_sg {t : ℕ} {h : HSt V D₀} (hI : InvE M₀ R t L γ η w κ h) :
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
theorem InvE.gap_ne {t : ℕ} {h : HSt V D₀} (hI : InvE M₀ R t L γ η w κ h) {b : V} (hb : b ∈ h.s.M.atoms)
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

/-- **`cycles` for `HRunN`** (DH23 Prop 9.5 L1807, with `NoEligibleTriangle`, R29 item 2): a triangle component with two `α`-atoms
would be an eligible triangle. -/
theorem HRunN.cycles [Infinite V] {C : CollData M₀} {hf : HSt V D₀}
    (hr : HRunN C L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀) (obl : SubproOblG C L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) → CycleShape hf.s a := by
  have hI := hr.invN (InvE.init hS h0)
  obtain ⟨R', hR', hgR'⟩ := hI.good
  have hst : FinalStructE R 0 hf.s := FinalStructE.of_inv hI.good0 hR' hgR' hI.comp hI.flat
  have hNE := hr.noElig hS h0
  obtain ⟨hD, hA⟩ := hr.desRec obl
  have hdp := hr.dp
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
    exact desig_pair hS obl hA hgR'.2 hI.hrec hdp hD (T.t_mem j) hj (T.atom_a j) (T.atom_b j) (hxy j)

end WaveTurbulence.FinalCountG3
