/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.NCGraph
public import WaveTurbulence.Foundations.FinalCount.AsmTriPot
public import WaveTurbulence.Foundations.FinalCount.G3UStep
/-! **Ghost assembly: the survivors of a triangle step** (Operation 2; design: `CHAIN-DESIGN.md`).

`h' = h.triPost T Q kp hcl` (main `G3UStep`): the three cuts `t j ↦ (t j, f j)` along the triangle darts `(a j, b j)`,
removal of the triangle `{t 0, t 1, t 2}`, the classes `triCls`, deletion of the ghost remainders. Every atom of `h'`
other than the fresh `f j` is an atom of `h` with the same darts, class and cut record (`triSurvMap`), and the new atom
`f j` carries the record of its cut (`gvec_triPost_f`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section mol
variable {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M)

theorem m1_atom_of_ne (y : D) (hy : T.m1.atom y ≠ T.f 0) : T.m1.atom y = M.atom y := by
  rw [T.m1_atom] at hy ⊢; split_ifs at hy ⊢ <;> simp_all

theorem m2_atom_of_ne (y : D) (hy : T.m2.atom y ≠ T.f 1) : T.m2.atom y = T.m1.atom y := by
  rw [T.m2_atom] at hy ⊢; split_ifs at hy ⊢ <;> simp_all

theorem m3_atom_of_ne (y : D) (hy : T.m3.atom y ≠ T.f 2) : T.m3.atom y = T.m2.atom y := by
  rw [T.m3_atom] at hy ⊢; split_ifs at hy ⊢ <;> simp_all

/-- After the three cuts, a dart whose atom is not fresh kept its atom. -/
theorem m3_atom_of_ne_f (y : D) (hy : ∀ j, T.m3.atom y ≠ T.f j) : T.m3.atom y = M.atom y := by
  have e3 := m3_atom_of_ne T y (hy 2)
  have e2 := m2_atom_of_ne T y (by rw [← e3]; exact hy 1)
  have e1 := m1_atom_of_ne T y (by rw [← e2, ← e3]; exact hy 0)
  rw [e3, e2, e1]

/-- A dart at a fresh atom `f j` after the cuts was at `t j`. -/
theorem m3_atom_eq_f (y : D) (j : Fin 3) (hy : T.m3.atom y = T.f j) : M.atom y = T.t j := by
  have hft : ∀ i k : Fin 3, T.f i ≠ T.t k := T.f_ne_t
  have h01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
  have h02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
  have h12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
  have hfM : ∀ i, M.atom y ≠ T.f i := fun i e => T.f_fresh i (e ▸ M.atom_mem y)
  have m1t : ∀ k, T.m1.atom y = T.t k → M.atom y = T.t k := by
    intro k hk; rw [T.m1_atom] at hk; split_ifs at hk with hc
    · exact absurd hk (hft 0 k)
    · exact hk
  have m2t : ∀ k, T.m2.atom y = T.t k → M.atom y = T.t k := by
    intro k hk; rw [T.m2_atom] at hk; split_ifs at hk with hc
    · exact absurd hk (hft 1 k)
    · exact m1t k hk
  rw [T.m3_atom] at hy
  split_ifs at hy with h3
  · have hj : j = 2 := T.f_inj hy.symm
    subst hj; exact m2t 2 h3.1
  · rw [T.m2_atom] at hy
    split_ifs at hy with h2
    · have hj : j = 1 := T.f_inj hy.symm
      subst hj; exact m1t 1 h2.1
    · rw [T.m1_atom] at hy
      split_ifs at hy with h1
      · have hj : j = 0 := T.f_inj hy.symm
        subst hj; exact h1.1
      · exact absurd hy (hfM j)

theorem m3_common (a b : D) (hab : T.m3.atom a = T.m3.atom b) : M.atom a = M.atom b := by
  by_cases ha : ∀ j, T.m3.atom a ≠ T.f j
  · have hb : ∀ j, T.m3.atom b ≠ T.f j := fun j e => ha j (hab.trans e)
    rw [← m3_atom_of_ne_f T a ha, ← m3_atom_of_ne_f T b hb, hab]
  · push Not at ha
    obtain ⟨j, hj⟩ := ha
    rw [m3_atom_eq_f T a j hj, m3_atom_eq_f T b j (hab ▸ hj)]

/-- The darts at an atom other than the `t j`, `f j` are unchanged by the three cuts. -/
theorem m3_dartsAt_other {v : V} (hvt : ∀ j, v ≠ T.t j) (hvf : ∀ j, v ≠ T.f j) :
    T.m3.dartsAt v = M.dartsAt v := by
  ext y
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
  constructor
  · intro hy
    rw [← hy, m3_atom_of_ne_f T y (fun j e => hvf j (hy ▸ e))]
  · intro hy
    have hn : ∀ j, T.m3.atom y ≠ T.f j := by
      intro j e
      exact hvt j (hy ▸ m3_atom_eq_f T y j e)
    rw [m3_atom_of_ne_f T y hn, hy]

end mol

/-- The survivors of a triangle step: the atoms of the post state other than the fresh `f j`. -/
def triSurv (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) : Set V :=
  {v | v ∈ (h.triPost T Q kp hcl).s.M.atoms ∧ ∀ j, v ≠ T.f j}

theorem triPost_atoms (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) {v : V} (hv : v ∈ (h.triPost T Q kp hcl).s.M.atoms) :
    v ∈ T.m3.atoms ∧ T.TP v ∧ triKeep h.s T v := by
  have hv' : v ∈ (T.m3.atoms.filter T.TP).filter (triKeep h.s T) := hv
  simp only [mem_filter] at hv'
  exact ⟨hv'.1.1, hv'.1.2, hv'.2⟩

/-- **The survivor map of a triangle step.** -/
noncomputable def triSurvMap (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) : SurvMap h (h.triPost T Q kp hcl) (triSurv h T Q kp hcl) where
  ι := fun x => x.1.1
  down_eq := fun _ => rfl
  out_eq := fun _ => rfl
  mate_eq := fun _ => rfl
  atom_eq := fun x hx => (m3_atom_of_ne_f T x.1.1 hx.2).symm
  common := fun a b hab => m3_common T a.1.1 b.1.1 hab
  mem := fun v hv _ => by
    obtain ⟨h1, -, -⟩ := triPost_atoms h T Q kp hcl hv.1
    rw [T.m3_atoms] at h1
    simp only [mem_insert] at h1
    rcases h1 with e | e | e | e
    · exact absurd e (hv.2 2)
    · exact absurd e (hv.2 1)
    · exact absurd e (hv.2 0)
    · exact e
  deg_eq := fun v hv => by
    obtain ⟨-, hTP, hK⟩ := triPost_atoms h T Q kp hcl hv.1
    have e1 : (h.triPost T Q kp hcl).s.M.deg v = T.kept.deg v := restrictP_deg T.kept (triKeep h.s T) hcl hK
    have e2 : T.kept.deg v = T.m3.deg v := restrictP_deg T.m3 T.TP T.pclosed hTP
    rw [e1, e2]
    unfold Molecule.deg
    rw [m3_dartsAt_other T hTP hv.2]
  cls_eq := fun v hv => by
    show triCls h.s T Q kp v = h.s.cls v
    unfold triCls
    simp only [hv.2 0, hv.2 1, hv.2 2, ite_false]
  crec_eq := fun v hv => by
    show Function.update (Function.update (Function.update h.crec (T.f 0) _) (T.f 1) _) (T.f 2) _ v = h.crec v
    rw [Function.update_of_ne (hv.2 2), Function.update_of_ne (hv.2 1), Function.update_of_ne (hv.2 0)]

/-- The fresh atom `f 2` of a triangle step is never critical (`β` or a deleted ghost). -/
theorem not_critA_f2 {L γ η : ℝ} (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) : ¬ IsCritA L γ η (h.triPost T Q kp hcl) (T.f 2) := by
  rintro ⟨-, -, R, hR, -⟩
  have : (h.triPost T Q kp hcl).s.cls (T.f 2) = triCls h.s T Q kp (T.f 2) := rfl
  rw [this] at hR
  unfold triCls at hR
  simp only [ite_true] at hR
  split_ifs at hR

/-- The record gap of the fresh atom `f 0` is the gap of its cut. -/
theorem gvec_triPost_f0 (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.triPost T Q kp hcl) L w k0 (T.f 0) = Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 0) (T.b 0) := by
  have h01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
  have h02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
  have e : (h.triPost T Q kp hcl).crec (T.f 0) = some (h.s.pr (T.a 0) (T.b 0), h.alive) := by
    show Function.update (Function.update (Function.update h.crec (T.f 0) _) (T.f 1) _) (T.f 2) _ (T.f 0) = _
    rw [Function.update_of_ne h02, Function.update_of_ne h01, Function.update_self]
  unfold gvec; rw [e]; rfl

/-- The record gap of the fresh atom `f 1` is the gap of its cut. -/
theorem gvec_triPost_f1 (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.triPost T Q kp hcl) L w k0 (T.f 1) = Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 1) (T.b 1) := by
  have h12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
  have e : (h.triPost T Q kp hcl).crec (T.f 1) = some (h.s.pr (T.a 1) (T.b 1), h.triVis1 T) := by
    show Function.update (Function.update (Function.update h.crec (T.f 0) _) (T.f 1) _) (T.f 2) _ (T.f 1) = _
    rw [Function.update_of_ne h12, Function.update_self]
  unfold gvec; rw [e]; rfl

end WaveTurbulence.GammaLow.FinalCount.Ghost
