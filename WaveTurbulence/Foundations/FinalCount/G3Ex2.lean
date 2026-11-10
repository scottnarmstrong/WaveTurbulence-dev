/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex34
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.G3URun
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.FinalCount.TriSib3
/-! **FINALCOUNT-G3: excessprop1 (1) for Step 2 (triangles)** (DH23 Prop 9.4, Step 2, L1793--L1796, glued to
FINALCOUNT-G2-SIBLING `triangle_excess_sibling`).

The three cuts are G2's `T.m1, T.m2, T.m3`, the removal of the triangle is `T.kept`; the ghost deletion of
`triSt` (reading R-T1: an already cut triangle atom leaves an isolated remainder) is a dartless restriction
(`countA_restrict_dartless`: `𝔄` is unchanged).  The `κ = 50` of the second cut comes from an older cut still carried by a
present atom (`IotaUnif`), or from the first cut of the same triangle (`SibUnif`, the sibling count). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀}

theorem isDeviation_trans' {a b c I J : ℝ≥0∞} (h1 : IsDeviation a b I) (h2 : IsDeviation b c J) :
    IsDeviation a c (I * J) := by
  unfold IsDeviation at *
  calc a ≤ I * b := h1
    _ ≤ I * (J * c) := by gcongr
    _ = I * J * c := by ring

theorem gapKind_SG_ne_zero {r : Mom d} (h : Molecule.gapKind L γ η r = .SG) : r ≠ 0 := by
  intro e; subst e; simp [Molecule.gapKind] at h

theorem sibU_reading {h : HSt V D₀} {T : TriData h.s.M} {R : ℝ}
    (hS : SibUnif Adm0 L η w (h.s.pr (T.a 0) (T.b 0)) (h.s.pr (T.a 1) (T.b 1)) R) :
    T.SiblingReading L w (AdmS Adm0 h.s) (L ^ (-50 * η) * R) := by
  obtain ⟨sg, hsg, hb⟩ := hS
  rcases hsg with rfl | rfl
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rintro _ ⟨k0, hk0, rfl⟩
    have := (hb k0 hk0).2
    have e : Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 1) (T.b 1) - ((-1 : ℤ) : ℝ) • Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 0) (T.b 0) =
        pgap L w k0 (h.s.pr (T.a 1) (T.b 1)) + (1 : ℝ) • pgap L w k0 (h.s.pr (T.a 0) (T.b 0)) := by
      simp [pgap, St.pr]; rfl
    rw [e]; exact this
  · refine ⟨1, Or.inl rfl, ?_⟩
    rintro _ ⟨k0, hk0, rfl⟩
    have := (hb k0 hk0).2
    have e : Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 1) (T.b 1) - ((1 : ℤ) : ℝ) • Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 0) (T.b 0) =
        pgap L w k0 (h.s.pr (T.a 1) (T.b 1)) + (-1 : ℝ) • pgap L w k0 (h.s.pr (T.a 0) (T.b 0)) := by
      simp [pgap, St.pr]; rfl
    rw [e]; exact this

theorem kept_deg_f_zero {s : St.{u} V D₀} (T : TriData s.M) (j : Fin 3) (hd : s.M.deg (T.t j) ≤ 2) :
    T.kept.deg (T.f j) = 0 := by
  have hP : T.TP (T.f j) := fun i e => T.f_ne_t j i e
  have h5 := tri_deg_f T j
  have h6 : T.kept.deg (T.f j) = T.m3.deg (T.f j) := restrictP_deg T.m3 T.TP T.pclosed hP
  have := tri_deg_ge_two T j
  omega

/-! ### R38(2): the charged triangle bound with the TRUE increments -/

/-- The `α`-ghosts of a triangle: the already-cut `α` atoms `t j`, with their stored labels `(Q_g, κ_g)`. -/
noncomputable def alphaGhostList (h : HSt V D₀) (T : TriData h.s.M) : List (ℝ × ℕ) :=
  (List.finRange 3).filterMap fun j => match h.s.cls (T.t j) with
    | .alpha R k => some (R, k)
    | _ => none

/-- The new `α`-atoms (labels) of a triangle step: the non-ghost `f_j`, `j ∈ {0,1}`, that `triCls` makes `α`. -/
noncomputable def triAlphaNew (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) : List (ℝ × ℕ) :=
  (List.finRange 2).filterMap fun j => if h.s.cls (T.t j.castSucc) = .eps then
    (match triCls h.s T Q kp (T.f j.castSucc) with | .alpha R k => some (R, k) | _ => none) else none

/-- The number of `β`-atoms of a state. -/
noncomputable def betaCount (s : St.{u} V D₀) : ℤ := ((s.M.atoms.filter fun a => s.cls a = .beta).card : ℤ)

/-- The refund factor `∏ T(Q_g, κ_g)` of a list of labels, `T(Q,κ) = L^{(γ+3η)/2 - κη} Q`. -/
noncomputable def labelProd (L γ η : ℝ) (l : List (ℝ × ℕ)) : ℝ :=
  (l.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod

/-- The label of an already-cut `α`/`β` atom of degree `2` on the triangle darts, from the run invariants. -/
theorem ghost_alpha_gap {h : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hI : HInv L γ η w κ h) (hG : HGap L w κ h)
    {a : V} (ha : a ∈ h.s.M.atoms) {R : ℝ} {k : ℕ} (hc : h.s.cls a = .alpha R k) {x y : h.s.D}
    (hx : h.s.M.atom x = a) (hy : h.s.M.atom y = a) (ho1 : h.s.M.out x = false) (ho2 : h.s.M.out y = true) :
    IsLabel L γ η R ∧ (k = 0 ∨ k = 50) ∧ GapSim L w (κ ∘ h.s.down) x y R := by
  obtain ⟨hl, p, vis, hr, hp, hk, -, -⟩ := (hI.ok a ha).1 R k hc
  obtain ⟨p', vis', hr', hn⟩ := hG.dg a ha (by rw [hc]; simp) x y hx hy ho1 ho2
  rw [hr] at hr'; simp only [Option.some.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, -⟩ := hr'
  have := norm_gap_of_pm hn
  exact ⟨hl, hk, by unfold GapSim; rw [this]; exact hp⟩

end WaveTurbulence.FinalCountG3
