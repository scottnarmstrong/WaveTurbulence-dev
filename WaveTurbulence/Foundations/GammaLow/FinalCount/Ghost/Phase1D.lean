/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2D
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.CutCone2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1A
/-! **Ghost assembly, Phase 1 (D): the cone around a critical present atom** (design: `CHAIN-DESIGN.md`).

A critical atom `y` of a state (degree `2`, balanced: one outgoing dart `x₁'`, one incoming `x₂'`) has the dart gap
`± gvec y ≠ 0` (`present_gap`, from `HGap.dg` and the SG record of `HInv`). A cone of a cut gap around `gvec y` in a
class is then a parameter cone (`cutCone_of_present`: Lemma 6.2(iii) for the cut, as L6E2's `jointCone_of_present`):
`cutCone_of_crit` (triple α-cuts) and `jointCone_of_crit` (Operation 1, for any cut `K'` with the same joint record). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- **Lemma 6.2(iii) at a cut**: the cone of the cut gap around the gap of a present degree-2 atom `v` is a cone
around the fixed centre `c v` in each parameter class (`jointCone_of_present` for `CutCone`). -/
theorem cutCone_of_present {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (x₁ x₂ : D)
    {L γ δ η : ℝ} (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (v : V) (hv : v ∈ M.atoms)
    (x₁' x₂' : D) (hx : x₁' ≠ x₂') (hdarts : M.dartsAt v = {x₁', x₂'}) (h1 : M.out x₁' = true)
    (h2 : M.out x₂' = false) (hd : 0 < d) (hnz : ∀ κ', Adm κ' → Molecule.gapAt L w κ' x₁' x₂' ≠ 0)
    (hcone : ∀ κ', Adm κ' →
      InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ' x₁ x₂) (Molecule.gapAt L w κ' x₁' x₂')) :
    CutCone M x₁ x₂ L γ δ (L ^ (-6 * η)) w Adm := by
  intro c β k0 _
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  · obtain ⟨κs, hκs⟩ := hne
    refine ⟨c v, ?_, fun κ' hκ' => ?_⟩
    · rw [← gap_eq_param_deg2 M hκs.1 v hv x₁' x₂' hx hdarts h1 h2]; exact hnz κs hκs.2.2
    · have := hcone κ' hκ'.2.2
      rwa [gap_eq_param_deg2 M hκ'.1 v hv x₁' x₂' hx hdarts h1 h2] at this
  · refine ⟨EuclideanSpace.single ⟨0, hd⟩ 1, ?_, fun κ' hκ' => absurd ⟨κ', hκ'⟩ hne⟩
    intro h
    have := congrArg (fun u : Mom d => u ⟨0, hd⟩) h
    simp at this

variable {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- **The dart gap of a critical present atom** is `± gvec y`, nonzero on the class. -/
theorem present_gap {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} (hB : BalS h.s)
    {B : Set (D₀ → (Fin d → ℤ))} (hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h) {y : V}
    (hy : IsCritA L γ η h y) :
    ∃ x₁ x₂ : h.s.D, x₁ ≠ x₂ ∧ h.s.M.dartsAt y = {x₁, x₂} ∧ h.s.M.out x₁ = true ∧ h.s.M.out x₂ = false ∧
      ∀ k0 ∈ B, (Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = gvec h L w k0 y ∨
        Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = -gvec h L w k0 y) ∧ gvec h L w k0 y ≠ 0 := by
  obtain ⟨hym, hyd, R, hyc, -⟩ := hy
  have hne : h.s.cls y ≠ .eps := by rw [hyc]; exact fun e => by cases e
  obtain ⟨x₁, x₂, hx, hdarts, h1, h2⟩ := darts_of_bal hB hym hne hyd
  have hat : ∀ x ∈ ({x₁, x₂} : Finset h.s.D), h.s.M.atom x = y := by
    intro x hx'
    rw [← hdarts] at hx'
    simpa [Molecule.dartsAt] using hx'
  refine ⟨x₁, x₂, hx, hdarts, h1, h2, fun k0 hk0 => ?_⟩
  obtain ⟨p, vis, hp, hg⟩ := (hRI k0 hk0).2.dg y hym hne x₂ x₁ (hat x₂ (by simp)) (hat x₁ (by simp)) h2 h1
  obtain ⟨-, p', vis', hp', -, -, -, hsg⟩ := ((hRI k0 hk0).1.ok y hym).1 R 0 hyc
  rw [hp] at hp'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hp')
  have hgv : gvec h L w k0 y = pgap L w k0 p := by unfold gvec; rw [hp]
  have hswap : Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = -Molecule.gapAt L w (k0 ∘ h.s.down) x₂ x₁ := by
    unfold Molecule.gapAt; abel
  refine ⟨?_, by rw [hgv]; exact gapKind_SG_ne_zero hsg⟩
  rw [hswap, hgv]
  rcases hg with e | e
  · right; rw [e]
  · left; rw [e, neg_neg]

/-- **The cut cone of a class around a critical present atom.** -/
theorem cutCone_of_crit {L γ δ η : ℝ} {w : Mom d} {h : HSt V D₀} (hd : 0 < d) (hB : BalS h.s)
    {B : Set (D₀ → (Fin d → ℤ))} (hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h) {y : V}
    (hy : IsCritA L γ η h y) (x₁ x₂ : h.s.D)
    (hcone : ∀ k0 ∈ B, InCone (L ^ (-6 * η)) (Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂) (gvec h L w k0 y)) :
    CutCone h.s.M x₁ x₂ L γ δ (L ^ (-6 * η)) w (AdmS (fun k => k ∈ B) h.s) := by
  obtain ⟨x₁', x₂', hx, hdarts, h1, h2, hgv⟩ := present_gap hB hRI hy
  refine cutCone_of_present x₁ x₂ w _ y hy.1 x₁' x₂' hx hdarts h1 h2 hd ?_ ?_
  · rintro κ' ⟨k0, hk0, rfl⟩
    rcases (hgv k0 hk0).1 with e | e
    · rw [e]; exact (hgv k0 hk0).2
    · rw [e]; exact neg_ne_zero.2 (hgv k0 hk0).2
  · rintro κ' ⟨k0, hk0, rfl⟩
    exact inCone_pm_ctr (hgv k0 hk0).1 (hcone k0 hk0)

/-- **The joint cone of a class around a critical present atom**, for any cut `K'` whose upper joint has the record
`p` (the same post state as the node's cut). -/
theorem jointCone_of_crit {L γ δ η : ℝ} {w : Mom d} {h : HSt V D₀} (hd : 0 < d) (hB : BalS h.s)
    {B : Set (D₀ → (Fin d → ℤ))} (hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h) {y : V}
    (hy : IsCritA L γ η h y) (K' : Step1.VineCut Src.γL h.s.M) (p : D₀ × D₀) (hp : h.s.pr K'.x₁ K'.x₂ = p)
    (hcone : ∀ k0 ∈ B, InCone (L ^ (-6 * η)) (pgap L w k0 p) (gvec h L w k0 y)) :
    JointCone K' L γ δ η w (AdmS (fun k => k ∈ B) h.s) := by
  obtain ⟨x₁', x₂', hx, hdarts, h1, h2, hgv⟩ := present_gap hB hRI hy
  refine jointCone_of_present K' w _ y hy.1 x₁' x₂' hx hdarts h1 h2 hd ?_ ?_
  · rintro κ' ⟨k0, hk0, rfl⟩
    rcases (hgv k0 hk0).1 with e | e
    · rw [e]; exact (hgv k0 hk0).2
    · rw [e]; exact neg_ne_zero.2 (hgv k0 hk0).2
  · rintro κ' ⟨k0, hk0, rfl⟩
    have e : Molecule.gapAt L w (k0 ∘ h.s.down) K'.x₁ K'.x₂ = pgap L w k0 p := by
      rw [← hp]; rfl
    rw [e]
    exact inCone_pm_ctr (hgv k0 hk0).1 (hcone k0 hk0)

end WaveTurbulence.GammaLow.FinalCount.Ghost
