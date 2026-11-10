/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Adm
public import WaveTurbulence.Foundations.FinalCount.G3Hist
public import WaveTurbulence.Foundations.FinalCount.Prop94Statement
/-! **FINALCOUNT-G3: the `ι_v ≠ 0` ball of an earlier cut** (excessprop1 (1), glue of `IotaHit` to the fixed ball of
DH23 L1801).

`IotaBall` is the fixed-ball form of FINALCOUNT-G2 (`hball` of `alphaCut_excess`, `triangle_excess`): for every parameter
triple `(c, β, k0)` of the current molecule there is a centre `r₀` with `‖gap - r₀‖ ≤ ρ` on all decorations of that
triple.  `AtomRelU` is the uniform (over the admissible class `Adm0`) *charge relation* of the cut atoms: a present atom
`a` carrying the record of the cut `q` has charge `± gap(q) + c₀` (`c₀` a constant: `0` for the half that keeps the two cut
darts, the charge of the cut `ε`-atom for the other half).  An earlier cut that is still carried by a present atom
(`IotaUnif`) therefore fixes the ball: its centre is `∓ (c_a - c₀)`, a function of the parameters. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The fixed-ball form of the `ι` condition** (DH23 L1801; the `hball` hypothesis of FINALCOUNT-G2). -/
def IotaBall {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (x₁ x₂ : D) (ρ : ℝ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' x₁ x₂ - r₀‖ ≤ ρ

/-- The charge relation of the cut atoms, uniform over the admissible class. -/
def AtomRelU (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L : ℝ) (w : Mom d) (h : HSt V D₀) : Prop :=
  ∀ a ∈ h.s.M.atoms, ∀ q vis, h.crec a = some (q, vis) →
    ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ ∃ c₀ : Mom d, ∀ k0, Adm0 k0 →
      chargeAt h.s.M L w (k0 ∘ h.s.down) a = sgn • pgap L w k0 q + c₀

/-- **`ι_v ≠ 0` with an earlier cut that is still carried by a present atom**, uniformly on `Adm0`. -/
def IotaUnif (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L η : ℝ) (w : Mom d) (h : HSt V D₀) (p : D₀ × D₀) (R : ℝ) :
    Prop :=
  ∃ q ∈ h.hist, (∃ a ∈ h.s.M.atoms, ∃ vis, h.crec a = some (q, vis)) ∧ ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
    ∀ k0, Adm0 k0 → 0 < ‖pgap L w k0 p + sg • pgap L w k0 q‖ ∧
      ‖pgap L w k0 p + sg • pgap L w k0 q‖ ≤ L ^ (-50 * η) * R

theorem IotaUnif.ball {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {L γ δ η R : ℝ} {w : Mom d} {h : HSt V D₀}
    (hAR : AtomRelU Adm0 L w h) {x₁ x₂ : h.s.D} (hI : IotaUnif Adm0 L η w h (h.s.pr x₁ x₂) R) :
    IotaBall h.s.M L γ δ w (AdmS Adm0 h.s) x₁ x₂ (L ^ (-50 * η) * R) := by
  obtain ⟨q, -, ⟨a, ha, vis, hc⟩, sg, hsg, hb⟩ := hI
  obtain ⟨sgn, hsgn, c₀, hrel⟩ := hAR a ha q vis hc
  intro c β k0' _
  refine ⟨-(sg * sgn) • (c a - c₀), fun κ' hκ' => ?_⟩
  obtain ⟨k0, hk0, rfl⟩ := hκ'.2.2
  have hch : chargeAt h.s.M L w (k0 ∘ h.s.down) a = c a := hκ'.1.2 a ha
  have e := hrel k0 hk0
  rw [hch] at e
  have hss : sgn * sgn = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hq : sg • pgap L w k0 q = (sg * sgn) • (c a - c₀) := by
    have : pgap L w k0 q = sgn • (c a - c₀) := by
      rw [e]; simp only [add_sub_cancel_right, smul_smul, hss, one_smul]
    rw [this, smul_smul]
  have := (hb k0 hk0).2
  have e2 : Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ - -(sg * sgn) • (c a - c₀) =
      pgap L w k0 (h.s.pr x₁ x₂) + sg • pgap L w k0 q := by
    rw [hq, neg_smul, sub_neg_eq_add]; rfl
  rw [e2]; exact this

/-- `0 < ‖difference of two gap combinations‖` forces the radius to be at least the lattice spacing. -/
theorem pgap_comb_lattice (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) (p q : D₀ × D₀) (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) :
    ∃ n : Fin d → ℤ, pgap L w k0 p + sg • pgap L w k0 q = latticePoint L n := by
  rcases hsg with rfl | rfl
  · refine ⟨k0 p.1 - k0 p.2 + (k0 q.1 - k0 q.2), ?_⟩
    unfold pgap Molecule.gapAt Molecule.kvec
    ext i; simp [latticePoint]; ring
  · refine ⟨k0 p.1 - k0 p.2 - (k0 q.1 - k0 q.2), ?_⟩
    unfold pgap Molecule.gapAt Molecule.kvec
    ext i; simp [latticePoint]; ring

theorem IotaUnif.radius {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {L η R : ℝ} {w : Mom d} {h : HSt V D₀}
    {p : D₀ × D₀} (hL : 0 < L) (hI : IotaUnif Adm0 L η w h p R) {k0 : D₀ → (Fin d → ℤ)} (hk : Adm0 k0) :
    L⁻¹ ≤ L ^ (-50 * η) * R := by
  obtain ⟨q, -, -, sg, hsg, hb⟩ := hI
  obtain ⟨hpos, hle⟩ := hb k0 hk
  obtain ⟨n, hn⟩ := pgap_comb_lattice L w k0 p q sg hsg
  rw [hn] at hpos hle
  refine (norm_latticePoint_ge hL _ ?_).trans hle
  intro h0
  rw [h0] at hpos
  have : latticePoint L (0 : Fin d → ℤ) = 0 := by ext i; simp [latticePoint]
  rw [this, norm_zero] at hpos
  exact lt_irrefl _ hpos

end WaveTurbulence.FinalCountG3
