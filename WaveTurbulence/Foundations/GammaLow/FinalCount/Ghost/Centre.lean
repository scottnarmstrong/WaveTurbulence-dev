/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone3
/-! **L6E GHOST, part 21: the cone centre is a present parameter** (M1-R2 Lemma 6.2(iii); NOTES §10.2).

At the creation step `s(P)` of the later ghost `y`, the earlier ghost `x` is a present atom of degree `2` (it keeps its
two triangle bonds from its creation on). Its gap along its two darts is its parameter `c_x` in every decoration of a
parameter class (conservation at `x`). Hence the decoration-level cone hypothesis of NOTES §10.2
(`hcone : ∀ κ' ∈ Adm, sin²∠(g_y, g_x) ≤ θ₀²`) gives the class-level `ConeAt` with the fixed centre `c_x`.
* `gap_eq_param_deg2`: `gapAt κ x₁ x₂ = c x` for the two darts of a degree-2 atom (out `x₁`, in `x₂`);
* `coneAt_of_present`: `ConeAt` from the cone around the present atom's gap. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Conservation at a degree-2 atom**: its gap is its parameter. -/
theorem gap_eq_param_deg2 (M : Molecule V D) {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hdec : M.IsDecoration L w c κ) (v : V) (hv : v ∈ M.atoms) (x₁ x₂ : D) (hx : x₁ ≠ x₂)
    (hdarts : M.dartsAt v = {x₁, x₂}) (h1 : M.out x₁ = true) (h2 : M.out x₂ = false) :
    Molecule.gapAt L w κ x₁ x₂ = c v := by
  have h := hdec.2 v hv
  rw [hdarts, Finset.sum_pair hx] at h
  unfold Molecule.dartSign at h
  rw [if_pos h1, if_neg (by rw [h2]; simp)] at h
  unfold Molecule.gapAt
  rw [← h]
  simp only [one_smul, neg_one_smul]
  abel

/-- **Lemma 6.2(iii) in Lean**: the cone around the gap of a present degree-2 atom `v` (darts `x₁` out, `x₂` in) is a
cone around the fixed centre `c v` in each parameter class. -/
theorem coneAt_of_present {M : Molecule V D} (T : TriData M) {L γ δ η : ℝ} (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (j : Fin 3) (v : V) (hv : v ∈ M.atoms) (x₁ x₂ : D) (hx : x₁ ≠ x₂)
    (hdarts : M.dartsAt v = {x₁, x₂}) (h1 : M.out x₁ = true) (h2 : M.out x₂ = false) (hd : 0 < d)
    (hnz : ∀ κ', Adm κ' → Molecule.gapAt L w κ' x₁ x₂ ≠ 0)
    (hcone : ∀ κ', Adm κ' →
      InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ' (T.a j) (T.b j)) (Molecule.gapAt L w κ' x₁ x₂)) :
    ConeAt T L γ δ η w Adm j := by
  intro c β k0 _
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  · obtain ⟨κs, hκs⟩ := hne
    refine ⟨c v, ?_, fun κ' hκ' => ?_⟩
    · rw [← gap_eq_param_deg2 M hκs.1 v hv x₁ x₂ hx hdarts h1 h2]; exact hnz κs hκs.2.2
    · have := hcone κ' hκ'.2.2
      rwa [gap_eq_param_deg2 M hκ'.1 v hv x₁ x₂ hx hdarts h1 h2] at this
  · refine ⟨EuclideanSpace.single ⟨0, hd⟩ 1, ?_, fun κ' hκ' => absurd ⟨κ', hκ'⟩ hne⟩
    intro h
    have := congrArg (fun u : Mom d => u ⟨0, hd⟩) h
    simp at this

end WaveTurbulence.GammaLow.FinalCount.Ghost
