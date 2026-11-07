/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Iso
/-! **FINALCOUNT-ASSEMBLY, A1: the base change `w ↦ w'` of the counting quantities.**

For a molecule whose degree-`4` atoms are balanced (two incoming, two outgoing bonds), `countE` does not depend on the base `w`:
a decoration of `w + ℤ_L^d` is a decoration of `w' + ℤ_L^d` with the charges `c' = c + (Σζ)(w'-w)` and the energies
`β' = β + 2⟨w'-w, c⟩ + (Σζ)|w'-w|²` (and `k0' = k0 + (w'-w)`).  The final components are counted by G8 at base `0`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- `Σ ζ = outdeg - indeg` at an atom. -/
theorem sum_dartSign (M : Molecule V D) (v : V) :
    ∑ x ∈ M.dartsAt v, M.dartSign x = (M.outdeg v : ℝ) - M.indeg v := by
  have h := Finset.sum_filter_add_sum_filter_not (M.dartsAt v) (fun x => M.out x = true) (fun x => M.dartSign x)
  rw [← h]
  have h1 : ∑ x ∈ (M.dartsAt v).filter (fun x => M.out x = true), M.dartSign x = (M.outdeg v : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun x hx => by simp [Molecule.dartSign, (Finset.mem_filter.1 hx).2])]
    simp [Molecule.outdeg]
  have h2 : ∑ x ∈ (M.dartsAt v).filter (fun x => ¬ M.out x = true), M.dartSign x = -(M.indeg v : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℝ)) (fun x hx => by simp [Molecule.dartSign, (Finset.mem_filter.1 hx).2])]
    have : ((M.dartsAt v).filter (fun x => ¬ M.out x = true)) = (M.dartsAt v).filter fun x => M.out x = false := by
      ext x; simp
    rw [this]; simp [Molecule.indeg]
  rw [h1, h2]; ring

/-- A balanced degree-`4` atom (two outgoing, two incoming) has `Σ ζ = 0`. -/
theorem sum_dartSign_deg4 {M : Molecule V D} (hM : M.IsMolecule) {v : V} (hv : v ∈ M.atoms) (h4 : M.deg v = 4) :
    ∑ x ∈ M.dartsAt v, M.dartSign x = 0 := by
  rw [sum_dartSign]
  obtain ⟨ho, hi⟩ := hM.1 v hv
  have hd : M.deg v = M.outdeg v + M.indeg v := by
    unfold Molecule.deg Molecule.outdeg Molecule.indeg
    have := Finset.card_filter_add_card_filter_not (s := M.dartsAt v) (fun x => M.out x = true)
    have e : ((M.dartsAt v).filter (fun x => ¬ M.out x = true)) = (M.dartsAt v).filter fun x => M.out x = false := by
      ext x; simp
    rw [e] at this; omega
  have : M.outdeg v = 2 := by omega
  have : M.indeg v = 2 := by omega
  simp [*]

/-- The vector of a dart at base `w'` is the vector at base `w` shifted by `w' - w`. -/
theorem kvec_shift (L : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (x : D) :
    Molecule.kvec L w' κ x = Molecule.kvec L w κ x + (w' - w) := by
  unfold Molecule.kvec; abel

theorem decoration_shift (M : Molecule V D) (L : ℝ) (w w' : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (h : M.IsDecoration L w c κ) :
    M.IsDecoration L w' (fun v => c v + (∑ x ∈ M.dartsAt v, M.dartSign x) • (w' - w)) κ := by
  refine ⟨h.1, fun v hv => ?_⟩
  have := h.2 v hv
  simp only [kvec_shift L w w', smul_add]
  rw [Finset.sum_add_distrib, this, ← Finset.sum_smul]

theorem gamma_shift (M : Molecule V D) (L : ℝ) (w w' : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (h : M.IsDecoration L w c κ) (v : V) (hv : v ∈ M.atoms) :
    M.Gamma L w' κ v = M.Gamma L w κ v + 2 * inner ℝ (w' - w) (c v) + (∑ x ∈ M.dartsAt v, M.dartSign x) * ‖w' - w‖ ^ 2 := by
  unfold Molecule.Gamma
  have e : ∀ x, ‖Molecule.kvec L w' κ x‖ ^ 2 = ‖Molecule.kvec L w κ x‖ ^ 2 + 2 * inner ℝ (w' - w) (Molecule.kvec L w κ x) +
      ‖w' - w‖ ^ 2 := by
    intro x
    rw [kvec_shift L w w', norm_add_sq_real, real_inner_comm]
  simp only [e, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ x ∈ M.dartsAt v, M.dartSign x * (2 * inner ℝ (w' - w) (Molecule.kvec L w κ x)) =
      2 * inner ℝ (w' - w) (c v) := by
    rw [← h.2 v hv, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_smul_right]; ring
  rw [h2, ← Finset.sum_mul]

/-- **`countE` is monotone under base change** (hence invariant, by symmetry) when the degree-`4` atoms are balanced. -/
theorem countE_le_shift (M : Molecule V D) (hbal : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x = 0)
    (L γ δ : ℝ) (w w' : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    M.countE L γ δ w Adm ≤ M.countE L γ δ w' Adm := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  refine le_iSup_of_le (fun v => c v + (∑ x ∈ M.dartsAt v, M.dartSign x) • (w' - w)) (le_iSup_of_le ?_ ?_)
  · intro v hv h4; simp [hc v hv h4, hbal v hv h4]
  · refine le_iSup_of_le (fun v => β v + 2 * inner ℝ (w' - w) (c v) + (∑ x ∈ M.dartsAt v, M.dartSign x) * ‖w' - w‖ ^ 2)
      (le_iSup_of_le (fun x => k0 x + (w' - w)) (le_iSup_of_le ?_ ?_))
    · intro x; simp [hk0 x]
    · refine Set.encard_le_encard ?_
      rintro κ ⟨hdec, ⟨hres1, hres2⟩, hadm⟩
      refine ⟨decoration_shift M L w w' c κ hdec, ⟨fun v hv => ?_, fun x => ?_⟩, hadm⟩
      · rw [gamma_shift M L w w' c κ hdec v hv]
        have := hres1 v hv
        have e : M.Gamma L w κ v + 2 * inner ℝ (w' - w) (c v) + (∑ x ∈ M.dartsAt v, M.dartSign x) * ‖w' - w‖ ^ 2 -
            (β v + 2 * inner ℝ (w' - w) (c v) + (∑ x ∈ M.dartsAt v, M.dartSign x) * ‖w' - w‖ ^ 2) =
            M.Gamma L w κ v - β v := by ring
        rw [e]; exact this
      · have := hres2 x
        rw [kvec_shift L w w']
        have e : Molecule.kvec L w κ x + (w' - w) - (k0 x + (w' - w)) = Molecule.kvec L w κ x - k0 x := by abel
        rw [e]; exact this

theorem countE_base_eq (M : Molecule V D) (hbal : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x = 0)
    (L γ δ : ℝ) (w w' : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    M.countE L γ δ w Adm = M.countE L γ δ w' Adm :=
  le_antisymm (countE_le_shift M hbal L γ δ w w' Adm) (countE_le_shift M hbal L γ δ w' w Adm)

/-- `countA` does not depend on the base (balanced degree-`4` atoms). -/
theorem countA_base_eq (M : Molecule V D) (hbal : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x = 0)
    (L γ δ C₁ : ℝ) (w w' : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P = M.countA L γ δ C₁ w' Adm P := by
  unfold Molecule.countA; rw [countE_base_eq M hbal L γ δ w w' Adm]

theorem countA_base_eq_of_molecule (M : Molecule V D) (hM : M.IsMolecule)
    (L γ δ C₁ : ℝ) (w w' : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P = M.countA L γ δ C₁ w' Adm P :=
  countA_base_eq M (fun v hv h4 => sum_dartSign_deg4 hM hv h4) L γ δ C₁ w w' Adm P

end WaveTurbulence.FinalCountAsm
