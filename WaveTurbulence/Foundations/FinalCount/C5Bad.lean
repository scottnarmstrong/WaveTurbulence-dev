/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Cut
import Mathlib.Tactic

/-! # Prop 9.6, case (5): the reduced molecule has no excluded `β`-cut (DH23 L1887) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Away from `v` and the new atom the degrees do not change under a cut. -/
theorem cut_deg_of_ne' (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D} {u : V} (hu : u ≠ v) (hu2 : u ≠ v₂) :
    (M.cut v v₂ x₁ x₂).deg u = M.deg u := by
  classical
  unfold Molecule.deg Molecule.dartsAt
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and]
  change (if _ then _ else _) = u ↔ _
  split_ifs with h
  · exact ⟨fun h' => absurd h'.symm hu2, fun h' => absurd (h'.symm.trans h.1) hu⟩
  · exact Iff.rfl

/-- **`M` has no `β`-cut at an `ε`-atom** (from `FinalDec.noBetaCut` and `epsLG`), given an admissible decoration. -/
theorem noBeta_eps {d : ℕ} {M : Molecule V D} {cls : V → Cls} {odd : Prop} {L γ η : ℝ}
    {Adm : (D → (Fin d → ℤ)) → Prop} (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm)
    (hLp : 0 < L) {κ : D → (Fin d → ℤ)} (hκ : Adm κ) {v : V} (hv : v ∈ M.atoms) (hε : (cls v).IsEps)
    {v₂ : V} {x₁ x₂ : D} (hc : M.IsCutData v v₂ x₁ x₂) : M.IsAlphaCut v v₂ x₁ x₂ := by
  have hdeg3 : 3 ≤ M.deg v := by
    have := (hS.classes v hv).not.mpr (fun h => h hε)
    omega
  refine hF.noBetaCut κ hκ v hv hdeg3 v₂ x₁ x₂ hc ?_
  have hlt := hF.epsLG κ hκ v hv hε x₁ x₂ hc.2.2.1 hc.2.2.2.1 (by rw [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]; simp)
  intro h0
  have : (0 : ℝ) < L ^ (-γ + η) := Real.rpow_pos_of_pos hLp _
  have h' : Molecule.kvec L (0 : Mom d) κ x₁ - Molecule.kvec L (0 : Mom d) κ x₂ = 0 := h0
  rw [h', norm_zero] at hlt
  linarith

/-- **Erasing a chain creates no `β`-cut** (S1). -/
theorem not_bad_erase (M : Molecule V D) (K0 : Finset V)
    (hconn : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, M.SameComponent u w)
    (hconnN : ∀ u ∈ (Degen.eraseAtoms M K0).atoms, ∀ w ∈ (Degen.eraseAtoms M K0).atoms,
      (Degen.eraseAtoms M K0).SameComponent u w)
    (hfr : ∃ w, w ∉ M.atoms) (hdeg4 : ∀ u ∈ (Degen.eraseAtoms M K0).atoms, M.deg u = 4)
    (hNB : ∀ v ∈ (Degen.eraseAtoms M K0).atoms, ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂) :
    ¬ HasBadBetaCut (Degen.eraseAtoms M K0) := by
  classical
  rintro ⟨v, v₂, x₁, x₂, hc, hna, hdeg⟩
  obtain ⟨v₂', hv₂'⟩ := hfr
  have hsep := not_sameComponent_of_not_alpha _ hconnN hc hna
  have hdegN : ∀ u ∈ (Degen.eraseAtoms M K0).atoms,
      ((Degen.eraseAtoms M K0).cut v v₂ x₁ x₂).SameComponent v u → u ≠ v →
      (Degen.eraseAtoms M K0).deg u = M.deg u := by
    intro u hu hsame hne
    have h1 := hdeg u (by change u ∈ insert v₂ _; exact mem_insert_of_mem hu) hsame hne
    have hu2 : u ≠ v₂ := fun h => hc.2.1 (h ▸ hu)
    have h2 : ((Degen.eraseAtoms M K0).cut v v₂ x₁ x₂).deg u = (Degen.eraseAtoms M K0).deg u :=
      cut_deg_of_ne' _ hne hu2
    rw [h1] at h2
    rw [← h2, hdeg4 u hu]
  obtain ⟨hcM, hsepM⟩ := cut_lift_erase M K0 hc hsep hdegN hv₂'
  exact not_alpha_of_not_sameComponent M hconn hcM hsepM (hNB v hc.1 v₂' _ _ hcM)

end
end WaveTurbulence.FinalCountG8
