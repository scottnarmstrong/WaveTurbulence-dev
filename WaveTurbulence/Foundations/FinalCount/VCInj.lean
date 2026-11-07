/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCoords
public import WaveTurbulence.Foundations.FinalCount.VCSquare
/-! # VINE-COUNT part 16: the chart coordinates determine the labels of the removed vine (injectivity). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem latticePoint_zsmul (L : ℝ) (n : ℤ) (z : Fin d → ℤ) : latticePoint L (n • z) = n • latticePoint L z := by
  ext i; simp [latticePoint, mul_div_assoc]

theorem latticePoint_sum {ι : Type*} (L : ℝ) (s : Finset ι) (f : ι → (Fin d → ℤ)) :
    latticePoint L (∑ i ∈ s, f i) = ∑ i ∈ s, latticePoint L (f i) := by
  ext j; simp [latticePoint, Finset.sum_apply, Finset.sum_div]

theorem latticePoint_injective {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro z z' h
  funext i
  have h' := congrArg (fun v : Mom d => v i) h
  have h'' : ((z i : ℤ) : ℝ) / L = ((z' i : ℤ) : ℝ) / L := by simpa [latticePoint] using h'
  have : ((z i : ℤ) : ℝ) = ((z' i : ℤ) : ℝ) := by
    field_simp at h''; exact h''
  exact_mod_cast this

section Inj
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower) (hMol : M.IsMolecule)
  (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)
include hB hMol hM

/-- The label of an internal bond is an integer combination of the chart coordinates and the gap. -/
theorem bond_label_eq {L : ℝ} (hL : L ≠ 0) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (e : Bond M K.C.atoms) :
    κ e.1 = ∑ i, A.decodeFree e i • xint K A κ i + A.decodeGap e • rint K κ := by
  have h1 := A.decode_eq w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc)) e
  rw [Equiv.symm_apply_apply] at h1
  have h2 : (kfibElt K hB hMol hM L w c κ hdec hc).1 e = Molecule.kvec L w κ e.1 :=
    kfibElt_val K hB hMol hM L w c κ hdec hc e
  rw [h2] at h1
  have hx : ∀ i, A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc) i =
      latticePoint L (xint K A κ i) := fun i => chart_coord_eq K hB hMol hM A L w c κ hdec hc i
  simp_rw [hx, gapAt_eq_lattice K L w κ] at h1
  apply latticePoint_injective hL
  rw [latticePoint_add, latticePoint_sum, latticePoint_zsmul]
  simp_rw [latticePoint_zsmul]
  unfold Molecule.kvec at h1
  rw [add_assoc] at h1
  exact add_left_cancel h1

omit hMol hM in
theorem restrS_apply_group (κ : D → (Fin d → ℤ)) {x : D} (hg : M.InGroup K.C.atoms x) : K.restrS κ x = κ x := by
  unfold VineCut.restrS
  rw [if_pos]
  rw [cutMol_atom_of_inGroup K hB hg]; exact hg.1

omit hMol hM in
theorem rint_restrS (κ : D → (Fin d → ℤ)) : rint K (K.restrS κ) = rint K κ := by
  unfold rint
  rw [restrS_apply_group K hB κ (x₁_inGroup K), restrS_apply_group K hB κ (x₂_inGroup K)]

omit hMol hM in
theorem xint_restrS (κ : D → (Fin d → ℤ)) (i : Fin A.indexing.shape.n) :
    xint K A (K.restrS κ) i = xint K A κ i := by
  have hO : ∀ p, Oint K (K.restrS κ) p = Oint K κ p := by
    intro p
    rcases p with e | j
    · simp only [Oint]
      apply restrS_apply_group K hB κ
      have he := e.2
      unfold internalBondSet at he
      exact (Finset.mem_filter.mp he).2
    · simp only [Oint, rint_restrS K hB]
  unfold xint
  rw [hO, hO]

theorem restrS_eq_of_coords {L : ℝ} (hL : L ≠ 0) (w : Mom d) (c₁ c₂ : V → Mom d) (κ₁ κ₂ : D → (Fin d → ℤ))
    (hd₁ : M.IsDecoration L w c₁ κ₁) (hd₂ : M.IsDecoration L w c₂ κ₂)
    (hc₁ : ∀ x ∈ M.atoms, M.deg x = 4 → c₁ x = 0) (hc₂ : ∀ x ∈ M.atoms, M.deg x = 4 → c₂ x = 0)
    (hx : ∀ i, xint K A κ₁ i = xint K A κ₂ i) (hr : rint K κ₁ = rint K κ₂) : K.restrS κ₁ = K.restrS κ₂ := by
  have hbond : ∀ e : Bond M K.C.atoms, κ₁ e.1 = κ₂ e.1 := by
    intro e
    rw [bond_label_eq K hB hMol hM A hL w c₁ κ₁ hd₁ hc₁ e, bond_label_eq K hB hMol hM A hL w c₂ κ₂ hd₂ hc₂ e]
    simp_rw [hx, hr]
  funext x
  unfold VineCut.restrS
  by_cases hxs : K.cutMol.atom x ∈ K.C.atoms
  · rw [if_pos hxs, if_pos hxs]
    have hg : M.InGroup K.C.atoms x := (vc_dart_iff K hB x).mp (not_not.mpr hxs)
    by_cases ho : M.out x = true
    · exact hbond ⟨x, Square.mem_bond ho (by unfold Molecule.ends; rfl) hg.1 hg.2⟩
    · have hom : M.out (M.mate x) = true := by
        rw [M.out_mate]; simpa using ho
      have := hbond ⟨M.mate x, Square.mem_bond hom (by unfold Molecule.ends; rfl) (inGroup_mate K hB hg).1 (inGroup_mate K hB hg).2⟩
      simpa [hd₁.1 x, hd₂.1 x] using this
  · rw [if_neg hxs, if_neg hxs]

end Inj

end WaveTurbulence.VineCount
