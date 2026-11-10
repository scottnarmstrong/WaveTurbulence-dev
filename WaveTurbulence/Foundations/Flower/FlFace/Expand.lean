/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Domain
/-! # FL-FACE: supplement Lemma 9.1 on the `kernelKgen` time domain (exact face expansion)

This file holds the analytic steps, for a general phase product `phaseVec θ = ∏_b exp(iθ_b t_b)` (the assembly is in
`Main`). Proof: separate the selected coordinates (`splitEquiv`, measure preserving), apply Fubini, factor the integrand over
the selected nodes (`integrand_split`; the selected nodes share no constraint), integrate each selected time exactly
(`integral_slice_faces`, (9.1)), expand the product of the per-node sums over the faces (`prod_sum_faces`) and
recognize each term as the face integrand (`restFac_mul_prod_cellFac`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory Set

variable {w : ℕ}

/-! ### Separating the selected coordinates -/

section Split

variable {G : Garden w} (fix : GBranch G.tree → Option ℝ) (S : Finset (GBranch G.tree))

/-- The selected nodes as free coordinates. -/
def selEquiv (hfix : ∀ v ∈ S, fix v = none) : S ≃ {i : {b : GBranch G.tree // fix b = none} // i.1 ∈ S} where
  toFun v := ⟨⟨v.1, hfix v.1 v.2⟩, v.2⟩
  invFun i := ⟨i.1.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The free coordinates of `fixSel fix S` are the unselected free coordinates. -/
def restEquiv :
    {b : GBranch G.tree // fixSel fix S b = none} ≃ {i : {b : GBranch G.tree // fix b = none} // ¬ i.1 ∈ S} where
  toFun b := ⟨⟨b.1, (fixSel_eq_none.1 b.2).2⟩, (fixSel_eq_none.1 b.2).1⟩
  invFun i := ⟨i.1.1, fixSel_eq_none.2 ⟨i.2, i.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Free times = (selected times, remaining free times). -/
def splitEquiv (hfix : ∀ v ∈ S, fix v = none) :
    ((S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) ≃ᵐ
      ({b : GBranch G.tree // fix b = none} → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix))
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {b : GBranch G.tree // fix b = none} => ℝ)
      fun i => i.1 ∈ S).symm

theorem measurePreserving_splitEquiv (hfix : ∀ v ∈ S, fix v = none) :
    MeasurePreserving (splitEquiv fix S hfix) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (restEquiv fix S)
  have h3 := MeasurePreserving.symm _ (volume_preserving_piEquivPiSubtypeProd
    (fun _ : {b : GBranch G.tree // fix b = none} => ℝ) fun i => i.1 ∈ S)
  have hp : MeasurePreserving (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix))
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S))) volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact h1.prod h2
  exact h3.comp hp

theorem splitEquiv_apply (hfix : ∀ v ∈ S, fix v = none)
    (x : (S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) (i : {b : GBranch G.tree // fix b = none}) :
    splitEquiv fix S hfix x i =
      if h : i.1 ∈ S then x.1 ⟨i.1, h⟩ else x.2 ⟨i.1, fixSel_eq_none.2 ⟨h, i.2⟩⟩ := by
  have e : splitEquiv fix S hfix x =
      (Equiv.piEquivPiSubtypeProd (fun i : {b : GBranch G.tree // fix b = none} => i.1 ∈ S) (fun _ => ℝ)).symm
        ((Equiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix)) x.1,
          (Equiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S)) x.2) := rfl
  rw [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  split_ifs with h
  · exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) (selEquiv fix S hfix) x.1 ⟨i.1, h⟩
  · exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) (restEquiv fix S) x.2 ⟨i.1, fixSel_eq_none.2 ⟨h, i.2⟩⟩

/-- The branch times of the split free times: the selected times at `S`, the `fixSel` extension elsewhere. -/
theorem extendFix_splitEquiv (hfix : ∀ v ∈ S, fix v = none)
    (x : (S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) (b : GBranch G.tree) :
    G.extendFix fix (splitEquiv fix S hfix x) b =
      if h : b ∈ S then x.1 ⟨b, h⟩ else G.extendFix (fixSel fix S) x.2 b := by
  by_cases hb : b ∈ S
  · rw [extendFix_of_none fix _ b (hfix b hb), splitEquiv_apply]
    simp only [hb, ↓reduceDIte]
  · simp only [hb, ↓reduceDIte]
    rcases hf : fix b with _ | y
    · rw [extendFix_of_none fix _ b hf, splitEquiv_apply,
        extendFix_of_none (fixSel fix S) _ b (fixSel_eq_none.2 ⟨hb, hf⟩)]
      simp only [hb, ↓reduceDIte]
    · have hs : fixSel fix S b = some y := by simp [fixSel, hb, hf]
      rw [extendFix_of_some fix _ b hf, extendFix_of_some (fixSel fix S) _ b hs]

end Split

/-! ### The phase and integrability -/

section Phase

variable {T : Fin w → TTree}

end Phase

/-! ### The factorization over the selected nodes -/

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
  (fix : GBranch LG.garden.tree → Option ℝ) (θ : GBranch LG.garden.tree → ℝ) (S : Finset (GBranch LG.garden.tree))

end Layered

end WaveTurbulence.Flower.FlFace
