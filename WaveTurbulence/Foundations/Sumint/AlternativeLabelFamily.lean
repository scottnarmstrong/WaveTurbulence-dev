/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedSpatialExpansion
public import WaveTurbulence.Foundations.Sumint.SourceEdgeBoxes

/-!
# The literal finite family of alternative localization labels

The family depends on primary labels and the prescribed output-ball
centres, never on the actual output momenta. Outside this family the
entire localized source weight product vanishes pointwise.
-/

public section

open Finset Set

namespace WaveTurbulence.Sumint

/-- Alternative labels permitted by the fixed predecessor edge boxes. -/
@[expose] noncomputable def sourceAlternativeLabelSet {d : ℕ} (D : SumintDatum d)
    (a : D.S.VIdx → Fin d → ℤ) : Set (D.S.VIdx → Fin d → ℤ) :=
  predecessorLabelSet D.prev (fun v => Counting.latticeBox
    (edgeCenter (fun v w => (D.σk v w : ℝ)) (fun v j => (D.σe v j : ℝ)) a
      (fun j k => D.centre j k) v) (4*(D.Λ v : ℝ)))

/-- Acyclic predecessor identities make the actual alternative family finite. -/
theorem sourceAlternativeLabelSet_finite {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx → Fin d → ℤ) : (sourceAlternativeLabelSet D a).Finite :=
  (source_predecessor_box_count D hD
    (edgeCenter (fun v w => (D.σk v w : ℝ)) (fun v j => (D.σe v j : ℝ)) a
      (fun j k => D.centre j k))).1

/-- The finite alternative family used in the coefficient recombination. -/
@[expose] noncomputable def sourceAlternativeLabels {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx → Fin d → ℤ) : Finset (D.S.VIdx → Fin d → ℤ) :=
  (sourceAlternativeLabelSet_finite D hD a).toFinset

/-- Finite-family membership is exactly the source edge-box condition. -/
theorem mem_sourceAlternativeLabels {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    b ∈ sourceAlternativeLabels D hD a ↔ b ∈ sourceAlternativeLabelSet D a := by
  exact Set.Finite.mem_toFinset _

/-- The actual family has only an exponential-in-M cardinality. -/
theorem card_sourceAlternativeLabels_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx → Fin d → ℤ) :
    ((sourceAlternativeLabels D hD a).card : ℝ) ≤ ((9:ℝ)^d*A^d)^D.S.M := by
  have hh := (source_predecessor_box_count D hD
    (edgeCenter (fun v w => (D.σk v w : ℝ)) (fun v j => (D.σe v j : ℝ)) a
      (fun j k => D.centre j k))).2
  have he : (sourceAlternativeLabelSet D a).ncard = (sourceAlternativeLabels D hD a).card :=
    Set.ncard_eq_toFinset_card _ (sourceAlternativeLabelSet_finite D hD a)
  change ((sourceAlternativeLabelSet D a).ncard : ℝ) ≤ ((9:ℝ)^d*A^d)^D.S.M at hh
  rwa [he] at hh

/-- A nonzero localized source product has every primary and alternative profile nonzero. -/
theorem localizedSourceWeight_nonzero_profiles {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (x : D.S.VIdx → Fin d → ℤ)
    (hh : localizedSourceWeight D L a b E x ≠ 0) :
    (∀ v, localizationProfile (a v) (D.kVec L x E v) ≠ 0) ∧
      (∀ v, localizationProfile (b v) (D.ℓVec L x E v) ≠ 0) := by
  classical
  constructor
  · intro v hv
    apply hh
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [localizedWeight,hv,zero_smul,zero_mul]
  · intro v hv
    apply hh
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [localizedWeight,hv,zero_smul,mul_zero]

/-- Alternative labels outside the fixed family contribute zero at every permitted output. -/
theorem localizedSourceWeight_eq_zero_of_not_alternative {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1)
    (x : D.S.VIdx → Fin d → ℤ) (hb : b ∉ sourceAlternativeLabels D hD a) :
    localizedSourceWeight D L a b E x = 0 := by
  by_contra hh
  obtain ⟨hK,hL⟩ := localizedSourceWeight_nonzero_profiles D L a b E x hh
  apply hb
  apply (mem_sourceAlternativeLabels D hD a b).mpr
  exact source_edge_labels_mem D hD x E a b hK hL hE

end WaveTurbulence.Sumint
