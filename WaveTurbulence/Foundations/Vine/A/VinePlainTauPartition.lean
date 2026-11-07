/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedCode
/-! The full fixed-sigma tau partition of actual plain gardens in a coarse class. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist Represents
variable {w p : ℕ} {kind : Bool}

/-- Members of a coarse class with the fixed prescription on normalized group codes. -/
def fixedSigmaPoints (a : PrescribedPrimeGarden w) : Set (PrescribedPrimeGarden w) :=
  {b | b.layered ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) ∧ b.code = a.code}

/-- Tau classes are the actual once-per-member fine LF outputs on plain gardens. -/
def plainTauClasses (a : PrescribedPrimeGarden w) : Set (Set (LayeredGarden w)) :=
  {T | ∃ b ∈ a.fixedSigmaPoints (p := p) (kind := kind), T = b.outputs (p := p) (kind := kind)}

/-- Fixing sigma on quotient supports loses no coarse-class gardens, and gives one point over each. -/
theorem fixedSigma_unique_point (a : PrescribedPrimeGarden w) {LG : LayeredGarden w}
    (h : LG ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind)) :
    ∃! b, b ∈ a.fixedSigmaPoints (p := p) (kind := kind) ∧ b.layered = LG := by
  obtain ⟨b, hb, hc⟩ := coarse_point h
  refine ⟨b, ⟨⟨hb ▸ h, hc.symm⟩, hb⟩, ?_⟩
  intro c hC
  exact eq_of_layered_code (hC.2.trans hb.symm) (hC.1.2.trans hc)

/-- Fine classes with the same normalized sigma are disjoint or identical as garden sets. -/
theorem outputs_disjoint_or_eq_of_code {a b : PrescribedPrimeGarden w} (hc : a.code = b.code) :
    Disjoint (a.outputs (p := p) (kind := kind)) (b.outputs (p := p) (kind := kind)) ∨
      a.outputs (p := p) (kind := kind) = b.outputs (p := p) (kind := kind) := by
  classical
  by_cases hd : Disjoint (a.outputs (p := p) (kind := kind)) (b.outputs (p := p) (kind := kind))
  · exact Or.inl hd
  · right
    obtain ⟨LG, ha, hb⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨c, hca, hcc, hec⟩ := output_point ha
    obtain ⟨d, hdb, hdd, hed⟩ := output_point hb
    have hcd : c = d := eq_of_layered_code (hca.trans hdb.symm) (hcc.symm.trans (hc.trans hdd))
    subst d
    exact hec.trans hed.symm

/-- Every tau class stays in the original coarse class of actual gardens. -/
theorem plainTau_subset (a : PrescribedPrimeGarden w) {T : Set (LayeredGarden w)}
    (h : T ∈ a.plainTauClasses (p := p) (kind := kind)) :
    T ⊆ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨b, hb, rfl⟩ := h
  rw [a.prime.coarse_outputs_rebase b.prime hb.1]
  exact b.prime.fine_outputs_subset_coarse b.totalSigma

/-- Every garden of the coarse class belongs to exactly one actual tau class for fixed sigma. -/
theorem existsUnique_plainTau (a : PrescribedPrimeGarden w) {LG : LayeredGarden w}
    (h : LG ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind)) :
    ∃! T : Set (LayeredGarden w), T ∈ a.plainTauClasses (p := p) (kind := kind) ∧ LG ∈ T := by
  obtain ⟨b, hb, _⟩ := fixedSigma_unique_point a h
  refine ⟨b.outputs (p := p) (kind := kind), ⟨⟨b, hb.1, rfl⟩, hb.2 ▸ b.mem_outputs_self⟩, ?_⟩
  rintro T ⟨⟨c, hc, rfl⟩, hLc⟩
  rcases outputs_disjoint_or_eq_of_code (p := p) (kind := kind) (hc.2.trans hb.1.2.symm) with hd | he
  · exact (Set.disjoint_left.mp hd hLc (hb.2 ▸ b.mem_outputs_self)).elim
  · exact he

/-- The union of the fixed-sigma classes is exactly the full coarse garden class. -/
theorem plainTau_cover (a : PrescribedPrimeGarden w) :
    ⋃₀ a.plainTauClasses (p := p) (kind := kind) = a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  ext LG
  constructor
  · rintro ⟨T, hT, hL⟩
    exact plainTau_subset a hT hL
  · intro h
    obtain ⟨T, hT, _⟩ := existsUnique_plainTau a h
    exact ⟨T, hT⟩

/-- Distinct fixed-sigma classes are disjoint on the plain-garden carrier itself. -/
theorem plainTau_pairwise (a : PrescribedPrimeGarden w) :
    (a.plainTauClasses (p := p) (kind := kind)).PairwiseDisjoint id := by
  intro T hT U hU hne
  obtain ⟨b, hb, rfl⟩ := hT
  obtain ⟨c, hc, rfl⟩ := hU
  rcases outputs_disjoint_or_eq_of_code (p := p) (kind := kind) (hb.2.trans hc.2.symm) with hd | he
  · exact hd
  · exact (hne he).elim

end WaveTurbulence.VineA.PrescribedPrimeGarden
