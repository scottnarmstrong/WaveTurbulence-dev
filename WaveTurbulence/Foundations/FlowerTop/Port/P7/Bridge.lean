/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSwap
/-! FLOWER-P7: the bridge `kernelKgen` (no designated nodes) `=` `kernelK` for plain gardens.  The proofs of
`integral_subtype_congr` and `kernelKgen_noFix` are copied from flower-reg `WaveBDraft/FlowerProbes.lean`
(sha256 a5a2598d6fd07d6c139fff9aeb4cdda78d23d59d8086076aa41b6905d5760c24, recorded in COPIED-SHA256SUMS). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open MeasureTheory Finset Set TTree

/-- Integrals over function spaces on two subtypes defined by equivalent predicates agree. -/
theorem integral_subtype_congr {ι : Type*} [Fintype ι] {Pp Q : ι → Prop} [DecidablePred Pp]
    [DecidablePred Q] (h : ∀ i, Pp i ↔ Q i) (G : ({i // Q i} → ℝ) → ℂ) :
    ∫ τ : {i // Pp i} → ℝ, G (fun q => τ ⟨q.1, (h q.1).2 q.2⟩) = ∫ σ : {i // Q i} → ℝ, G σ := by
  let e : {i // Pp i} ≃ {i // Q i} := Equiv.subtypeEquivRight h
  have hmp := measurePreserving_piCongrLeft (fun _ : {i // Q i} => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : {i // Q i} => ℝ) e) G
  convert this using 2 with τ
  funext τ
  congr 1

variable (L γ δ : ℝ) {d : ℕ}

/-- **Bridge (no designated nodes):** for a plain garden, `kernelKgen` with no designated nodes, no removed
phases and weight `1` is `kernelK` (for any `s`: a plain garden has no flower or lone parents). -/
theorem kernelKgen_noFix {w : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up k₀ nroot nfl =
      kernelK L γ δ F LG up s k₀ nroot nfl := by
  classical
  have hnf : ∀ b, ¬ LG.garden.IsFlowerParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsFlower, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  have hnl : ∀ b, ¬ LG.garden.IsLoneParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsLone, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  unfold kernelKgen kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  simp only [Complex.ofReal_one, mul_one]
  congr 2
  have hoff : phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k₀ κ.1) =
      phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) := by
    funext τ
    simp [phaseProdOff, phaseProd]
  rw [hoff]
  unfold phaseIntegral
  have hfree : ∀ b : GBranch LG.garden.tree, (none : Option ℝ) = none ↔ ¬ LG.garden.IsFlowerParent b :=
    fun b => ⟨fun _ => hnf b, fun _ => rfl⟩
  have key := integral_subtype_congr (Pp := fun b => ¬ LG.garden.IsFlowerParent b)
    (Q := fun _ => (none : Option ℝ) = none) (fun b => (hfree b).symm)
    (fun σ => (kDomainFix LG up (fun _ => none)).indicator
      (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1))
        (LG.garden.extendFix (fun _ => none) σ))
  refine key.symm.trans ?_
  show ∫ τ : LG.garden.FreeBranch → ℝ, _ = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  have hext : LG.garden.extendFix (fun _ => none) (fun q => τ ⟨q.1, hnf q.1⟩) =
      LG.garden.extendTime s τ := by
    funext b
    simp [Garden.extendFix, Garden.extendTime, hnf b]
  rw [hext]
  have hdom : LG.garden.extendTime s τ ∈ kDomainFix LG up (fun _ => none) ↔
      LG.garden.extendTime s τ ∈ kDomain LG up s := by
    constructor
    · intro h b
      obtain ⟨h1, h2, h3, h4⟩ := (h b).1 rfl
      exact ⟨h1, h2, h3, h4, fun b' hb' => (h b).2 b' hb' (Or.inl rfl), fun h' => absurd h' (hnl b)⟩
    · intro h b
      exact ⟨fun _ => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩, fun b' hb' _ =>
        (h b).2.2.2.2.1 b' hb'⟩
  by_cases hmem : LG.garden.extendTime s τ ∈ kDomain LG up s
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hdom.2 hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem (hdom.1 h))]

end WaveTurbulence.FlowerP7
