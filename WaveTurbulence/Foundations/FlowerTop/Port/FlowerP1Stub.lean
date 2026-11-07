/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Spine.Stage1Interface

/-!
# FLOWER-P1: the garden-side stub kernel (design C, R61 X4)

`kernelLeavesFix` generalizes `LGSpine.kernelLeaves` (the leafwise garden kernel with individual profiles
`H` at the input leaves) by designated *stub* nodes `fix : GBranch → Option ℝ`: a node with `fix b = some v`
has the prescribed time `v` and is not integrated, and `kDomainFix` keeps the order constraint between a
parent and a child iff at least one of the two is free.  With `fix ≡ none` on a plain garden it is
`kernelLeaves` (`kernelLeavesFix_noStubs`); likewise `LeafFamily.valueFix`, `valueSelFix` reduce to
`LeafFamily.value`, `valueSel`.

Anchors are trivial trees with prescribed root labels (the entries of `nroot`), paired with a stub child
leaf; their profile is `1` (`AnchorOne`).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset Set

namespace WaveTurbulence.FlowerP1

open WaveTurbulence LGSpine

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

/-- The designated times of a stub set: every stub gets the time `s`. -/
def stubFix {w : ℕ} {tree : Fin w → TTree} (stubs : Finset (GBranch tree)) (s : ℝ) :
    GBranch tree → Option ℝ := fun b => open Classical in if b ∈ stubs then some s else none

variable {w d : ℕ}

/-- The summand (without the prefactor `coupling ^ order * zeta`) of the stub kernel. -/
noncomputable def kernelLeavesFixTerm (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG up fix).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-- **The garden-side stub kernel** (generalizes `kernelLeaves`; R61 X4): the leafwise garden kernel with
the designated (stub) nodes `fix` held at their prescribed times.  The decoration sum runs over the
decorations with root labels `nroot` (anchors are trivial trees whose root labels are prescribed there). -/
noncomputable def kernelLeavesFix (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl, kernelLeavesFixTerm L γ δ LG H up fix k₀ κ

/-- The stub kernel with the decoration sum restricted to `sel`. -/
noncomputable def kernelLeavesFixSel (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      open Classical in if sel κ then kernelLeavesFixTerm L γ δ LG H up fix k₀ κ else 0

/-- The family value with stubs `stubs` at time `ts`: the signed sum of the stub kernels, root times `tt`. -/
noncomputable def _root_.WaveTurbulence.LGSpine.LeafFamily.valueFix {P : WTParams} {w : ℕ}
    (F : LeafFamily P w) (tt : Fin w → ℝ) (fix : ∀ LG : LayeredGarden w, GBranch LG.garden.tree → Option ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) : ℂ :=
  @Finset.sum (F.ι LG) ℂ _ (@Finset.univ _ (F.fin LG)) fun i =>
    ((F.sign LG i : ℝ) : ℂ) *
      kernelLeavesFix P.L P.γ P.δ LG (F.H LG i) (fun b => tt b.1.1) (fix LG) base roots 0

/-- The family value with stubs and the decoration sum restricted to `sel`. -/
noncomputable def _root_.WaveTurbulence.LGSpine.LeafFamily.valueSelFix {P : WTParams} {w : ℕ}
    (F : LeafFamily P w) (tt : Fin w → ℝ) (fix : ∀ LG : LayeredGarden w, GBranch LG.garden.tree → Option ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w)
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) : ℂ :=
  @Finset.sum (F.ι LG) ℂ _ (@Finset.univ _ (F.fin LG)) fun i =>
    ((F.sign LG i : ℝ) : ℂ) *
      kernelLeavesFixSel P.L P.γ P.δ LG (F.H LG i) (fun b => tt b.1.1) (fix LG) base roots 0 sel

/-- Anchored pairs carry the profile `1`: every input leaf paired with a root leaf of a tree in `J`
(the anchor trees) has profile `1`. -/
def AnchorOne (LG : LayeredGarden w) (J : Finset (Fin w)) (H : LeafProfiles w d) : Prop :=
  ∀ ℓ ∈ inputLeaves LG.garden, ((LG.garden.pair ℓ).1.2 = [] ∧ (LG.garden.pair ℓ).1.1 ∈ J) →
    H ℓ.1 = fun _ => 1

/-! ## Bridges: no stubs, plain garden -/

theorem kernelLeavesFixTerm_noStubs (L γ δ : ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    kernelLeavesFixTerm L γ δ LG H up (fun _ => none) k₀ κ = kernelLeavesTerm L γ δ LG H up s k₀ κ := by
  classical
  have hnf : ∀ b, ¬ LG.garden.IsFlowerParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsFlower, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  have hnl : ∀ b, ¬ LG.garden.IsLoneParent b := fun b ⟨ℓ, hℓ, _⟩ => by
    rw [Garden.IsLone, hP ℓ] at hℓ
    exact absurd hℓ (by simp)
  unfold kernelLeavesFixTerm kernelLeavesTerm
  congr 2
  unfold phaseIntegral
  have hfree : ∀ b : GBranch LG.garden.tree, ¬ LG.garden.IsFlowerParent b ↔ (none : Option ℝ) = none :=
    fun b => ⟨fun _ => rfl, fun _ => hnf b⟩
  have key := integral_subtype_congr (Pp := fun b => ¬ LG.garden.IsFlowerParent b)
    (Q := fun _ => (none : Option ℝ) = none) (fun b => hfree b)
    (fun σ => (kDomainFix LG up (fun _ => none)).indicator
      (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1))
        (LG.garden.extendFix (fun _ => none) σ))
  refine key.symm.trans ?_
  show _ = ∫ τ : LG.garden.FreeBranch → ℝ, _
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

/-- **Bridge** (R61 X4): with no stubs a plain garden has the stub kernel `kernelLeaves`. -/
theorem kernelLeavesFix_noStubs (L γ δ : ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeavesFix L γ δ LG H up (fun _ => none) k₀ nroot nfl = kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold kernelLeavesFix kernelLeaves
  congr 1
  exact tsum_congr fun κ => kernelLeavesFixTerm_noStubs L γ δ LG hP H up s k₀ κ

theorem kernelLeavesFixSel_noStubs (L γ δ : ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) :
    kernelLeavesFixSel L γ δ LG H up (fun _ => none) k₀ nroot nfl sel =
      kernelLeavesSel L γ δ LG H up s k₀ nroot nfl sel := by
  unfold kernelLeavesFixSel kernelLeavesSel
  congr 1
  exact tsum_congr fun κ => by
    simp only [kernelLeavesFixTerm_noStubs L γ δ LG hP H up s k₀ κ]

theorem LeafFamily.valueFix_noStubs {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) (hP : LG.garden.IsPlain) :
    F.valueFix tt (fun _ _ => none) base roots LG = F.value tt base roots LG := by
  unfold LeafFamily.valueFix LeafFamily.value
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kernelLeavesFix_noStubs P.L P.γ P.δ LG hP _ _ 0 base roots 0]

theorem LeafFamily.valueSelFix_noStubs {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) :
    F.valueSelFix tt (fun _ _ => none) base roots LG sel = F.valueSel tt base roots LG sel := by
  unfold LeafFamily.valueSelFix LeafFamily.valueSel
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kernelLeavesFixSel_noStubs P.L P.γ P.δ LG hP _ _ 0 base roots 0]

end WaveTurbulence.FlowerP1
