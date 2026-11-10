/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp
public import WaveTurbulence.Foundations.Flower.MkMark.Batch
public import WaveTurbulence.Foundations.Flower.MkMarkX.Defs

/-! # B4 STAGE1MK-GATE: the markings

* `markI0_sub_markI`: `Π₀ ⊆ Π`, so the coarse marking lies below the fine one.
* **Stem-free case** (`¬ StemDep σ kSel`, i.e. `kSel ≡ none` and `σ ≡ none`): no selected seed exists
  (`selSetCap … = ∅`), so `Π = Π₀` and `markI = markI0`, which B2b transports along every batch at unmarked members
  with no clean condition (`markInvariantBatchV_markI0`). Hence `markI` is a `FineMarking` (`fineMarking_stemFree`):
  the stem condition of `markI`'s transport comes only from selected seeds.
* Conversions between the world's `MkMark.MarkInvariantBatchV` and main's `Stage1Mk.MarkInvariantBatchV` (same body). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

/-- `markedVinesRaw` is monotone in the protected set. -/
theorem markedVinesRaw_mono {S : Garden w} (X : GBranch S.tree → RegChain) {T : Fin w → TTree}
    {Pi Pi' : Finset (GNode T)} (h : Pi ⊆ Pi') : markedVinesRaw S X Pi ⊆ markedVinesRaw S X Pi' :=
  fun _ ⟨hv, b, hb, hbu, a, ha, hn⟩ => ⟨hv, b, hb, hbu, a, h ha, hn⟩

theorem protI0_sub_protI (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) : protI0 LG J pat t s ⊆ protI LG J pat t s kSel := by
  intro a ha
  simp only [protI0, protI, protectedSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  obtain ⟨x, hx, h⟩ := ha
  refine ⟨x, hx, h.imp id fun ⟨b, hb, hfs⟩ => ⟨b, hb, hfs.imp id fun hs => ?_⟩⟩
  exact absurd hs (Finset.notMem_empty b)

/-- `Π₀ ⊆ Π`: the coarse marking lies below the fine one. -/
theorem markI0_sub_markI (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    {LG : LayeredGarden w} (B : PrimeData LG) : markI0 J pat t s B ⊆ markI J pat t s kSel B :=
  markedVinesRaw_mono _ (protI0_sub_protI LG J pat t s kSel)

/-- Without a depth selection there is no selected seed. -/
theorem selSetCap_none (LG : LayeredGarden w) (J : Finset (Fin w)) {kSel : Fin w → Option ℕ}
    (hk : ∀ j, kSel j = none) : selSetCap LG J kSel = ∅ := by
  ext b
  simp [selSetCap, selCap, hk]

theorem protI_eq_protI0 (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    {kSel : Fin w → Option ℕ} (hk : ∀ j, kSel j = none) : protI LG J pat t s kSel = protI0 LG J pat t s := by
  simp only [protI, protI0, selSetCap_none LG J hk]

/-- **Without a depth selection the fine marking is the coarse one.** -/
theorem markI_eq_markI0 (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ}
    (hk : ∀ j, kSel j = none) : @markI w J pat t s kSel = @markI0 w J pat t s := by
  funext LG B
  simp only [markI, markI0, protI_eq_protI0 LG J pat t s hk]

theorem not_stemDep_iff {σ kSel : Fin w → Option ℕ} :
    ¬ StemDep σ kSel ↔ (∀ i, σ i = none) ∧ ∀ i, kSel i = none := by
  simp [StemDep, not_or]

/-- **Stem-free case: `markI` is a fine marking.** -/
theorem fineMarking_stemFree (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (hns : ¬ StemDep σ kSel) : FineMarking J pat t s kSel σ (markI J pat t s kSel) := by
  have hk := (not_stemDep_iff.mp hns).2
  refine ⟨fun _ => subset_rfl, fun h => (hns h).elim, fun _ c hc => Or.inl hc, fun a => ?_⟩
  rw [markI_eq_markI0 J pat t s hk]
  have h0 : Stage1Mk.MarkInvariantBatchV (@markI0 w J pat t s) (fun _ => True) :=
    fun hb hA hm hc => MkMark.markInvariantBatchV_markI0 J pat t s hb hA hm hc
  exact @fineTransportedAt_of_markInvariantBatchV w (@markI0 w J pat t s) (fun _ => True) h0 a trivial

end WaveTurbulence.Flower.Stage1MKGate
