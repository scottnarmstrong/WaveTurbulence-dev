/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final1
import Mathlib.Tactic
/-! The box sum is at most `#classes · 2^{3n} ·` (uniform class bound). -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

/-- The possible signatures of presentation families. -/
noncomputable def Sigs (G : Garden w) : Finset (∀ _S : LQ G, GBranch G.tree × GBranch G.tree) :=
  Fintype.piFinset (fun S : LQ G => S.1 ×ˢ S.1)

theorem PF.sig_mem (π : PF G) : π.sig ∈ Sigs G := by
  unfold Sigs
  rw [Fintype.mem_piFinset]
  intro S
  have h0 : rowN (π.u S) 0 ∈ S.1 := by
    have := atomAt_mem π S true (i := 0) (Nat.zero_le _)
    simpa [atomAt] using this
  have h1 : rowN (π.u S) 1 ∈ S.1 := by
    have := atomAt_mem π S true (i := 1) (by have := (π.ladder S).1; omega)
    simpa [atomAt] using this
  exact Finset.mem_product.mpr ⟨h0, h1⟩

theorem box_sum_bound (_hp : G.IsPlain) {L : ℝ} (_hL : 0 < L) (D : SplicedKernelData G d)
    (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (Bcl : ℝ≥0∞)
    (hB : ∀ (π0 : PF G) (A : Finset (GBranch G.tree)),
      ∫⁻ α in Wnb (clsPF G D scales L γ η δ base roots π0),
        ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ ≤ Bcl) :
    splicedFourierBoxSum G D.layer D.rootTime (splicedFrequencySpectrum G D scales L γ η δ base roots) ≤
      ((Sigs G).card : ℝ≥0∞) * (2 ^ Fintype.card (GBranch G.tree) *
        (2 ^ Fintype.card (GBranch G.tree) * (2 ^ Fintype.card (GBranch G.tree) * Bcl))) := by
  set 𝒜 := splicedFrequencySpectrum G D scales L γ η δ base roots with h𝒜
  by_cases hne : 𝒜 = ∅
  · have : sourceFrequencyBoxes G 𝒜 = ∅ := by
      ext σ; simp [sourceFrequencyBoxes, hne]
    unfold splicedFourierBoxSum
    rw [this]
    simp
  have hne' : ∃ α, α ∈ 𝒜 := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨α0, hα0⟩ := hne'
  have : Nonempty (PF G) := by
    obtain ⟨π, _⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D scales L γ η δ base roots hα0)
    exact ⟨π⟩
  let repf : (∀ S : LQ G, GBranch G.tree × GBranch G.tree) → PF G :=
    fun c => Classical.epsilon (fun π : PF G => π.sig = c)
  have hrep : ∀ π : PF G, (repf π.sig).sig = π.sig := fun π => by
    show (Classical.epsilon (fun π' : PF G => π'.sig = π.sig)).sig = π.sig
    exact Classical.epsilon_spec (p := fun π' : PF G => π'.sig = π.sig) ⟨π, rfl⟩
  have hcover : ∀ α ∈ 𝒜, ∃ c ∈ Sigs G,
      α ∈ clsPF G D scales L γ η δ base roots (repf c) := by
    intro α hα
    obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D scales L γ η δ base roots hα)
    exact ⟨π.sig, π.sig_mem, clsPF_transport G D scales L γ η δ base roots π (repf π.sig)
      (hrep π).symm hπ⟩
  have hΩm : MeasurableSet (splicedTimeDomain G D.layer D.rootTime) := by
    rw [splicedTimeDomain_eq_Om0]; exact measurableSet_Om0 (fun a b : GBranch G.tree => a.IsChildOf b) (fun v => (D.layer v : ℝ)) (fun v => D.rootTime v.1.1)
  have hΩb : ∀ t ∈ splicedTimeDomain G D.layer D.rootTime, ∀ v, |t v| ≤ ∑ v, (|(D.layer v : ℝ)| + 1) := by
    rw [splicedTimeDomain_eq_Om0]; exact bdd_Om0 (fun a b : GBranch G.tree => a.IsChildOf b) (fun v => (D.layer v : ℝ)) (fun v => D.rootTime v.1.1)
  unfold splicedFourierBoxSum
  calc ∑' σ : sourceFrequencyBoxes G 𝒜, ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ 𝒜)
        (_ : ∀ v, |α v - σ.1 v| ≤ 1), ‖splicedFourierB G D.layer D.rootTime α‖ₑ
      ≤ ∑' σ : sourceFrequencyBoxes G 𝒜, ∑ c ∈ Sigs G, ⨆ (α : GBranch G.tree → ℝ)
          (_ : α ∈ clsPF G D scales L γ η δ base roots (repf c)) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
          ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) ∅ α‖ₑ := by
        refine ENNReal.tsum_le_tsum (fun σ => ?_)
        refine iSup_le (fun α => iSup_le (fun hα => iSup_le (fun hσ => ?_)))
        obtain ⟨c, hc, hαc⟩ := hcover α hα
        rw [splicedFourierB_eq_Phi]
        refine le_trans ?_ (Finset.single_le_sum (f := fun c => ⨆ (α : GBranch G.tree → ℝ)
          (_ : α ∈ clsPF G D scales L γ η δ base roots (repf c)) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
          ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) ∅ α‖ₑ) (fun _ _ => bot_le) hc)
        exact le_iSup₂_of_le α hαc (le_iSup_of_le hσ le_rfl)
    _ = ∑ c ∈ Sigs G, ∑' σ : sourceFrequencyBoxes G 𝒜, ⨆ (α : GBranch G.tree → ℝ)
          (_ : α ∈ clsPF G D scales L γ η δ base roots (repf c)) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
          ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) ∅ α‖ₑ := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ _c ∈ Sigs G, (2 ^ Fintype.card (GBranch G.tree) *
          (2 ^ Fintype.card (GBranch G.tree) * (2 ^ Fintype.card (GBranch G.tree) * Bcl))) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        refine (sum_sup_le _ hΩm _ hΩb _ _ _).trans ?_
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        calc ∑ A : Finset (GBranch G.tree), ∫⁻ α in Wnb (clsPF G D scales L γ η δ base roots (repf c)),
              ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ
            ≤ ∑ _A : Finset (GBranch G.tree), Bcl := Finset.sum_le_sum (fun A _ => hB _ A)
          _ = 2 ^ Fintype.card (GBranch G.tree) * Bcl := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]; push_cast; ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end WaveTurbulence.Ladder
