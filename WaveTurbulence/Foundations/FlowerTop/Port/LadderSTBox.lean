/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTClass2
/-! # FLOWER-P5: the free-clock box sum is bounded by the class bounds (copy-and-thread of `box_sum_bound`, `Final2`) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

theorem measurableSet_Om0_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (ch : ι → ι → Prop) (ls cap : ι → ℝ) :
    MeasurableSet (Om0 ch ls cap) := by
  have e : Om0 ch ls cap = OmegaC ls cap ch (fun _ _ => False) (k := 0) (fun i => (Fin.elim0 i)) Set.univ := by
    ext t; simp [Om0, OmegaC]
  rw [e]
  exact measurableSet_OmegaC ls cap _ _ _ _ MeasurableSet.univ

theorem bdd_Om0_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (ch : ι → ι → Prop) (ls cap : ι → ℝ) :
    ∀ t ∈ Om0 ch ls cap, ∀ v, |t v| ≤ ∑ v, (|ls v| + 1) := by
  have e : Om0 ch ls cap = OmegaC ls cap ch (fun _ _ => False) (k := 0) (fun i => (Fin.elim0 i)) Set.univ := by
    ext t; simp [Om0, OmegaC]
  rw [e]
  exact bdd_OmegaC ls cap _ _ _ _

/-- The frequency spectrum is covered by the classes of representatives of the signatures. -/
theorem box_sum_boundST (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelDataST G d)
    (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (Bcl : ℝ≥0∞)
    (hB : ∀ (π0 : PF G) (A : Finset (FrB G D.fix)),
      ∫⁻ α in Wnb (clsPFfree D scales L γ η δ base roots π0),
        ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ ≤ Bcl) :
    splicedFourierBoxSumSTFree G D.layer D.rootTime D.fix
        (splicedFrequencySpectrum G D.toSplicedKernelData scales L γ η δ base roots) ≤
      ((Sigs G).card : ℝ≥0∞) * (2 ^ Fintype.card (FrB G D.fix) *
        (2 ^ Fintype.card (FrB G D.fix) * (2 ^ Fintype.card (FrB G D.fix) * Bcl))) := by
  set 𝒜 := splicedFrequencySpectrum G D.toSplicedKernelData scales L γ η δ base roots with h𝒜
  by_cases hne : 𝒜 = ∅
  · have : sourceFrequencyBoxesFree G D.fix 𝒜 = ∅ := by
      ext σ; simp [sourceFrequencyBoxesFree, hne]
    unfold splicedFourierBoxSumSTFree
    rw [this]
    simp
  have hne' : ∃ α, α ∈ 𝒜 := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨α0, hα0⟩ := hne'
  haveI : Nonempty (PF G) := by
    obtain ⟨π, _⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D.toSplicedKernelData scales L γ η δ base roots hα0)
    exact ⟨π⟩
  let repf : (∀ S : LQ G, GBranch G.tree × GBranch G.tree) → PF G :=
    fun c => Classical.epsilon (fun π : PF G => π.sig = c)
  have hrep : ∀ π : PF G, (repf π.sig).sig = π.sig := fun π => by
    show (Classical.epsilon (fun π' : PF G => π'.sig = π.sig)).sig = π.sig
    exact Classical.epsilon_spec (p := fun π' : PF G => π'.sig = π.sig) ⟨π, rfl⟩
  have hcover : ∀ α ∈ 𝒜, ∃ c ∈ Sigs G,
      α ∈ clsPF G D.toSplicedKernelData scales L γ η δ base roots (repf c) := by
    intro α hα
    obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D.toSplicedKernelData scales L γ η δ base roots hα)
    exact ⟨π.sig, π.sig_mem, clsPF_transport G D.toSplicedKernelData scales L γ η δ base roots π (repf π.sig)
      (hrep π).symm hπ⟩
  have hΩm := measurableSet_Om0_gen (chF D) (lsF D) (capF D)
  have hΩb := bdd_Om0_gen (chF D) (lsF D) (capF D)
  unfold splicedFourierBoxSumSTFree
  calc ∑' σ : sourceFrequencyBoxesFree G D.fix 𝒜, ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ 𝒜)
        (_ : ∀ v : FrB G D.fix, |α v.1 - σ.1 v| ≤ 1), ‖splicedFourierBST G D.layer D.rootTime D.fix α‖ₑ
      ≤ ∑' σ : sourceFrequencyBoxesFree G D.fix 𝒜, ∑ c ∈ Sigs G, ⨆ (αf : FrB G D.fix → ℝ)
          (_ : αf ∈ clsPFfree D scales L γ η δ base roots (repf c)) (_ : ∀ v, |αf v - σ.1 v| ≤ 1),
          ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) ∅ αf‖ₑ := by
        refine ENNReal.tsum_le_tsum (fun σ => ?_)
        refine iSup_le (fun α => iSup_le (fun hα => iSup_le (fun hσ => ?_)))
        obtain ⟨c, hc, hαc⟩ := hcover α hα
        rw [enorm_splicedFourierBST_eq]
        refine le_trans ?_ (Finset.single_le_sum (f := fun c => ⨆ (αf : FrB G D.fix → ℝ)
          (_ : αf ∈ clsPFfree D scales L γ η δ base roots (repf c)) (_ : ∀ v, |αf v - σ.1 v| ≤ 1),
          ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) ∅ αf‖ₑ) (fun _ _ => bot_le) hc)
        exact le_iSup₂_of_le (fun v => α v.1) ⟨α, hαc, fun v => rfl⟩ (le_iSup_of_le hσ le_rfl)
    _ = ∑ c ∈ Sigs G, ∑' σ : sourceFrequencyBoxesFree G D.fix 𝒜, ⨆ (αf : FrB G D.fix → ℝ)
          (_ : αf ∈ clsPFfree D scales L γ η δ base roots (repf c)) (_ : ∀ v, |αf v - σ.1 v| ≤ 1),
          ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) ∅ αf‖ₑ := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ _c ∈ Sigs G, (2 ^ Fintype.card (FrB G D.fix) *
          (2 ^ Fintype.card (FrB G D.fix) * (2 ^ Fintype.card (FrB G D.fix) * Bcl))) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        refine (sum_sup_le _ hΩm _ hΩb _ _ _).trans ?_
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        calc ∑ A : Finset (FrB G D.fix), ∫⁻ α in Wnb (clsPFfree D scales L γ η δ base roots (repf c)),
              ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ
            ≤ ∑ _A : Finset (FrB G D.fix), Bcl := Finset.sum_le_sum (fun A _ => hB _ A)
          _ = 2 ^ Fintype.card (FrB G D.fix) * Bcl := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]; push_cast; ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end WaveTurbulence.FlowerP5
