/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Ker
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp

/-! # RT-GATE (ii), both roots pinned: a type-1 couple with BOTH roots designated

D2c's `T1Data.summand_t1Trace` / `kernelProt_t1Trace` (ProtCut/T1Summand.lean, T1Ker.lean; copies recorded in
RT2-COPIED.md) when the partner root is ALSO designated: no `u`-integral. The time level is D2c's `protTime_t1` with both
roots at `σ`; the linked phase at `σ = u` is `1`:

    kernelProt LG H M σ s (both roots at σ) k = c² Σ'_{e ∈ T1E} Mc ε_e · Q₁ Q₂ Q₃ (clocks σ)   (**`rt2_kernelProt_t1`**)

(the decoration sum by D2c's `tsum_cut_assembly` on the unit interval with a constant integrand). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtRT

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

namespace T1B

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
variable (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden)
include h

theorem rt2_rootPins_rt (σ : ℝ) (t : Fin 2) :
    MkSlotsO.rootPins (fun _ => True) σ (h.rt t) = some ((fun _ : Fin 2 => σ) t) := by
  unfold MkSlotsO.rootPins; rw [if_pos ⟨rfl, trivial⟩]

theorem rt2_rootPins_A (σ : ℝ) : (fun x => MkSlotsO.rootPins (fun _ => True) σ (h.βA x)) = fun _ => none :=
  funext fun x => by unfold MkSlotsO.rootPins; rw [if_neg (fun he => h.βA_path_ne x he.1)]

theorem rt2_rootPins_B (σ : ℝ) : (fun x => MkSlotsO.rootPins (fun _ => True) σ (h.βB x)) = fun _ => none :=
  funext fun x => by unfold MkSlotsO.rootPins; rw [if_neg (fun he => h.βB_path_ne x he.1)]

theorem rt2_rootPins_C (σ : ℝ) : (fun x => MkSlotsO.rootPins (fun _ => True) σ (h.βC x)) = fun _ => none :=
  funext fun x => by unfold MkSlotsO.rootPins; rw [if_neg (fun he => h.βC_path_ne x he.1)]

variable {d : ℕ}

/-- **A type-1 couple with both roots at `σ`, one decoration.** -/
theorem rt2_summand_t1 (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L : ℝ) (k : Mom d) (γ δ : ℝ)
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ)
    (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ) (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hM : h.MultFactors M Mc M₁ M₂ M₃) (s σ : ℝ)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) :
    protSummand L γ δ LG H M (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) k κ =
      (Mc (t1Star c L k (h.decEquiv d κ).1 0) (t1Star c L k (h.decEquiv d κ).1 1) *
          (t1Eps c (h.decEquiv d κ).1 : ℂ)) *
        (protSummand L γ δ LG₁ (t1HA c H) M₁ (fun _ => σ) 0 (fun _ => none)
            (k + latticePoint L (h.decEquiv d κ).1.1.1) (h.decEquiv d κ).2.1 *
          (protSummand L γ δ LG₂ (t1HB H) M₂ (fun _ => σ) 0 (fun _ => none)
              (k + latticePoint L (h.decEquiv d κ).1.1.2.1) (h.decEquiv d κ).2.2.1 *
            protSummand L γ δ LG₃ (t1HC c H) M₃ (fun _ => σ) 0 (fun _ => none)
              (k + latticePoint L (h.decEquiv d κ).1.1.2.2) (h.decEquiv d κ).2.2.2)) := by
  have hT := h.protTime_t1 L γ δ (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) (fun _ => σ)
    (rt2_rootPins_rt h σ) (fun _ => le_rfl) hlA hlB hlC
    (fun x v hv => by rw [congrFun (rt2_rootPins_A h σ) x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun (rt2_rootPins_B h σ) x] at hv; simp at hv)
    (fun x v hv => by rw [congrFun (rt2_rootPins_C h σ) x] at hv; simp at hv)
    (cosetDecoration LG.garden L k κ.1)
  rw [rt2_rootPins_A h σ, rt2_rootPins_B h σ, rt2_rootPins_C h σ] at hT
  have hph := h.phase_t1 κ L k γ δ 0 σ σ
  simp only [t1Clock, ite_self] at hph
  have h1 : t1Ph (LG.garden.sig 0) L γ δ k (h.decEquiv d κ).1 σ σ = 1 := by
    unfold t1Ph; simp
  unfold protSummand
  rw [hM, h.bstar_rt κ L k 0, h.bstar_rt κ L k 1, h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k,
    h.epsDec_t1' κ, hT, h.prodH_t1 κ L k H]
  simp only [h.coset_A κ L k, h.coset_B κ L k, h.coset_C κ L k, hph, h1]
  push_cast
  ring

/-- **A type-1 couple with both roots at `σ`** on `kernelProt`. -/
theorem rt2_kernelProt_t1 (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ) (hM : h.MultFactors M Mc M₁ M₂ M₃) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hM₁ : ∀ K, ‖M₁ K‖ ≤ CM) (hM₂ : ∀ K, ‖M₂ K‖ ≤ CM) (hM₃ : ∀ K, ‖M₃ K‖ ≤ CM)
    (s σ : ℝ)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z)) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 *
        ∑' e : T1E d, Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          (kernelProt L γ δ LG₁ (t1HA c H) M₁ (fun _ => σ) 0 (fun _ => none)
              (k + latticePoint L e.1.1) (fun _ => 0) 0 *
            (kernelProt L γ δ LG₂ (t1HB H) M₂ (fun _ => σ) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
              kernelProt L γ δ LG₃ (t1HC c H) M₃ (fun _ => σ) 0 (fun _ => none)
                (k + latticePoint L e.1.2.2) (fun _ => 0) 0)) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hM₁ 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * CM)) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hM₁ _
    · exact hM₂ _
    · exact hM₃ _
  have hvol : volume (Ioo (0 : ℝ) 1) = 1 := by rw [Real.volume_Ioo]; simp
  have hint1 : ∀ x : ℂ, ∫ _ in Ioo (0 : ℝ) 1, x = x := fun x => by
    rw [setIntegral_const]; simp [Measure.real, hvol]
  set Φ := (h.decEquiv d).trans ((Equiv.punitProd _).symm : _ ≃ Unit × _)
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hΦ : ∀ q, h.decEquiv d (Φ.symm q) = q.2 := fun q => by
    simp only [Φ, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    rfl
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) k (Φ.symm q) =
      (Mc (t1Star c L k q.2.1 0) (t1Star c L k q.2.1 1) * (t1Eps c q.2.1 : ℂ)) *
        ∫ u in Ioo (0 : ℝ) 1, (fun (_ : T1E d) (_ : ℝ) => (1 : ℂ)) q.2.1 u *
          ((fun (_ : Unit) (_ : ℝ) => (1 : ℂ)) q.1 u *
            ((fun (e : T1E d) (i : GenDecoration LG₁.garden d (fun _ => 0) 0) (_ : ℝ) =>
                protSummand L γ δ LG₁ (t1HA c H) M₁ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.1) i)
                q.2.1 q.2.2.1 u *
              ((fun (e : T1E d) (r : GenDecoration LG₂.garden d (fun _ => 0) 0) (_ : ℝ) =>
                  protSummand L γ δ LG₂ (t1HB H) M₂ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
                  q.2.1 q.2.2.2.1 u *
                (fun (e : T1E d) (g : GenDecoration LG₃.garden d (fun _ => 0) 0) (_ : ℝ) =>
                  protSummand L γ δ LG₃ (t1HC c H) M₃ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
                  q.2.1 q.2.2.2.2 u))) := by
    intro q
    have := rt2_summand_t1 h (Φ.symm q) L k γ δ H M Mc M₁ M₂ M₃ hM s σ hlA hlB hlC
    rw [hΦ] at this
    rw [this]
    simp only [one_mul]
    rw [hint1]
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) k
    (card_lone_le_of_plain h.plain) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) k
      (Φ.symm q) := (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (Ioo (0 : ℝ) 1) (by rw [hvol]; exact ENNReal.one_ne_top)
    (fun e => Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ))
    (fun _ _ => (1 : ℂ)) (fun _ _ => by simp) (fun _ => stronglyMeasurable_const)
    (fun (_ : Unit) (_ : ℝ) => (1 : ℂ))
    (fun e i _ => protSummand L γ δ LG₁ (t1HA c H) M₁ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.1) i)
    (fun e r _ => protSummand L γ δ LG₂ (t1HB H) M₂ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g _ => protSummand L γ δ LG₃ (t1HC c H) M₃ (fun _ => σ) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (fun _ => 1)
    (fun e i => CM * leafMajorant L LG₁ (t1HA c H) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LG₂ (t1HB H) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LG₃ (t1HC c H) (k + latticePoint L e.1.2.2) g)
    (fun _ _ => by simp)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hM₁ _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hM₂ _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hM₃ _ _ _ _ g)
    (hasSum_fintype _).summable
    (fun e => (summable_leafMajorant L LG₁ (t1HA c H) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₁.1.1) (h.hH_A L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₂ (t1HB H) (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₂.1.1) (h.hH_B L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₃ (t1HC c H) (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₃.1.1) (h.hH_C L H hH _)).mul_left CM)
    (fun _ => stronglyMeasurable_const) (fun _ _ => stronglyMeasurable_const)
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => stronglyMeasurable_const)
    _ hS hsum]
  have h1 : (∑' _ : Unit, (1 : ℂ)) = 1 := by simp
  simp only [h1, one_mul, hint1, kernelProt_eq_tsum]
  set cc := (coupling d L γ δ : ℂ)
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [h.order_t1, h.zeta_t1', pow_add, pow_add, pow_add]
  ring

end T1B

end WaveTurbulence.Flower.ProtRT
