/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGate1
public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.Spine.LeafwiseAppContinuity
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelContinuity
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import WaveTurbulence.Foundations.Spine.TimeBoxGeometry
import Mathlib.Tactic

/-!
# S2 REPRESENTS: couple slots from the leafwise gates

Incoherent couples (`LeafwiseIncoherentDecayAt`): `CenSup` of the couple kernel on the time box with mass
`C * regBound P n g * cost`.  Coherent couples (`LeafwiseCoherentApproximationAt`, `q' ≤ q`): the kernel is the
sum of the coherent error and the coherent app, so its `XNormRestr` is at most the error bound plus the
separation bound of the app.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic Set
open scoped ENNReal

theorem regBound_ne_top (P : WTParams) (n g : ℕ) : regBound P n g ≠ ⊤ := by
  unfold regBound; exact ENNReal.ofReal_ne_top

theorem couple_slot_incoh (P : WTParams) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (hginc : LeafwiseIncoherentDecayAt P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = cenCplC P.d P.η ∧ ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 →
      ∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2), Q.Decodes LG.garden →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      CenSup (30 * P.d) (timeBox (q : ℝ) q')
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
        (C * (regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B))) := by
  obtain ⟨C, hC, hCe, h⟩ := cenSup_couple P hd1 hη0
  refine ⟨C, hC, hCe, fun p n hp hn Q hwf hsz LG hdec hlay q q' hq hq' hr0 hr1 hi H B hctrl => ?_⟩
  refine h q q' _ _ (ENNReal.mul_ne_top (regBound_ne_top _ _ _) ENNReal.ofReal_ne_top) ?_ ?_
  · intro k
    have hK := continuous_coupleLeaves_time P.L P.γ P.δ H LG hdec.1.1 k (hctrl.summable_coset hd1 hL1 k)
    exact hK
  · exact (hginc p hp n hn).1 Q hwf hsz LG hdec hlay q q' hq hq' hr0 hr1 hi H B hctrl

theorem xnorm_add_split {r d : ℕ} {θ : ℝ} {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) {B : Set (Fin r → ℝ)}
    (f app : (Fin r → ℝ) → Mom d → ℂ) {X Y : ℝ≥0∞}
    (he : XNormRestr θ Λ₁ Λ₂ B Set.univ (fun ts k => f ts k - app ts k) ≤ X)
    (ha : XNormRestr θ Λ₁ Λ₂ B Set.univ app ≤ Y) :
    XNormRestr θ Λ₁ Λ₂ B Set.univ f ≤ X + Y := by
  have hc : XNormRestr θ Λ₁ Λ₂ B Set.univ f =
      XNormRestr θ Λ₁ Λ₂ B Set.univ (fun ts k => (f ts k - app ts k) + app ts k) := by
    simp only [sub_add_cancel]
  refine hc.le.trans ?_
  refine (PL2330.XNormRestr_eq_rN θ Λ₁ Λ₂ B _).le.trans
    ((PL2330.restr_add_le (θ := θ) (Λ := Λ₁) (Λ₂ := Λ₂) hΛ B Set.univ (fun ts k => f ts k - app ts k) app).trans
      (add_le_add ?_ ?_))
  · exact (PL2330.XNormRestr_eq_rN θ Λ₁ Λ₂ B (fun ts k => f ts k - app ts k)).symm.le.trans he
  · exact (PL2330.XNormRestr_eq_rN θ Λ₁ Λ₂ B app).symm.le.trans ha

theorem couple_slot_coh_of (P : WTParams) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 2)
    (hC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = cenCplC P.d P.η ∧ ∀ (n q q' : ℕ) (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (LG : LayeredGarden 2)
      (H : LeafProfiles 2 P.d)
      (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B → LG.garden.IsPlain →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          f ts k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B) →
      LeafwiseSeparated P n (30 * P.d) (timeBox (q : ℝ) q') f (leafSizeProduct LG B) →
      CenSup (30 * P.d) (timeBox (q : ℝ) q')
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k)
        (C * (regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B) +
          sepMass P n (leafSizeProduct LG B))) := by
  obtain ⟨C, hC0, hCe, h⟩ := cenSup_couple P hd1 hη0
  refine ⟨C, hC0, hCe, fun n q q' f LG H B hctrl hplain hXe hsep => ?_⟩
  have hcost : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hKc : ∀ k, Continuous fun ts : Fin 2 → ℝ => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k :=
    fun k => continuous_coupleLeaves_time P.L P.γ P.δ H LG hplain k (hctrl.summable_coset hd1 hL1 k)
  have hA : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ
      f ≤
      sepMass P n (leafSizeProduct LG B) := by
    rw [PL2330.XNormRestr_eq_rN]
    exact rN_leafwiseSeparated_le hsep hd1 (by linarith) hC hδ hcost
  exact h q q' _ _ (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (regBound_ne_top _ _ _) ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩) hKc (xnorm_add_split (by omega) _ _ hXe hA)

end WaveTurbulence.Represents
