/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SepTree
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoherentTaylor

/-!
# TARGET Prop 6.1, leafwise (L1097–1111, L2065–2067): `LeafwiseCoherentApproximationGate`

* `oracle_of_bodies`: the single-layer estimates (`Oracle`) at the constant `max C₁ᴬ C₁ᴮ`, from the B2.1
  body (`B21Body`, the time factors) and the leafwise B2.1 body (`LRABody`, errors and momentum factors);
* `couple_same`, `tree_same`: the case `q = q'` (all layers `q`);
* **`leafwiseCoherentApproximationGate`**: `RegularAsymptoticsGate → LeafwiseRegularAsymptoticsGate →
  LeafwiseCoherentApproximationGate`, with `C₁ = max(1, C_f, K_J, K_M)` at `C = max C₁ᴬ C₁ᴮ`, for
  `η ≤ min(1/2, ηTaylor d γ)` (so `η ≤ 1 - η` and `√η ≤ γ₁`, i.e. `L^{-(γ₁-√η)} ≤ 1`).
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-! ### The single-layer estimates from the B2.1 bodies -/

theorem oracle_of_bodies (P : WTParams) {C₁' C₂' : ℝ} (hC₁ : 1 ≤ P.C₁) (hC₁' : 1 ≤ C₁') (hδ : 0 ≤ P.δ)
    (hL : 0 < P.L) (hA : B21Body P) (hB : LRABody { P with C₁ := C₁', C₂ := C₂' }) {p : ℕ}
    (hp : p < P.D) : Oracle P p (max P.C₁ C₁') := by
  have hΛ0 : 0 ≤ gainΛ P := Real.rpow_nonneg hL.le _
  have hC0 : 0 ≤ max P.C₁ C₁' := le_trans (by linarith) (le_max_left _ _)
  have hC₁'0 : 0 ≤ C₁' := by linarith
  have h0 : ∀ r, InputRemainder P (fun _ => 0) r := fun r => by
    unfold InputRemainder
    rw [SNormR_zero]
    exact zero_le
  have hreg : ∀ n, regBound { P with C₁ := C₁', C₂ := C₂' } n 1 =
      ENNReal.ofReal (C₁' * (C₁' * P.δ) ^ n * gainΛ P) := fun n => rfl
  have monoE : ∀ (n : ℕ) (β : ℝ), 0 ≤ β → regBound { P with C₁ := C₁', C₂ := C₂' } n 1 * ENNReal.ofReal β ≤
      ENNReal.ofReal (max P.C₁ C₁' * (max P.C₁ C₁' * P.δ) ^ n * gainΛ P * β) := by
    intro n β hβ
    rw [hreg, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : C₁' ≤ max P.C₁ C₁' := le_max_right _ _
    have h2 : (C₁' * P.δ) ^ n ≤ (max P.C₁ C₁' * P.δ) ^ n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 hδ) n
    have h3 : C₁' * (C₁' * P.δ) ^ n ≤ max P.C₁ C₁' * (max P.C₁ C₁' * P.δ) ^ n :=
      mul_le_mul h1 h2 (by positivity) hC0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hΛ0) hβ
  have monoJ : ∀ (n : ℕ) {a : ℝ}, 0 ≤ a → a ≤ max P.C₁ C₁' → a * a ^ n ≤ max P.C₁ C₁' * max P.C₁ C₁' ^ n :=
    fun n a ha hle => mul_le_mul hle (pow_le_pow_left₀ ha hle n) (by positivity) hC0
  have hNB : ∀ {n : ℕ}, n ≤ P.N (p + 1) ^ 4 → n ≤ ({ P with C₁ := C₁', C₂ := C₂' } : WTParams).N (p + 1) ^ 4 :=
    fun hn => by rwa [N_eq_of P { P with C₁ := C₁', C₂ := C₂' } rfl rfl rfl]
  refine ⟨fun r q'' n hr hq hn X hwf hsize LG hX hlay H B hH => ?_,
    fun r n hr hn Q hwf hsize LG hQ hlay H B hH => ?_⟩
  · have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hE, hM⟩ := (hB p hp r hr n (hNB hn)).2 X hwf hsize LG hX q'' hq hlay H B hH
    have hA' := hA p hp r hr (fun _ => 0) (h0 r) n hn
    dsimp only at hA'
    obtain ⟨-, -, -, hA4, -⟩ := hA'
    refine ⟨hE.trans (monoE n _ hβ0), fun hdom => (hA4 X hwf hdom hsize (LG.garden.sig 0) q'' hq).1.trans
      (ENNReal.ofReal_le_ofReal (monoJ n (by linarith) (le_max_left _ _))),
      fun hdom Z hZ => (hM hdom Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right (monoJ n hC₁'0 (le_max_right _ _)) hβ0
  · have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hE, hM⟩ := (hB p hp r hr n (hNB hn)).1 Q hwf hsize LG hQ hlay H B hH
    have hA' := hA p hp r hr (fun _ => 0) (h0 r) n hn
    dsimp only at hA'
    obtain ⟨-, -, hA3, -, -⟩ := hA'
    refine ⟨hE.trans (monoE n _ hβ0), fun hdom => (hA3 Q hwf hdom hsize).1.trans
      (ENNReal.ofReal_le_ofReal (monoJ n (by linarith) (le_max_left _ _))),
      fun hdom Z hZ => (hM hdom Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right (monoJ n hC₁'0 (le_max_right _ _)) hβ0

/-! ### The case `q = q'` -/

section Same

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C)

include O

theorem couple_same {q n : ℕ} (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl)
    (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBox q q) Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q (ts 0) (ts 1) k)) ≤
      ENNReal.ofReal (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) ∧
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n (timeBox q q)
      (fun ts k => LeafApp.coherentCouple P.δ LG H Q q q (ts 0) (ts 1) k) (C * C ^ n)
      (C * C ^ n * leafSizeProduct LG Bd) := by
  have hlay := coherentCouple_layer_eq hcoh
  obtain ⟨hE, hJ, hM⟩ := O.couple q n hqp hnN Q hcoh.1 hsize LG hcoh.2.1 hlay H Bd hH
  have hA : ∀ t s k, LeafApp.coherentCouple P.δ LG H Q q q t s k = LeafApp.couple P.δ q H Q t s k :=
    fun t s k => by simp [LeafApp.coherentCouple]
  constructor
  · simp only [hA]
    refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η (timeBox (q : ℝ) q) Set.univ
      (fun ts k => wt k * (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.couple P.δ q H Q (ts 0) (ts 1) k))).symm.le.trans ?_
    exact (XNorm00Restr_weight_le_XNormRestr P.η (30 * P.d) (30 * P.d) _ _ _).trans hE
  · refine (sepRep_couple (q : ℝ) H Q hsize (fun ts => ts 0) (fun ts => ts 1) (continuous_apply 0)
      (continuous_apply 1) (fun hdom => (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _
        (fun ts (_ : Unit) => (Q.JB q (ts 0) (ts 1) : ℂ))).symm.le.trans (hJ hdom)) hM).congr
      fun ts _ k => hA _ _ _

theorem tree_same {q n : ℕ} (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4) (X : RegChain)
    (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q X LG)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBoxGt q q) Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) ∧
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n (timeBoxGt q q)
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q (ts 0) (ts 1) k) (C * C ^ n)
      (C * C ^ n * leafSizeProduct LG Bd) := by
  have hlay := coherentTree_layer_eq hcoh
  have hlay' : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q else q := fun a => by
    rw [hlay a]
    split_ifs <;> rfl
  obtain ⟨hE, hJ, hM⟩ := O.tree q q n hqp le_rfl hnN X hcoh.1 hsize LG hcoh.2.1 hlay' H Bd hH
  have hA : ∀ t s k, LeafApp.coherentTree P.δ LG H X q q t s k =
      LeafApp.tree P.δ q H X (LG.garden.sig 0) t s k := fun t s k => by simp [LeafApp.coherentTree]
  constructor
  · simp only [hA]
    refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η (timeBoxGt (q : ℝ) q) Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ q H X (LG.garden.sig 0) (ts 0) (ts 1) k)).symm.le.trans ?_
    exact (XNorm00Restr_le_XNormRestr _ _ _ _ _ _).trans hE
  · refine (sepRep_tree (q : ℝ) H X (LG.garden.sig 0) hsize (fun ts => ts 0) (fun ts => ts 1) (continuous_apply 0)
      (continuous_apply 1) (fun hdom => (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _
        (fun ts (_ : Unit) => (X.JBtree q (ts 0) (ts 1) : ℂ))).symm.le.trans (hJ hdom)) hM).congr
      fun ts _ k => hA _ _ _

end Same

/-! ### Constants and the gate -/

/-- The constant of Prop 6.1, from the data fixed before `C₁` and the two B2.1 constants. -/
noncomputable def g61 (P₀ : WTParams) (x y : ℝ) : ℝ :=
  max 1 (max (Cf P₀.η (max x y)) (max (KJ (1 - P₀.η) (max x y)) (KM (30 * P₀.d) P₀.d (max x y))))

/-- The threshold on `η`. -/
noncomputable def η61 (d : ℕ) (γ : ℝ) : ℝ := min (1 / 2) (ηTaylor d γ)

theorem η61_pos (d : ℕ) (γ : ℝ) : 0 < η61 d γ := lt_min (by norm_num) (ηTaylor_pos d γ)

theorem le_Cf {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) : C ≤ Cf θ C := by
  have hK := one_le_Ktr hθ
  have h1 : C ≤ C ^ 4 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 4 := pow_le_pow_right₀ hC (by norm_num)
  have h2 : (1 : ℝ) ≤ 6 * Ktr θ ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hK]
  unfold Cf
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ C by linarith) 4]


end WaveTurbulence.PL234
