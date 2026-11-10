/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeGate
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Pin0814
public import WaveTurbulence.Foundations.Spine.PL234Draft.Gate61Helpers

/-!
# TARGET Prop 6.1 at its literal `Λ₁ = 30d` norm, leafwise (L1097–1111, L2065–2067) (PL23-30D)

* `LCABody30`: the body of `PL2330Pin.LeafwiseCoherentApproximationGate` (the 0814 pin, byte-copied; `rfl`);
* `couple_same30`, `tree_same30`: the case `q = q'` (the single-layer estimate itself);
* **`leafwiseCoherentApproximationGate30`**: `RegularAsymptoticsGate → LeafwiseRegularAsymptoticsGate →
  PL2330Pin.LeafwiseCoherentApproximationGate`, at `C₁ = max(1, C_f, K_J, K_M)` with `C_f = 6K_tr²C⁴L²`,
  `L² = (2d)^{60d}`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

/-- The body of `PL2330Pin.LeafwiseCoherentApproximationGate` (pin text, `rfl`). -/
def LCABody30 (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)
        (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n 0 (timeBoxGt q q')
        (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
        (leafSizeProduct LG B))


/-! ### The case `q = q'` -/

section Same

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C)

include O

theorem couple_same30 {q n : ℕ} (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl)
    (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q) Set.univ (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q (ts 0) (ts 1) k) ≤
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
    exact hE
  · refine (sepRep_couple (q : ℝ) H Q hsize (fun ts => ts 0) (fun ts => ts 1) (continuous_apply 0)
      (continuous_apply 1) (fun hdom => (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _
        (fun ts (_ : Unit) => (Q.JB q (ts 0) (ts 1) : ℂ))).symm.le.trans (hJ hdom)) hM).congr
      fun ts _ k => hA _ _ _

theorem tree_same30 {q n : ℕ} (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4) (X : RegChain)
    (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q X LG)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q) Set.univ (fun ts k =>
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
    exact hE
  · refine (sepRep_tree (q : ℝ) H X (LG.garden.sig 0) hsize (fun ts => ts 0) (fun ts => ts 1) (continuous_apply 0)
      (continuous_apply 1) (fun hdom => (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _
        (fun ts (_ : Unit) => (X.JBtree q (ts 0) (ts 1) : ℂ))).symm.le.trans (hJ hdom)) hM).congr
      fun ts _ k => hA _ _ _

end Same


/-- The constant of Prop 6.1 at `30d`, from the data fixed before `C₁` and the two B2.1 constants. -/
noncomputable def g6130 (P₀ : WTParams) (x y : ℝ) : ℝ :=
  max 1 (max (Cf30 P₀.η (max x y) (Lsq P₀)) (max (KJ (1 - P₀.η) (max x y)) (KM (30 * P₀.d) P₀.d (max x y))))

theorem le_Cf30 {θ C L2 : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (hL : 1 ≤ L2) : C ≤ Cf30 θ C L2 := by
  have hK := one_le_Ktr hθ
  have h1 : C ≤ C ^ 4 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 4 := pow_le_pow_right₀ hC (by norm_num)
  have h2 : (1 : ℝ) ≤ 6 * Ktr θ ^ 2 * L2 := by nlinarith [one_le_pow₀ (n := 2) hK]
  unfold Cf30
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ C by linarith) 4]

/-- **The body of Prop 6.1, leafwise**, at `C₁ = g61`. -/
theorem lcaBody30_of (P : WTParams) (C₁' C₂' : ℝ) (hS : Standing P (η61 P.d P.γ)) (hC₁' : 1 ≤ C₁')
    (hA : B21Body P) (hB : LRABody { P with C₁ := C₁', C₂ := C₂' }) :
    LCABody30 { P with C₁ := g6130 (preC₁ P) P.C₁ C₁' } := by
  set C := max P.C₁ C₁' with hCdef
  set G := g6130 (preC₁ P) P.C₁ C₁' with hG
  have hC : 1 ≤ C := le_trans hS.C₁_ge (le_max_left _ _)
  have hC0 : 0 ≤ C := by linarith
  have hd : 1 ≤ P.d := by have := hS.d_ge; omega
  have hL : 1 ≤ P.L := by linarith [hS.L_ge]
  have hη0 : 0 ≤ P.η := hS.η_pos.le
  have hηh : P.η ≤ 1 / 2 := hS.η_le.trans (min_le_left _ _)
  have hη1 : P.η ≤ 1 := by linarith
  have hη2 : P.η ≤ 1 - P.η := by linarith
  have hδ : 0 ≤ P.δ := hS.δ_pos.le
  have hΛ0 : 0 ≤ gainΛ P := Real.rpow_nonneg (by linarith) _
  have hΛ1 : gainΛ P ≤ 1 := by
    have hθ := theta_avg_le P hS.d_ge hS.γ_mem hS.η_pos (hS.η_le.trans (min_le_right _ _)) 0
    apply Real.rpow_le_one_of_one_le_of_nonpos hL
    rw [Nat.cast_one, mul_one]
    linarith [theta_nonneg P 0, theta_nonneg P 1]
  have hG1 : 1 ≤ G := le_max_left _ _
  have hGf : Cf30 P.η C (Lsq P) ≤ G := (le_max_left _ _).trans (le_max_right _ _)
  have hGJ : KJ (1 - P.η) C ≤ G := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hGM : KM (30 * P.d) P.d C ≤ G := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : C ≤ G := (le_Cf30 hη0 hC (one_le_Lsq P hd)).trans hGf
  have herr : ∀ (n : ℕ) (β : ℝ), 0 ≤ β → ∀ a : ℝ, 0 ≤ a → a ≤ G →
      ENNReal.ofReal (a * (a * P.δ) ^ n * gainΛ P * β) ≤
        regBound { P with C₁ := G } n 1 * ENNReal.ofReal β := by
    intro n β hβ a ha haG
    have hreg : regBound { P with C₁ := G } n 1 = ENNReal.ofReal (G * (G * P.δ) ^ n * gainΛ P) := rfl
    rw [hreg, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h2 : (a * P.δ) ^ n ≤ (G * P.δ) ^ n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right haG hδ) n
    have h3 : a * (a * P.δ) ^ n ≤ G * (G * P.δ) ^ n := mul_le_mul haG h2 (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hΛ0) hβ
  have hpow : ∀ (n : ℕ) (a : ℝ), 0 ≤ a → a ≤ G → a ^ (n + 1) ≤ G * G ^ n := fun n a ha haG => by
    rw [← pow_succ']
    exact pow_le_pow_left₀ ha haG _
  have hCn : ∀ n : ℕ, C * C ^ n ≤ G * G ^ n := fun n => by
    rw [← pow_succ', ← pow_succ']
    exact pow_le_pow_left₀ hC0 hCG _
  unfold LCABody30
  intro p hp n hn₀
  have hn : n ≤ P.N (p + 1) ^ 4 := by
    rwa [N_eq_of P { P with C₁ := G } rfl rfl rfl] at hn₀
  have O := oracle_of_bodies P hS.C₁_ge hC₁' hδ (by linarith) hA hB hp
  refine ⟨fun Q LG q q' hqq hqp hsize hcoh H Bd hH => ?_, fun X LG q q' hqq hqp hsize hcoh H Bd hH => ?_⟩
  · have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    refine ⟨?_, fun hdom ts _ k => coherentCouple_eq_zero P.δ hqq hqp hcoh hdom H _ _ _, ?_⟩
    · rcases eq_or_lt_of_le hqq with heq | hlt
      · subst heq
        exact (couple_same30 P O hqp hn Q hsize LG hcoh H Bd hH).1.trans (herr n _ hβ0 C hC0 hCG)
      · rw [XNormRestr_eq_rN]
        exact (couple_err_gt30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hlt hqp hn Q hsize LG hcoh H Bd hH).trans
          (herr n _ hβ0 _ (by linarith [le_Cf30 hη0 hC (one_le_Lsq P hd)]) hGf)
    · rcases eq_or_lt_of_le hqq with heq | hlt
      · subst heq
        exact leafwiseSeparated_of_sepRep { P with C₁ := G }
          (couple_same30 P O hqp hn Q hsize LG hcoh H Bd hH).2 (hCn n)
          (mul_le_mul_of_nonneg_right (hCn n) hβ0)
      · exact leafwiseSeparated_of_sepRep { P with C₁ := G }
          (couple_sep_gt P O hC hd hL hη0 hη1 hlt hqp hn Q hsize LG hcoh H Bd hH)
          (hpow n _ (zero_le_one.trans (one_le_KJ (by linarith) hC)) hGJ)
          (mul_le_mul_of_nonneg_right (hpow n _ (zero_le_one.trans (one_le_KM _ hd hC)) hGM) hβ0)
  · have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    refine ⟨?_, fun hdom ts _ k => coherentTree_eq_zero P.δ hqq hcoh hdom H _ _ _, ?_⟩
    · rcases eq_or_lt_of_le hqq with heq | hlt
      · subst heq
        exact (tree_same30 P O hqp hn X hsize LG hcoh H Bd hH).1.trans (herr n _ hβ0 C hC0 hCG)
      · rw [XNormRestr_eq_rN]
        exact (tree_err_gt30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hlt hqp hn X hsize LG hcoh H Bd hH).trans
          (herr n _ hβ0 _ (by linarith [le_Cf30 hη0 hC (one_le_Lsq P hd)]) hGf)
    · rcases eq_or_lt_of_le hqq with heq | hlt
      · subst heq
        exact leafwiseSeparated_of_sepRep { P with C₁ := G }
          (tree_same30 P O hqp hn X hsize LG hcoh H Bd hH).2 (hCn n)
          (mul_le_mul_of_nonneg_right (hCn n) hβ0)
      · exact leafwiseSeparated_of_sepRep { P with C₁ := G }
          (tree_sep_gt P O hC hd hL hη0 hη1 hlt hqp hn X hsize LG hcoh H Bd hH)
          (hpow n _ (zero_le_one.trans (one_le_KJ (by linarith) hC)) hGJ)
          (mul_le_mul_of_nonneg_right (hpow n _ (zero_le_one.trans (one_le_KM _ hd hC)) hGM) hβ0)

/-- **TARGET Prop 6.1, leafwise, at `Λ₁ = 30d`** (L1097–1111 at the leaf inputs of L2065–2067) from B2.1. -/
theorem leafwiseCoherentApproximationGate30 (hA : RegularAsymptoticsGate)
    (hB : LeafwiseRegularAsymptoticsGate) : PL2330Pin.LeafwiseCoherentApproximationGate :=
  wtPrefix_transfer₂' g6130 (fun _ _ _ _ _ => le_max_left _ _) η61 η61_pos hA hB
    fun P C₁' C₂' hS hC₁' _ hAP hBP => lcaBody30_of P C₁' C₂' hS hC₁' hAP hBP

end WaveTurbulence.PL2330
