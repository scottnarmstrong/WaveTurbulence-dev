/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Gate30
public import WaveTurbulence.Foundations.Spine.PL234Draft.Gate61CHelpers

/-!
# TARGET Prop 6.1 at its literal `Λ₁ = 30d` norm (PL23-30D)

* `CABody30`: the body of `PL2330Pin.CoherentApproximationGate` (the 0814 pin, byte-copied; `rfl`);
* **`coherentApproximationGate30`**: `RegularAsymptoticsGate → LeafwiseRegularAsymptoticsGate →
  PL2330Pin.CoherentApproximationGate`, from the leafwise gate at the leaf inputs `H_F z = F(𝔏 z)`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

/-- The body of `PL2330Pin.CoherentApproximationGate` (pin text, `rfl`). -/
def CABody30 (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n 0 (timeBoxGt q q')
        (fun ts k => SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k))

/-- The constant of the common Prop 6.1 at `30d`. -/
noncomputable def gC30 (P₀ : WTParams) (x y : ℝ) : ℝ := g6130 P₀ x y * (βφ P₀ + 1) ^ 4

theorem one_le_gC30 (P₀ : WTParams) (x y : ℝ) : 1 ≤ gC30 P₀ x y := by
  unfold gC30
  have h1 : 1 ≤ g6130 P₀ x y := le_max_left _ _
  have h2 : (1 : ℝ) ≤ (βφ P₀ + 1) ^ 4 := one_le_pow₀ (by linarith [one_le_βφ P₀])
  nlinarith

/-- **The body of Prop 6.1**, at `C₁ = gC`. -/
theorem caBody30_of (P : WTParams) (C₁' C₂' : ℝ) (hS : Standing P (η61 P.d P.γ)) (hC₁' : 1 ≤ C₁')
    (hA : B21Body P) (hB : LRABody { P with C₁ := C₁', C₂ := C₂' }) :
    CABody30 { P with C₁ := gC30 (preC₁ P) P.C₁ C₁' } := by
  have hL61 := lcaBody30_of P C₁' C₂' hS hC₁' hA hB
  set G := g6130 (preC₁ P) P.C₁ C₁' with hG
  set b := βφ (preC₁ P) + 1 with hbdef
  have hb1 : 1 ≤ b := by linarith [one_le_βφ (preC₁ P)]
  have hG0 : 0 ≤ G := zero_le_one.trans (le_max_left _ _)
  have hδ : 0 ≤ P.δ := hS.δ_pos.le
  have hL : 0 < P.L := by linarith [hS.L_ge]
  have hgC : gC30 (preC₁ P) P.C₁ C₁' = G * b ^ 4 := rfl
  unfold LCABody30 at hL61
  unfold CABody30
  dsimp only
  intro p hp R hR n hn₀
  have hn : n ≤ P.N (p + 1) ^ 4 := by
    rwa [N_eq_of P { P with C₁ := gC30 (preC₁ P) P.C₁ C₁' } rfl rfl rfl] at hn₀
  have hnG : n ≤ ({ P with C₁ := G } : WTParams).N (p + 1) ^ 4 := by
    rwa [N_eq_of P { P with C₁ := G } rfl rfl rfl]
  obtain ⟨hLc, hLt⟩ := hL61 p hp n hnG
  have hin : inputsF { P with C₁ := gC30 (preC₁ P) P.C₁ C₁' } R = inputsF P R := rfl
  simp only [hin]
  have hb0 : (0 : ℝ) ≤ b := by linarith
  refine ⟨fun Q LG q q' hqq hqp hsize hcoh => ?_, fun X LG q q' hqq hqp hsize hcoh => ?_⟩
  · have hQ := hcoh.2.1
    set Bd : (Fin 2 × Path) → NNReal := fun _ => ⟨b, hb0⟩ with hBd
    have hH : LeafwiseControlled LG (layerProfiles LG (inputsF P R)) Bd := fun ℓ _ =>
      input_bound P hS hp hR (by
        exact (layerAt_node LG ℓ.toNode).le.trans (coherentCouple_layer_le hqq hqp hcoh _))
    obtain ⟨hE, hD, hSp⟩ := hLc Q LG q q' hqq hqp hsize hcoh _ Bd hH
    have hβ : leafSizeProduct LG Bd = b ^ (2 * n + 1) := by
      show ∏ _ℓ ∈ inputLeaves LG.garden, b = b ^ (2 * n + 1)
      rw [Finset.prod_const, card_inputLeaves_couple LG.garden hQ.1.1 ((RegCpl.size_eq_order Q hQ).trans hsize)]
    have hsrc : ∀ ts : Fin 2 → ℝ, ∀ k, SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k =
        LeafApp.coherentCouple P.δ LG (layerProfiles LG (inputsF P R)) Q q q' (ts 0) (ts 1) k :=
      fun ts k => sourceCouple_eq (inputsF P R) P.δ hqq hqp hcoh _ _ k
    refine ⟨?_, fun hdom ts hts k => by rw [hsrc]; exact hD hdom ts hts k, ?_⟩
    · have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
            SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k) =
          fun (ts : Fin 2 → ℝ) (k : Mom P.d) =>
            (coupleLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P R)) (ts 0) (ts 1) k -
              LeafApp.coherentCouple P.δ LG (layerProfiles LG (inputsF P R)) Q q q' (ts 0) (ts 1) k) := by
        funext ts k
        rw [KQstar_eq_coupleLeaves, hsrc]
      rw [hfun]
      refine hE.trans ?_
      rw [hβ, hgC]
      exact regBound_absorb P hG0 hb1 hδ hL (by omega)
    · obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := hSp
      refine ⟨m, J, M, hm, fun ts hts k => by beta_reduce; rw [hsrc]; exact hf ts hts k, fun i => (hJ i).trans ?_,
        fun i => (hM i).trans ?_⟩
      · apply ENNReal.ofReal_le_ofReal
        show G * G ^ n ≤ gC30 (preC₁ P) P.C₁ C₁' * gC30 (preC₁ P) P.C₁ C₁' ^ n
        rw [hgC]
        exact sep_absorb₀ hG0 hb1 n
      · apply ENNReal.ofReal_le_ofReal
        show G * G ^ n * leafSizeProduct LG Bd ≤ gC30 (preC₁ P) P.C₁ C₁' * gC30 (preC₁ P) P.C₁ C₁' ^ n
        rw [hβ, hgC]
        exact sep_absorb hG0 hb1 (by omega)
  · have hX := hcoh.2.1
    set Bd : (Fin 1 × Path) → NNReal := fun _ => ⟨b, hb0⟩ with hBd
    have hH : LeafwiseControlled LG (layerProfiles LG (inputsF P R)) Bd := fun ℓ _ =>
      input_bound P hS hp hR (by
        exact (layerAt_node LG ℓ.toNode).le.trans ((coherentTree_layer_le hqq hcoh _).trans hqp))
    obtain ⟨hE, hD, hSp⟩ := hLt X LG q q' hqq hqp hsize hcoh _ Bd hH
    have hcard := card_inputLeaves_tree_le hX hsize
    have hβ : leafSizeProduct LG Bd = b ^ (inputLeaves LG.garden).card := by
      show ∏ _ℓ ∈ inputLeaves LG.garden, b = _
      rw [Finset.prod_const]
    have hsrc : ∀ ts : Fin 2 → ℝ, ∀ k, SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k =
        LeafApp.coherentTree P.δ LG (layerProfiles LG (inputsF P R)) X q q' (ts 0) (ts 1) k :=
      fun ts k => sourceTree_eq (inputsF P R) P.δ hqq hcoh _ _ k
    refine ⟨?_, fun hdom ts hts k => by rw [hsrc]; exact hD hdom ts hts k, ?_⟩
    · have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
            SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k) =
          fun (ts : Fin 2 → ℝ) (k : Mom P.d) => treeLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P R)) (ts 0) (ts 1) k -
            LeafApp.coherentTree P.δ LG (layerProfiles LG (inputsF P R)) X q q' (ts 0) (ts 1) k := by
        funext ts k
        rw [KTstar_eq_treeLeaves, hsrc]
      rw [hfun]
      refine hE.trans ?_
      rw [hβ, hgC]
      exact regBound_absorb P hG0 hb1 hδ hL (by omega)
    · obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := hSp
      refine ⟨m, J, M, hm, fun ts hts k => by beta_reduce; rw [hsrc]; exact hf ts hts k, fun i => (hJ i).trans ?_,
        fun i => (hM i).trans ?_⟩
      · apply ENNReal.ofReal_le_ofReal
        show G * G ^ n ≤ gC30 (preC₁ P) P.C₁ C₁' * gC30 (preC₁ P) P.C₁ C₁' ^ n
        rw [hgC]
        exact sep_absorb₀ hG0 hb1 n
      · apply ENNReal.ofReal_le_ofReal
        show G * G ^ n * leafSizeProduct LG Bd ≤ gC30 (preC₁ P) P.C₁ C₁' * gC30 (preC₁ P) P.C₁ C₁' ^ n
        rw [hβ, hgC]
        exact sep_absorb hG0 hb1 (by omega)


theorem coherent_gate_eq30 : PL2330Pin.CoherentApproximationGate = WTPrefix CABody30 := rfl

/-- **TARGET Prop 6.1 at `Λ₁ = 30d`** (L1097–1111) from B2.1. -/
theorem coherentApproximationGate30 (hA : RegularAsymptoticsGate) (hB : LeafwiseRegularAsymptoticsGate) :
    PL2330Pin.CoherentApproximationGate :=
  wtPrefix_transfer₂' gC30 (fun P₀ x y _ _ => one_le_gC30 P₀ x y) η61 η61_pos hA hB
    fun P C₁' C₂' hS hC₁' _ hAP hBP => caBody30_of P C₁' C₂' hS hC₁' hAP hBP

end WaveTurbulence.PL2330
