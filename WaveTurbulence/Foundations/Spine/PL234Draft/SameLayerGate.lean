/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayerApprox

/-!
# TARGET Prop 6.1 when `q = q'` (TARGET L1235: "the result follows from Proposition `regref1`")

At parameters where the B2.1 body holds, for coherent eligible objects with equal parent layers:

* `coupleGate_same`: the three conjuncts of the couple part of `CoherentApproximationGate` at `q = q'`;
* `treeGate_same`: the same for regular trees whose lone leaf is in the root's parent layer.

The objects lie in one layer `q` (`coherentCouple_layer_eq`, `coherentTree_layer_eq`), so the
layer-indexed inputs `inputsF P R` are the single input `F_q` of B2.1, and `SourceApp` is B2's `app`
(`SourceApp.couple_same_layer`, `SourceApp.tree_same_layer`).
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-- **TARGET Prop 6.1 for a coherent couple with `q = q'`.** -/
theorem coupleGate_same (P : WTParams) (hB : B21Body P) {p : ℕ} (hp : p < P.D)
    (R : ℕ → Mom P.d → ℝ) (hR : ∀ r ≤ p, InputRemainder P (R r) r) {n : ℕ}
    (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LG : LayeredGarden 2) {q : ℕ} (hq : q ≤ p)
    (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q Q LG) :
    (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q) Set.univ
        (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.couple P.δ (inputsF P R) LG Q q q (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q, ∀ k,
        SourceApp.couple P.δ (inputsF P R) LG Q q q (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n (30 * P.d) (timeBox q q)
        (fun ts k => SourceApp.couple P.δ (inputsF P R) LG Q q q (ts 0) (ts 1) k) := by
  have hlay := coherentCouple_layer_eq hcoh
  have hwf := hcoh.1
  have hQ := hcoh.2.1
  have hB' := hB p hp q hq (R q) (hR q hq) n hn
  dsimp only at hB'
  obtain ⟨h1, -, h3, -, -⟩ := hB'
  simp only [SourceApp.couple_same_layer]
  refine ⟨?_, fun hdom ts _ k => by simp [RegCpl.app, hdom], ?_⟩
  · have he : (fun (ts : Fin 2 → ℝ) k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
        Q.app P.δ q (inputsF P R q) (ts 0) (ts 1) k) =
        fun ts k => KQstar P.L P.γ P.δ (fun _ => fun k => P.φ (P.δ * q) k + R q k) LG (ts 0) (ts 1) k -
          Q.app P.δ q (fun k => P.φ (P.δ * q) k + R q k) (ts 0) (ts 1) k := by
      funext ts k
      rw [KQstar_congr_layer P.L P.γ P.δ (inputsF P R) LG hlay]
      rfl
    rw [he]
    exact h1 Q hwf hsize LG hQ hlay
  · exact sourceSeparated_app_couple P (timeBox q q) q (inputsF P R q) Q hsize
      fun hdom => h3 Q hwf hdom hsize

/-- **TARGET Prop 6.1 for a coherent regular tree with `q = q'`.** -/
theorem treeGate_same (P : WTParams) (hB : B21Body P) {p : ℕ} (hp : p < P.D)
    (R : ℕ → Mom P.d → ℝ) (hR : ∀ r ≤ p, InputRemainder P (R r) r) {n : ℕ}
    (hn : n ≤ P.N (p + 1) ^ 4) (X : RegChain) (LG : LayeredGarden 1) {q : ℕ} (hq : q ≤ p)
    (hsize : X.size = 2 * n) (hcoh : IsCoherentTreeAt p q q X LG) :
    (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q) Set.univ
        (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.tree P.δ (inputsF P R) LG X q q (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q, ∀ k,
        SourceApp.tree P.δ (inputsF P R) LG X q q (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n 0 (timeBoxGt q q)
        (fun ts k => SourceApp.tree P.δ (inputsF P R) LG X q q (ts 0) (ts 1) k) := by
  have hlay := coherentTree_layer_eq hcoh
  have hwf := hcoh.1
  have hX := hcoh.2.1
  have hB' := hB p hp q hq (R q) (hR q hq) n hn
  dsimp only at hB'
  obtain ⟨-, h2, -, h3, -⟩ := hB'
  simp only [SourceApp.tree_same_layer]
  refine ⟨?_, fun hdom ts _ k => by simp [RegChain.app, hdom], ?_⟩
  · have he : (fun (ts : Fin 2 → ℝ) k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
        X.app P.δ q (inputsF P R q) (LG.garden.sig 0) (ts 0) (ts 1) k) =
        fun ts k => KTstar P.L P.γ P.δ (fun _ => fun k => P.φ (P.δ * q) k + R q k) LG (ts 0) (ts 1) k -
          X.app P.δ q (fun k => P.φ (P.δ * q) k + R q k) (LG.garden.sig 0) (ts 0) (ts 1) k := by
      funext ts k
      rw [KTstar_congr_layer P.L P.γ P.δ (inputsF P R) LG (fun ℓ _ => hlay _)]
      rfl
    rw [he]
    exact h2 X hwf hsize LG hX q le_rfl fun a => by rw [hlay a]; split_ifs <;> rfl
  · exact sourceSeparated_app_tree P (timeBoxGt q q) q (inputsF P R q) X (LG.garden.sig 0) hsize
      fun hdom => h3 X hwf hdom hsize (LG.garden.sig 0) q le_rfl

end WaveTurbulence.PL234
