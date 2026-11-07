/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateH
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemCont

/-! # P2: continuity in time of the exact kernels `K*` of coherent carriers (scope item 1)

`continuous_KQstar_of_coherent`, `continuous_KTstar_of_coherent`: for a coherent couple (tree) carrier `LG` at layers `≤ p` and a layer family
`h` with the size bound `ProfileBound` (so `SNormR (40d) (40d) (h r) < ∞` for `r ≤ p`), the exact kernel `K*_Q(t,s,k)`
(`K*_T`) is continuous in `(t,s)` for every `k`: the garden is plain (resp. a decoded tree) and the inputs are summable on every coset by
`summable_abs_coset_of_SNormR`.  `remainder_cont_of_gate`: with the gate's separated expansion `LeafwiseSeparated`, the remainder `K* - app` has a
continuous a.e.-representative (`remainder_ae_cont`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links
open scoped ENNReal

variable {d : ℕ}

theorem summable_layer_coset {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {r : ℕ} (hr : r ≤ p) (k : Mom P.d) :
    Summable fun n : Fin P.d → ℤ => |h r (k + latticePoint P.L n)| :=
  summable_abs_coset_of_SNormR (A := 40 * P.d) (B := 40 * P.d) hL (by omega) (hB r hr).1 (h r) (hB r hr).2 k

theorem continuous_KQstar_of_coherent {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ}
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (k : Mom P.d) :
    Continuous fun ts : Fin 2 → ℝ => KQstar P.L P.γ P.δ h LG (ts 0) (ts 1) k :=
  continuous_KQstar_time P.L P.γ P.δ h LG hcoh.2.1.1.1 k fun ℓ _ =>
    summable_layer_coset hB hd hL (coherentCouple_layer_le hqq hqp hcoh _) k

theorem continuous_KTstar_of_coherent {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {X : RegChain} {LG : LayeredGarden 1} {q q' : ℕ}
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentTreeAt p q q' X LG) (k : Mom P.d) :
    Continuous fun ts : Fin 2 → ℝ => KTstar P.L P.γ P.δ h LG (ts 0) (ts 1) k := by
  have hX := hcoh.2.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hc := continuous_treeLeaves_time P.L P.γ P.δ LG (PL234.layerProfiles LG h) hfl (card_lone_le_of_decodesTree hX) k
    fun ℓ _ => summable_layer_coset hB hd hL (r := layerAt LG ℓ.1) ((layerAt_node LG ℓ.toNode).le.trans
      ((coherentTree_layer_le hqq hcoh _).trans hqp)) k
  exact hc.congr fun ts => (KTstar_eq_treeLeaves P.L P.γ P.δ h LG (ts 0) (ts 1) k).symm

end WaveTurbulence.VineEstS5C.P2
