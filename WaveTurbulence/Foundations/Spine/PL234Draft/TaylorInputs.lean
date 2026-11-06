/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.InputBound
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs

/-!
# TARGET Prop 6.2: inputs (the leafwise gate body, decoded single-layer gardens)

* `LRABody`: the body of the spine's `LeafwiseRegularAsymptoticsGate` (`leafwise_gate_eq`: `rfl`);
* `exists_layered_decodes`: every well-formed code decodes a couple carrier, here layered in a single layer.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

/-- The body of the leafwise single-layer gate (spine `LeafwiseRegularAsymptoticsGate`). -/
def LRABody (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (Q.dominant = true → ∀ Z ∈ specialSets Q.links,
        SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B))) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
      (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
        SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B)))

theorem leafwise_gate_eq : LeafwiseRegularAsymptoticsGate = WTPrefix LRABody := rfl

/-- Every well-formed couple code decodes a couple carrier with all layers `p`. -/
theorem exists_layered_decodes (Q : RegCpl) (hwf : Q.wf = true) (p : ℕ) :
    ∃ LG : LayeredGarden 2, Q.Decodes LG.garden ∧ ∀ a, LG.layer a = p := by
  obtain ⟨G, hG, -⟩ := RegCpl.exists_decodes Q hwf
  exact ⟨⟨G, fun _ => p, ⟨fun _ _ => le_rfl, fun _ => rfl⟩⟩, hG, fun _ => rfl⟩

end WaveTurbulence.PL234
