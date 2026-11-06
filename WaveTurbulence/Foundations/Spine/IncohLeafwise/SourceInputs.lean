/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRoot
public import WaveTurbulence.Foundations.IncohInst.TreeCarrier
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs

/-! # Exact source input indices for couples and paired trees -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links
open WaveTurbulence.LGSpine

/-- The original couple input set is exactly its positive source leaves. -/
theorem couple_inputLeavesL {G : Garden 2} (hG : IsCouple G) : inputLeaves G = plusLeaves G := by
  ext ℓ
  simp only [inputLeaves, plusLeaves, Finset.mem_filter, Finset.mem_univ, true_and, hG.1 ℓ, and_true]

/-- The original paired-tree input set is exactly its paired positive leaves. -/
theorem tree_inputLeavesL {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    inputLeaves G = plusPaired G := by
  ext ℓ
  simp only [inputLeaves, plusPaired, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hm⟩
    exact ⟨hs, fun hp => ((G.pair_eq_iff ℓ).1 hp) hm⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, ?_⟩
    rw [hX.2.1 ℓ, ite_eq_right (fun he => hp ((tree_pair_eq_iff hX ℓ).2 he))]

/-- Couple input factors for per-leaf profiles, in the finite order consumed by the analytic carrier. -/
@[expose] def coupleInputFunctionsL {d : ℕ} (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) : Fin (Fintype.card (PlusLeaf LG.garden)) → Mom d → ℂ :=
  fun a k => H ((coupleInputEquiv LG.garden).symm a).1.1 k

/-- Paired-tree input factors for per-leaf profiles; the lone leaf is omitted. -/
@[expose] def treeInputFunctionsL {d : ℕ} (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) : Fin (Fintype.card (TPlus LG.garden)) → Mom d → ℂ :=
  fun a k => H ((treeInputEquiv LG.garden).symm a).1.1 k

/-- Per-leaf norm control transfers to the actual couple input enumeration. -/
theorem coupleInputFunctions_spatialNorm_leL {d K M : ℕ} {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (H : LeafProfiles 2 d) {B : ℝ}
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm K M (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B)
    (a : Fin (Fintype.card (PlusLeaf LG.garden))) :
    Fourier.spatialNorm K M (coupleInputFunctionsL LG H a) ≤ ENNReal.ofReal B := by
  apply hH
  rw [couple_inputLeavesL hQ.1]
  have := ((coupleInputEquiv LG.garden).symm a).2
  simpa [plusLeaves] using this

/-- Per-leaf norm control transfers to the actual tree input enumeration. -/
theorem treeInputFunctions_spatialNorm_leL {d K M : ℕ} {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LeafProfiles 1 d) {B : ℝ}
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm K M (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B)
    (a : Fin (Fintype.card (TPlus LG.garden))) :
    Fourier.spatialNorm K M (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal B := by
  apply hH
  rw [tree_inputLeavesL hX]
  have := ((treeInputEquiv LG.garden).symm a).2
  simpa [plusPaired] using this

end WaveTurbulence.IncohLeafwise
