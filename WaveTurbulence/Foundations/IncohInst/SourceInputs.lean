/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRoot
public import WaveTurbulence.Foundations.IncohInst.TreeCarrier
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-! # Exact source input indices for couples and paired trees -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The original couple input set is exactly its positive source leaves. -/
theorem couple_inputLeaves {G : Garden 2} (hG : IsCouple G) : inputLeaves G = plusLeaves G := by
  ext ℓ
  simp only [inputLeaves, plusLeaves, Finset.mem_filter, Finset.mem_univ, true_and, hG.1 ℓ, and_true]

/-- The original paired-tree input set is exactly its paired positive leaves. -/
theorem tree_inputLeaves {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    inputLeaves G = plusPaired G := by
  ext ℓ
  simp only [inputLeaves, plusPaired, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hm⟩
    exact ⟨hs, fun hp => ((G.pair_eq_iff ℓ).1 hp) hm⟩
  · rintro ⟨hs, hp⟩
    refine ⟨hs, ?_⟩
    rw [hX.2.1 ℓ, ite_eq_right (fun he => hp ((tree_pair_eq_iff hX ℓ).2 he))]

/-- Couple input factors, in precisely the finite order consumed by the analytic carrier. -/
@[expose] def coupleInputFunctions {d : ℕ} (LG : LayeredGarden 2)
    (F : ℕ → Mom d → ℝ) : Fin (Fintype.card (PlusLeaf LG.garden)) → Mom d → ℂ :=
  fun a k => F (LG.layer ((coupleInputEquiv LG.garden).symm a).1.toNode) k

/-- Paired-tree input factors omit the lone leaf, exactly as in B2's literal kernel. -/
@[expose] def treeInputFunctions {d : ℕ} (LG : LayeredGarden 1)
    (F : ℕ → Mom d → ℝ) : Fin (Fintype.card (TPlus LG.garden)) → Mom d → ℂ :=
  fun a k => F (LG.layer ((treeInputEquiv LG.garden).symm a).1.toNode) k

/-- Source input norm control transfers directly to the actual couple input enumeration. -/
theorem coupleInputFunctions_spatialNorm_le {d K M : ℕ} (LG : LayeredGarden 2)
    (F : ℕ → Mom d → ℝ) {p : ℕ} (hp : ∀ a, LG.layer a ≤ p) {B : ℝ}
    (hF : ∀ r ≤ p, Fourier.spatialNorm K M (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B)
    (a : Fin (Fintype.card (PlusLeaf LG.garden))) :
    Fourier.spatialNorm K M (coupleInputFunctions LG F a) ≤ ENNReal.ofReal B :=
  hF _ (hp _)

/-- Source input norm control transfers directly to the actual tree input enumeration. -/
theorem treeInputFunctions_spatialNorm_le {d K M : ℕ} (LG : LayeredGarden 1)
    (F : ℕ → Mom d → ℝ) {p : ℕ} (hp : ∀ a, LG.layer a ≤ p) {B : ℝ}
    (hF : ∀ r ≤ p, Fourier.spatialNorm K M (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B)
    (a : Fin (Fintype.card (TPlus LG.garden))) :
    Fourier.spatialNorm K M (treeInputFunctions LG F a) ≤ ENNReal.ofReal B :=
  hF _ (hp _)

end WaveTurbulence.IncohInst
