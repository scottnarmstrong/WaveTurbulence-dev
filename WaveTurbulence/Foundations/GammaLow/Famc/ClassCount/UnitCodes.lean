/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.IngCode
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCode2
/-! # Unit codes over `IngCodeG` (packet L5c, item I)

Main's `ClassCount.unitCodes`, `unitWeight`, `mem_unitCodes`, `card_unitCodes_le` (Stage1/ClassCount/UnitCode2.lean,
sha256 in COPIED-SHA256SUMS) over the `𝒱_γ` ingredient codes `IngCodeG` (item H): a unit code is a list of ingredient
codes; with `card_ingCodesAtG_le' : ≤ (2^102)^w` the unit codes of weight `W` number at most `(2^103)^W`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount

/-- Unit codes of total weight `W` (lists of counted ingredient codes). -/
noncomputable def unitCodes : ℕ → Finset (List IngCodeG)
  | 0 => {[]}
  | W + 1 => (Finset.range (W + 1)).attach.biUnion (fun i =>
      ((ingCodesAtG (i.1 + 1)) ×ˢ unitCodes (W - i.1)).image (fun p => p.1 :: p.2))
termination_by W => W
decreasing_by omega

/-- Total weight of a unit code. -/
def unitWeight (cs : List IngCodeG) : ℕ := (cs.map (fun c => c.size - 1)).sum

theorem mem_unitCodes : ∀ (cs : List IngCodeG), (∀ c ∈ cs, c.Wf) → cs ∈ unitCodes (unitWeight cs)
  | [], _ => by simp [unitWeight, unitCodes]
  | c :: cs, h => by
    have hc : c.Wf := h c (by simp)
    have hs : 2 ≤ c.size := hc.1
    have ih := mem_unitCodes cs (fun x hx => h x (by simp [hx]))
    have hw : unitWeight (c :: cs) = ((c.size - 2) + unitWeight cs) + 1 := by
      simp only [unitWeight, List.map_cons, List.sum_cons]; omega
    rw [hw, unitCodes]
    refine Finset.mem_biUnion.mpr ⟨⟨c.size - 2, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _, ?_⟩
    refine Finset.mem_image.mpr ⟨(c, cs), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact mem_ingCodesAtG hc (by simp only; omega)
    · have : (c.size - 2 + unitWeight cs) - (c.size - 2) = unitWeight cs := by omega
      simp only
      rw [this]; exact ih

theorem card_unitCodes_le : ∀ W : ℕ, (unitCodes W).card ≤ (2 ^ 103) ^ W
  | 0 => by simp [unitCodes]
  | W + 1 => by
    rw [unitCodes]
    refine Finset.card_biUnion_le.trans ?_
    have hterm : ∀ i : {x // x ∈ Finset.range (W + 1)},
        (((ingCodesAtG (i.1 + 1)) ×ˢ unitCodes (W - i.1)).image (fun p => p.1 :: p.2)).card ≤
          (2 ^ 102) ^ (i.1 + 1) * (2 ^ 103) ^ (W - i.1) := by
      intro i
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      have h1 := card_ingCodesAtG_le' (i.1 + 1) (by omega)
      have h2 := card_unitCodes_le (W - i.1)
      exact Nat.mul_le_mul h1 h2
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    rw [Finset.sum_attach (Finset.range (W + 1)) (fun i => (2 ^ 102) ^ (i + 1) * (2 ^ 103) ^ (W - i))]
    have := WaveTurbulence.ClassCount.geom_sum_bound (2 ^ 102) W
    simpa [pow_succ] using this

end WaveTurbulence.GammaLow.Famc.ClassCount
