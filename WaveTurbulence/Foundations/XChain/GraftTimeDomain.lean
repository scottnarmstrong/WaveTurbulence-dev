/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTimeBounds
/-! Exact kernel time-domain factorization for plain or flower-marked lower gardens. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kDomain_iff_bounds_order {w : ℕ} (LG : LayeredGarden w) (t s : ℝ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (τ : GBranch LG.garden.tree → ℝ) :
    τ ∈ kDomain LG (fun _ => t) s ↔ LayerTimeBounds LG t τ ∧ BranchOrdered LG.garden.tree τ := by
  constructor
  · intro h
    exact ⟨fun b => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩,
      fun a b hab => (h b).2.2.2.2.1 a hab⟩
  · rintro ⟨hb, ho⟩ b
    refine ⟨(hb b).1, (hb b).2.1, (hb b).2.2.1, (hb b).2.2.2, fun a ha => ho a b ha, ?_⟩
    rintro ⟨ℓ, hℓ, _⟩
    exact False.elim (hn ℓ hℓ)

theorem markedLayeredGardenGraft_no_lone {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower) :
    ∀ ℓ, (markedLayeredGardenGraft sig top P low p hsig hbound).garden.mark ℓ ≠
      some MarkTag.lower := by
  intro ℓ
  obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P (fun B => (low B).garden)).symm.surjective ℓ
  have hm := markedGardenGraft_mark_lower sig top P (fun B => (low B).garden) hsig B l
  exact fun he => hn B l (hm.symm.trans he)

theorem kDomain_markedGraft_iff {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (τ : GBranch (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → ℝ) :
    τ ∈ kDomain (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s ↔
      (graftTimeSplit top P (fun B => (low B).garden) τ).1 ∈ ForestTimeDomain top p t ∧
      ∀ B, (fun b => (graftTimeSplit top P (fun B => (low B).garden) τ).2 ⟨B, b⟩) ∈
        kDomain (low B) (fun _ => p) s := by
  let raw := fun B => (low B).garden
  have hbounds := layerTimeBounds_graft_iff sig top P low p hsig hbound hbranch t hpt htp τ
  have hbig := kDomain_iff_bounds_order
    (markedLayeredGardenGraft sig top P low p hsig hbound) t s
    (markedLayeredGardenGraft_no_lone sig top P low p hsig hbound hn) τ
  constructor
  · intro h
    obtain ⟨hb, ho⟩ := hbig.mp h
    obtain ⟨ht, hl⟩ := hbounds.mp hb
    have hed := branchOrdered_graft_iff top P raw τ p (fun b => (ht b).1)
      (fun B b => (hl B b).2.2.2)
    obtain ⟨hot, hol⟩ := hed.mp ho
    exact ⟨fun b => ⟨(ht b).1, (ht b).2, fun a ha => hot a b ha⟩,
      fun B => (kDomain_iff_bounds_order (low B) p s (hn B) _).mpr ⟨hl B, hol B⟩⟩
  · rintro ⟨ht, hl⟩
    have hlo := fun B => (kDomain_iff_bounds_order (low B) p s (hn B) _).mp (hl B)
    have htop : ∀ b : GBranch top,
        (p : ℝ) < (graftTimeSplit top P raw τ).1 b ∧ (graftTimeSplit top P raw τ).1 b < t :=
      fun b => ⟨(ht b).1, (ht b).2.1⟩
    have hb := hbounds.mpr ⟨htop, fun B => (hlo B).1⟩
    have hed := branchOrdered_graft_iff top P raw τ p (fun b => (ht b).1)
      (fun B b => ((hlo B).1 b).2.2.2)
    exact hbig.mpr ⟨hb, hed.mpr ⟨fun a b ha => (ht b).2.2 a ha, fun B => (hlo B).2⟩⟩

end WaveTurbulence.Induct
