/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TruncatedGraftOrderBound
public import WaveTurbulence.Foundations.XChain.CanonicalCoupleGraft
/-! The full source truncated garden and couple classes are finite, including all total orders. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem canonG_trunc_order_le {w p Ntop Natt : ℕ} (LG : LayeredGarden w)
    (hG : IsCanonG (p + 1) LG) (htr : LG.IsTrunc p Ntop Natt) :
    LG.garden.order ≤ w * Ntop + (2 * (w * Ntop) + w) * Natt := by
  obtain ⟨C, he⟩ := exists_canonicalGraftData LG hG
  have hC := (C.sourceTrunc_iff hG.1 Ntop Natt).mp (he.symm ▸ htr)
  exact (congrArg (fun K : LayeredGarden w => K.garden.order) he).symm.trans_le
    (canonicalGraftData_order_le C Ntop Natt hC)

theorem finite_canonG_truncated (w p Ntop Natt : ℕ) :
    {LG : LayeredGarden w | IsCanonG (p + 1) LG ∧ LG.IsTrunc p Ntop Natt}.Finite :=
  (Canon.finite_canonG (p + 1) (w * Ntop + (2 * (w * Ntop) + w) * Natt) w).subset
    (fun LG h => ⟨h.1, canonG_trunc_order_le LG h.1 h.2⟩)

theorem canonC_trunc_order_le {p Ntop Natt : ℕ} (LG : LayeredGarden 2)
    (hG : IsCanonC (p + 1) LG) (htr : LG.IsTrunc p Ntop Natt) :
    LG.garden.order ≤ 2 * Ntop + (2 * (2 * Ntop) + 2) * Natt := by
  obtain ⟨C, he⟩ := exists_canonicalCoupleGraftData LG p hG
  have hr : ∃ D : CanonicalGraftData ![1, -1] p, D.graft = LG :=
    (congrArg (fun sig => ∃ D : CanonicalGraftData sig p, D.graft = LG) hG.1.2).mp ⟨C, he⟩
  obtain ⟨D, hD⟩ := hr
  have htrD := (D.sourceTrunc_iff_couple Ntop Natt).mp (hD.symm ▸ htr)
  exact (congrArg (fun K : LayeredGarden 2 => K.garden.order) hD).symm.trans_le
    (canonicalGraftData_order_le D Ntop Natt htrD)

theorem finite_canonC_truncated (p Ntop Natt : ℕ) :
    {LG : LayeredGarden 2 | IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt}.Finite :=
  (Canon.finite_canonC (p + 1) (2 * Ntop + (2 * (2 * Ntop) + 2) * Natt)).subset
    (fun LG h => ⟨h.1, canonC_trunc_order_le LG h.1 h.2⟩)

end WaveTurbulence.Induct
