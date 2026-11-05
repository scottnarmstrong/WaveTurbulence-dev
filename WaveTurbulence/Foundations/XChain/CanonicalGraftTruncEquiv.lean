/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftEquiv
public import WaveTurbulence.Foundations.XChain.InverseGraftTruncation
/-! The structural graft bijection preserves the precise source truncation bounds. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

namespace CanonicalGraftData

def IsTrunc {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p) (Ntop Natt : ℕ) : Prop :=
  (∀ j, (C.top j).order ≤ Ntop) ∧ ∀ B, (C.low B).garden.order ≤ Natt

theorem sourceTrunc_iff {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (hw : 4 ≤ w) (Ntop Natt : ℕ) : C.graft.IsTrunc p Ntop Natt ↔ C.IsTrunc Ntop Natt := by
  have hG := C.graft_isCanonG hw
  obtain ⟨P, hTD, _⟩ := existsUnique_topDecomp C.graft p hG
  let D : CanonicalGraftData sig p :=
    inverseCanonicalGraftData C.graft p hG.2.2.2.1 hG.2.1 hG.2.2.1 P hTD
  have hd : D = C := canonicalGraftData_graft_injective
    (inverseCanonicalGraftData_graft C.graft p hG.2.2.2.1 hG.2.1 hG.2.2.1 P hTD)
  have ht := sourceTrunc_iff_inverse_bounds C.graft p Ntop Natt hG.2.2.2.1 hG.2.1 P hTD
  change C.graft.IsTrunc p Ntop Natt ↔ D.IsTrunc Ntop Natt at ht
  exact ht.trans ((congrArg (fun A : CanonicalGraftData sig p => A.IsTrunc Ntop Natt) hd).to_iff)

end CanonicalGraftData

noncomputable def canonicalGraftTruncEquiv {w p : ℕ} (sig : Fin w → ℤˣ) (hw : 4 ≤ w)
    (Ntop Natt : ℕ) : {C : CanonicalGraftData sig p // C.IsTrunc Ntop Natt} ≃
      {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧ LG.IsTrunc p Ntop Natt} :=
  Equiv.ofBijective (fun C => ⟨C.1.graft, C.1.graft_isCanonG hw, rfl,
    (C.1.sourceTrunc_iff hw Ntop Natt).mpr C.2⟩) (by
    constructor
    · intro C D he
      exact Subtype.ext (canonicalGraftData_graft_injective (congrArg Subtype.val he))
    · rintro ⟨LG, hG, hs, htr⟩
      have hr : ∃ C : CanonicalGraftData sig p, C.graft = LG := by
        cases hs
        exact exists_canonicalGraftData LG hG
      obtain ⟨C, he⟩ := hr
      have hC := (C.sourceTrunc_iff hw Ntop Natt).mp (he.symm ▸ htr)
      exact ⟨⟨C, hC⟩, Subtype.ext he⟩)

end WaveTurbulence.Induct
