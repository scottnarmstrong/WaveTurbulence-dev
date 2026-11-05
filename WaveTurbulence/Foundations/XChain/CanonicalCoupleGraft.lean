/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
/-! The same exact graft construction and truncation equivalence for two-point couples. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem existsUnique_topDecomp_couple (LG : LayeredGarden 2) (p : ℕ)
    (hG : IsCanonC (p + 1) LG) :
    ∃! P : Finpartition (LG.attachNodes p),
      LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P := by
  have ht := ((Canon.part3 p LG).mp hG).2.2
  obtain ⟨U, P, hP⟩ := Canon.Rel.unfold_topDecomp ht
  have hU := (Canon.uniqueness p false U P hP).1
  subst U
  exact ⟨P, hP, fun Q hQ => topDecomp_partition_unique LG p false _ Q P hQ hP⟩

theorem exists_canonicalCoupleGraftData (LG : LayeredGarden 2) (p : ℕ)
    (hG : IsCanonC (p + 1) LG) : ∃ C : CanonicalGraftData LG.garden.sig p, C.graft = LG := by
  obtain ⟨P, hTD, _⟩ := existsUnique_topDecomp_couple LG p hG
  exact ⟨inverseCanonicalGraftData LG p hG.2.1 hG.1.1 (garden_two_irreducible _) P hTD,
    inverseCanonicalGraftData_graft LG p hG.2.1 hG.1.1 (garden_two_irreducible _) P hTD⟩

namespace CanonicalGraftData

theorem graft_isCanonC {p : ℕ} (C : CanonicalGraftData ![1, -1] p) : IsCanonC (p + 1) C.graft := by
  refine ⟨⟨fun _ => rfl, rfl⟩, ?_⟩
  exact layeredGardenGraft_criterion _ C.top C.partition C.low p C.plain C.sign C.layer_bound
    (fun B => (C.component B).imp_right (fun h => h.2.2))

theorem sourceTrunc_iff_couple {p : ℕ} (C : CanonicalGraftData ![1, -1] p)
    (Ntop Natt : ℕ) : C.graft.IsTrunc p Ntop Natt ↔ C.IsTrunc Ntop Natt := by
  have hG := C.graft_isCanonC
  obtain ⟨P, hTD, _⟩ := existsUnique_topDecomp_couple C.graft p hG
  let D : CanonicalGraftData ![1, -1] p :=
    inverseCanonicalGraftData C.graft p hG.2.1 hG.1.1 (garden_two_irreducible _) P hTD
  have hd : D = C := canonicalGraftData_graft_injective
    (inverseCanonicalGraftData_graft C.graft p hG.2.1 hG.1.1 (garden_two_irreducible _) P hTD)
  have ht := sourceTrunc_iff_inverse_bounds C.graft p Ntop Natt hG.2.1 hG.1.1 P hTD
  change C.graft.IsTrunc p Ntop Natt ↔ D.IsTrunc Ntop Natt at ht
  exact ht.trans ((congrArg (fun A : CanonicalGraftData ![1, -1] p => A.IsTrunc Ntop Natt) hd).to_iff)

end CanonicalGraftData

noncomputable def canonicalCoupleGraftTruncEquiv (p Ntop Natt : ℕ) :
    {C : CanonicalGraftData ![1, -1] p // C.IsTrunc Ntop Natt} ≃
    {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt} :=
  Equiv.ofBijective (fun C => ⟨C.1.graft, C.1.graft_isCanonC,
    (C.1.sourceTrunc_iff_couple Ntop Natt).mpr C.2⟩) (by
    constructor
    · intro C D he
      exact Subtype.ext (canonicalGraftData_graft_injective (congrArg Subtype.val he))
    · rintro ⟨LG, hG, htr⟩
      have hr : ∃ D : CanonicalGraftData ![1, -1] p, D.graft = LG :=
        (congrArg (fun sig => ∃ D : CanonicalGraftData sig p, D.graft = LG) hG.1.2).mp
          (exists_canonicalCoupleGraftData LG p hG)
      obtain ⟨D, hD⟩ := hr
      exact ⟨⟨D, (D.sourceTrunc_iff_couple Ntop Natt).mp (hD.symm ▸ htr)⟩, Subtype.ext hD⟩)

end WaveTurbulence.Induct
