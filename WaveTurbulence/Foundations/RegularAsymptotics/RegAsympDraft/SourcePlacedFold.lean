/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceLinkRelocation
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressPullback
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressNorm
import Mathlib.Data.Finset.Preimage

/-! # Complete source folds at arbitrary independent root placements -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

/-- Moving the actual source code to independent roots changes only the
address labels of its singular fold and the literal marked-node set. -/
theorem addressAppAlong_source_rootPlacement {d w : ℕ}
    (Z : Finset (Fin w × Path)) (F : Mom d → ℂ) (Q : RegCpl)
    (a b : Fin w × Path) (k : Mom d) (hab : Indep a b)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q a b k) θ =
    addressAppAlong (Z.preimage (rootPlacement a b) (rootPlacement_injective hab).injOn)
      (Q.links.map Prod.fst)
      (fun θ => cplLeafProduct F θ Q (0,[]) (1,[]) k)
      (fun z => θ (rootPlacement a b z)) := by
  have hlist : (Q.linksAt a b).map Prod.fst =
      (Q.links.map Prod.fst).map (rootPlacement a b) := by
    rw [cpl_links_rootPlacement,List.map_map,List.map_map]
    rfl
  have hkernel : (fun θ => cplLeafProduct F θ Q a b k) =
      (fun θ => cplLeafProduct F (fun z => θ (rootPlacement a b z)) Q (0,[]) (1,[]) k) := by
    funext θ
    exact cplLeafProduct_rootPlacement F θ Q a b k hab
  rw [hlist,hkernel]
  exact addressAppAlong_pullback (rootPlacement a b) (rootPlacement_injective hab) Z _
    (fun _ => Finset.mem_preimage.symm) (Q.links.map Prod.fst)
    (fun θ => cplLeafProduct F θ Q (0,[]) (1,[]) k) θ

/-- The original geometric spatial estimate holds for the complete source
fold at every independent pair of roots. Its constant precedes both the
code order and the placement. -/
theorem source_placed_fold_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Garden 2) (Q : RegCpl) (_hQ : Q.Decodes G) (_hG : IsCouple G),
      0 < Q.links.length → ∀ F : Mom d → ℂ,
      Fourier.spatialNorm (40*d) (40*d) F ≤ ENNReal.ofReal B →
      ∀ (w : ℕ) (Z : Finset (Fin w × Path)) (a b : Fin w × Path), Indep a b →
      ∀ θ : Fin w × Path → Mom d × Mom d,
      Fourier.spatialNorm (30*d) (30*d) (fun k =>
        addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
          (fun θ => cplLeafProduct F θ Q a b k) θ) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨C,hC,hbound⟩ := source_address_fold_spatial_bound hd hB
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG hn F hF w Z a b hab θ
  have he : (fun k => addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q a b k) θ) =
      (fun k => addressAppAlong (Z.preimage (rootPlacement a b) (rootPlacement_injective hab).injOn)
        (Q.links.map Prod.fst) (fun θ => cplLeafProduct F θ Q (0,[]) (1,[]) k)
        (fun z => θ (rootPlacement a b z))) := by
    funext k
    exact addressAppAlong_source_rootPlacement Z F Q a b k hab θ
  rw [he]
  exact hbound G Q hQ hG hn F hF _ _

end WaveTurbulence.RegAsymp
