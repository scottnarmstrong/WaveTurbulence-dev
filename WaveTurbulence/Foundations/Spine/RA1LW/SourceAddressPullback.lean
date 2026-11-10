/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressSingular

/-! # Exact pullback of singular address folds under injective embeddings -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Function

/-- Updating an embedded address pulls back to the same single-coordinate
update when the embedding is injective. -/
theorem address_update_comp {d w w' : ℕ}
    (e : Fin w × TTree.Path → Fin w' × TTree.Path) (he : Injective e)
    (θ : Fin w' × TTree.Path → Mom d × Mom d) (a : Fin w × TTree.Path)
    (v : Mom d × Mom d) :
    (fun z => update θ (e a) v (e z)) = update (fun z => θ (e z)) a v := by
  classical
  funext z
  simp only [update_apply,he.eq_iff]

/-- An actual singular fold pulls back exactly under an injective address
embedding, with its marked nodes pulled back literally. No analytic
exchange of singular operators is used. -/
theorem addressAppAlong_pullback {d w w' : ℕ}
    (e : Fin w × TTree.Path → Fin w' × TTree.Path) (he : Injective e)
    (Z : Finset (Fin w' × TTree.Path)) (Z' : Finset (Fin w × TTree.Path))
    (hZ : ∀ a, e a ∈ Z ↔ a ∈ Z')
    (L : List (Fin w × TTree.Path))
    (H : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (θ : Fin w' × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (L.map e) (fun θ => H (fun z => θ (e z))) θ =
      addressAppAlong Z' L H (fun z => θ (e z)) := by
  classical
  induction L generalizing θ with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons,addressAppAlong,addressAppStep,hZ]
    have hfun : (fun x y => addressAppAlong Z (L.map e)
        (fun θ => H (fun z => θ (e z))) (update θ (e a) (x,y))) =
        (fun x y => addressAppAlong Z' L H (update (fun z => θ (e z)) a (x,y))) := by
      funext x y
      rw [ih,address_update_comp e he]
    rw [hfun]

end WaveTurbulence.RA1Leafwise
