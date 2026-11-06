/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressSingular

/-! # Integrated source parameters no longer affect the source fold -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Function

/-- A folded kernel depends only on the original parameters that have
not been integrated. This is an identity of the actual operators, and
requires neither an exchange of integration order nor a PV limit. -/
theorem addressAppAlong_congr_remaining {d w : ℕ}
    (Z : Finset (Fin w × TTree.Path)) (L : List (Fin w × TTree.Path))
    (S : Set (Fin w × TTree.Path))
    (H : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (hH : ∀ θ θ', (∀ a ∈ S, θ a = θ' a) → H θ = H θ')
    (θ θ' : Fin w × TTree.Path → Mom d × Mom d)
    (hθ : ∀ a ∈ S, a ∉ L → θ a = θ' a) :
    addressAppAlong Z L H θ = addressAppAlong Z L H θ' := by
  classical
  induction L generalizing θ θ' with
  | nil => exact hH θ θ' (fun a ha => hθ a ha (fun h => List.not_mem_nil h))
  | cons a L ih =>
    simp only [addressAppAlong,addressAppStep]
    have he : (fun x y => addressAppAlong Z L H (update θ a (x,y))) =
        (fun x y => addressAppAlong Z L H (update θ' a (x,y))) := by
      funext x y
      apply ih
      intro b hb hnot
      by_cases hba : b=a
      · subst b
        simp only [update_self]
      · simp only [update_of_ne hba]
        exact hθ b hb (by simpa only [List.mem_cons,not_or] using And.intro hba hnot)
    rw [he]

/-- The complete actual child-couple fold is independent of all initial
address parameters, at any independent source placement. -/
theorem addressAppAlong_cplLeafProduct_initial_independent {d w : ℕ}
    (Z : Finset (Fin w × TTree.Path)) (F : Fin w × TTree.Path → Mom d → ℂ) (Q : RegCpl)
    (a b : Fin w × TTree.Path) (r : Mom d) (hab : Indep a b)
    (θ θ' : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q a b r) θ =
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q a b r) θ' := by
  apply addressAppAlong_congr_remaining Z _
    (Set.range (fun l : {l // l ∈ Q.linksAt a b} => l.val.1))
  · intro v v' hv
    apply cplLeafProduct_congr_params F v v' Q a b r hab
    intro l hl
    exact hv l.1 ⟨⟨l,hl⟩,rfl⟩
  · intro z hz hn
    obtain ⟨l,rfl⟩ := hz
    exact (hn (List.mem_map.mpr ⟨l.val,l.property,rfl⟩)).elim

end WaveTurbulence.RA1Leafwise
