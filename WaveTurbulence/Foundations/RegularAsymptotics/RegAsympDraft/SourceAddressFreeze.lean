/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressSingular

/-! # Freezing parameters that remain fixed during an address block -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Function Links

/-- A parameter unchanged by every integrated coordinate may be frozen
before the actual singular fold. This preserves the operator order and
uses no general linearity or Fubini assertion about principal values. -/
theorem addressAppAlong_freeze {d w : ℕ} {T : Type*}
    (Z : Finset (Fin w × TTree.Path)) (L : List (Fin w × TTree.Path))
    (r : (Fin w × TTree.Path → Mom d × Mom d) → T)
    (hr : ∀ a ∈ L, ∀ θ x y, r (update θ a (x,y)) = r θ)
    (H : T → (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z L (fun θ => H (r θ) θ) θ =
      addressAppAlong Z L (H (r θ)) θ := by
  classical
  induction L generalizing θ with
  | nil => rfl
  | cons a L ih =>
    simp only [addressAppAlong,addressAppStep]
    have he : (fun x y => addressAppAlong Z L (fun θ => H (r θ) θ) (update θ a (x,y))) =
        (fun x y => addressAppAlong Z L (H (r θ)) (update θ a (x,y))) := by
      funext x y
      rw [ih (fun b hb => hr b (List.mem_cons_of_mem _ hb)),hr a List.mem_cons_self]
    rw [he]

/-- Updating an address outside a couple's chosen list does not change
its actual leaf kernel, including after arbitrary singular blocks. -/
theorem addressAppAlong_cplLeafProduct_update_of_not_mem {d w : ℕ}
    (Z : Finset (Fin w × TTree.Path)) (L : List (Fin w × TTree.Path))
    (F : Mom d → ℂ) (Q : RegCpl) (a b : Fin w × TTree.Path) (r : Mom d) (hab : Indep a b)
    (z : Fin w × TTree.Path) (hz : z ∉ (Q.linksAt a b).map Prod.fst)
    (θ : Fin w × TTree.Path → Mom d × Mom d) (v : Mom d × Mom d) :
    addressAppAlong Z L (fun θ => cplLeafProduct F θ Q a b r) (update θ z v) =
      addressAppAlong Z L (fun θ => cplLeafProduct F θ Q a b r) θ := by
  classical
  apply addressAppAlong_cplLeafProduct_congr_params Z L F Q a b r hab
  intro l hl
  apply update_of_ne
  intro he
  exact hz (List.mem_map.mpr ⟨l,hl,he⟩)

end WaveTurbulence.RegAsymp
