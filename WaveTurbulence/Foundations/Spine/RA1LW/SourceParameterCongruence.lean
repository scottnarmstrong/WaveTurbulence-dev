/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceType2Products
public import WaveTurbulence.Foundations.IncohInst.Links.Construct5

/-! # Original leaf kernels depend only on the chosen link parameters -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open Links Reg TTree

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- Parameter values away from the actual chosen links do not alter the
original couple leaf kernel, including its literal global placements. -/
theorem cplLeafProduct_congr_params (F : Fin w × Path → V → ℂ) (θ θ' : Fin w × Path → V × V)
    (Q : RegCpl) (a b : Fin w × Path) (r : V) (hab : Indep a b)
    (hθ : ∀ l ∈ Q.linksAt a b, θ l.1 = θ' l.1) :
    cplLeafProduct F θ Q a b r = cplLeafProduct F θ' Q a b r := by
  have hp (l) (hl : l ∈ Q.linksAt a b) :
      xv (cplVal θ Q a b r) l.1 = (θ' l.1).1 ∧
        yv (cplVal θ Q a b r) l.1 = (θ' l.1).2 := by
    have hh := cplVal_params θ Q a b r hab (cplVal θ Q a b r) (fun _ _ => rfl) l hl
    rw [hθ l hl] at hh
    exact hh
  have hv := cplDec_determined θ' Q a b r hab (cplVal θ Q a b r)
    (cplDec_cplVal θ Q a b r hab) (cplVal_root θ Q a b r hab).1 hp
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hmem
  apply congrArg (F p.1)
  exact hv p.1 (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hmem,Or.inl rfl⟩))

/-- The same localization of parameters holds for the chain's paired
leaf kernel; its excluded continuation contributes no input factor. -/
theorem chainLeafProduct_congr_params (F : Fin w × Path → V → ℂ) (θ θ' : Fin w × Path → V × V)
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V)
    (cont cont' : Fin w × Path → V)
    (hθ : ∀ l ∈ X.linksAt ζ a, θ l.1 = θ' l.1) :
    chainLeafProduct F θ X ζ a u cont = chainLeafProduct F θ' X ζ a u cont' := by
  rw [chainLeafProduct_cont_independent F θ X ζ a u cont (fun _ => u),
    chainLeafProduct_cont_independent F θ' X ζ a u cont' (fun _ => u)]
  have hp (l) (hl : l ∈ X.linksAt ζ a) :
      xv (chainVal θ X ζ a u (fun _ => u)) l.1 = (θ' l.1).1 ∧
        yv (chainVal θ X ζ a u (fun _ => u)) l.1 = (θ' l.1).2 := by
    have hh := chainVal_params θ X ζ a u (fun _ => u) rfl
      (chainVal θ X ζ a u (fun _ => u)) (fun _ _ _ => rfl) l hl
    rw [hθ l hl] at hh
    exact hh
  have hv := chainDec_determined θ' X ζ a u (fun _ => u) rfl
    (chainVal θ X ζ a u (fun _ => u)) (chainDec_chainVal θ X ζ a u (fun _ => u) rfl)
    (chainVal_root θ X ζ a u (fun _ => u) rfl) hp
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hmem
  apply congrArg (F p.1)
  exact hv p.1 (Finset.mem_union_right _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hmem,Or.inl rfl⟩))

end WaveTurbulence.RA1Leafwise
