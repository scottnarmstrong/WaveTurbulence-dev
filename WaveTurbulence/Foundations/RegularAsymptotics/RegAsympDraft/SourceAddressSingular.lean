/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressParameters
public import WaveTurbulence.Foundations.RegAsymp.CellSingularBlocks

/-! # Actual singular operations at the original chosen source addresses -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Function Finset

/-- The original local delta/PV operator acting on one address parameter. -/
def addressAppStep {d w : ℕ} (Z : Finset (Fin w × TTree.Path)) (a : Fin w × TTree.Path)
    (H : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (θ : Fin w × TTree.Path → Mom d × Mom d) : ℂ :=
  if a ∈ Z then pvOp (fun x y => H (update θ a (x,y)))
  else NTSP.deltaInner (fun x y => H (update θ a (x,y)))

/-- The outer-to-inner fold of the original source-address singular operations. -/
def addressAppAlong {d w : ℕ} (Z : Finset (Fin w × TTree.Path)) :
    List (Fin w × TTree.Path) →
    ((Fin w × TTree.Path → Mom d × Mom d) → ℂ) →
    (Fin w × TTree.Path → Mom d × Mom d) → ℂ
  | [], H => H
  | a::L, H => addressAppStep Z a (addressAppAlong Z L H)

/-- Address block concatenation is exactly composition of actual singular operators. -/
theorem addressAppAlong_append {d w : ℕ} (Z : Finset (Fin w × TTree.Path))
    (L K : List (Fin w × TTree.Path))
    (H : (Fin w × TTree.Path → Mom d × Mom d) → ℂ) :
    addressAppAlong Z (L++K) H = addressAppAlong Z L (addressAppAlong Z K H) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.cons_append,addressAppAlong,ih]

/-- Splitting the two arrays commutes with a literal pair-coordinate update. -/
theorem pairArray_update {d n : ℕ} (x y : Fin n → Mom d) (j : Fin n) (a b : Mom d) :
    (fun i => (update x j a i,update y j b i)) = update (fun i => (x i,y i)) j (a,b) := by
  classical
  funext i
  by_cases hi : i=j
  · subst i
    simp only [update_self]
  · simp only [update_of_ne hi]

/-- The finite actual link coordinates and the original chosen-node
addresses carry exactly the same singular operations, before any Fubini
or analytic estimate. No alternate source parameter map is introduced. -/
theorem addressAppAlong_map_chosenNode {d : ℕ} (Q : RegCpl)
    (Z : Finset (Fin 2 × TTree.Path)) (L : List (Fin Q.links.length))
    (H : (Fin 2 × TTree.Path → Mom d × Mom d) → ℂ) (x y : Fin Q.links.length → Mom d) :
    addressAppAlong Z (L.map (chosenNode Q)) H (paramFun Q (fun i => (x i,y i))) =
      appAlong (markedLinkIndices Q Z) L
        (fun x y => H (paramFun Q (fun i => (x i,y i)))) x y := by
  classical
  induction L generalizing x y with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons,addressAppAlong,addressAppStep,appAlong,appStep,
      markedLinkIndices,mem_filter,mem_univ,true_and]
    have hfun : (fun a b => addressAppAlong Z (L.map (chosenNode Q)) H
        (update (paramFun Q (fun i => (x i,y i))) (chosenNode Q j) (a,b))) =
        (fun a b => appAlong (markedLinkIndices Q Z) L
          (fun x y => H (paramFun Q (fun i => (x i,y i)))) (update x j a) (update y j b)) := by
      funext a b
      rw [← paramFun_update,← pairArray_update]
      exact ih _ _
    rw [hfun]
    rfl

/-- If a kernel depends only on a specified set of actual address
parameters, every folded singular operation preserves that dependence. -/
theorem addressAppAlong_congr_on {d w : ℕ} (Z : Finset (Fin w × TTree.Path))
    (L : List (Fin w × TTree.Path)) (S : Set (Fin w × TTree.Path))
    (H : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (hH : ∀ θ θ', (∀ a ∈ S, θ a = θ' a) → H θ = H θ')
    (θ θ' : Fin w × TTree.Path → Mom d × Mom d)
    (hθ : ∀ a ∈ S, θ a = θ' a) :
    addressAppAlong Z L H θ = addressAppAlong Z L H θ' := by
  classical
  induction L generalizing θ θ' with
  | nil => exact hH θ θ' hθ
  | cons a L ih =>
    simp only [addressAppAlong,addressAppStep]
    have hfun : (fun x y => addressAppAlong Z L H (update θ a (x,y))) =
        (fun x y => addressAppAlong Z L H (update θ' a (x,y))) := by
      funext x y
      apply ih
      intro b hb
      by_cases he : b=a
      · subst b
        simp only [update_self]
      · simp only [update_of_ne he]
        exact hθ b hb
    rw [hfun]

/-- The actual folded couple leaf product depends only on its own
chosen link parameters, including at arbitrary independent placements. -/
theorem addressAppAlong_cplLeafProduct_congr_params {d w : ℕ}
    (Z : Finset (Fin w × TTree.Path)) (L : List (Fin w × TTree.Path))
    (F : Mom d → ℂ) (Q : RegCpl) (a b : Fin w × TTree.Path) (r : Mom d) (hab : Indep a b)
    (θ θ' : Fin w × TTree.Path → Mom d × Mom d)
    (hθ : ∀ l ∈ Q.linksAt a b, θ l.1 = θ' l.1) :
    addressAppAlong Z L (fun θ => cplLeafProduct F θ Q a b r) θ =
      addressAppAlong Z L (fun θ => cplLeafProduct F θ Q a b r) θ' := by
  apply addressAppAlong_congr_on Z L (Set.range (fun l : {l // l ∈ Q.linksAt a b} => l.val.1))
  · intro v v' hv
    apply cplLeafProduct_congr_params F v v' Q a b r hab
    intro l hl
    exact hv l.1 ⟨⟨l,hl⟩,rfl⟩
  · intro z hz
    obtain ⟨l,rfl⟩ := hz
    exact hθ l.val l.property

end WaveTurbulence.RegAsymp
