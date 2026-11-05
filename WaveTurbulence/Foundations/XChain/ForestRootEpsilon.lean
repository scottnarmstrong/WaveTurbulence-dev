/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestSinglePaths
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
public import WaveTurbulence.Foundations.XChain.SignedSeries
/-! The forest epsilon product splits into real epsilon products at its roots. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

theorem zpowSign_epsProd {d : ℕ} (sig : ℤˣ) (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) :
    zpowSign sig (epsProd T κ) = epsProd T κ := by
  unfold zpowSign epsProd
  split_ifs
  · rfl
  · simp only [map_prod, Complex.conj_ofReal]

theorem forest_epsProd_eq_roots {w d : ℕ} (top : Fin w → TTree) (κ : GNode top → (Fin d → ℤ)) :
    (((∏ b : GBranch top, epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))) : ℝ) : ℂ) =
      ∏ j, epsProd (top j) (fun a => κ (singleNodeToForest top j a)) := by
  have hr := Fintype.prod_equiv (forestSingleBranchEquiv top)
    (fun b : GBranch top => epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)))
    (fun z : Σ j : Fin w, GBranch (single (top j)) =>
      epsCoef (κ (singleNodeToForest top z.1 (z.2.child 0)))
        (κ (singleNodeToForest top z.1 (z.2.child 1))) (κ (singleNodeToForest top z.1 (z.2.child 2))))
    (fun _ => rfl)
  rw [Fintype.prod_sigma] at hr
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  have hp := map_prod Complex.ofRealHom
    (fun j : Fin w => ∏ b : GBranch (single (top j)),
      epsCoef (κ (singleNodeToForest top j (b.child 0)))
        (κ (singleNodeToForest top j (b.child 1))) (κ (singleNodeToForest top j (b.child 2)))) univ
  simp only [Complex.ofRealHom_eq_coe] at hp
  refine hc.trans (hp.trans ?_)
  apply prod_congr rfl
  intro j _
  have h := map_prod Complex.ofRealHom (fun b : GBranch (single (top j)) =>
    epsCoef (κ (singleNodeToForest top j (b.child 0)))
      (κ (singleNodeToForest top j (b.child 1))) (κ (singleNodeToForest top j (b.child 2)))) univ
  simpa only [Complex.ofRealHom_eq_coe, epsProd] using h

end WaveTurbulence.Induct
