/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Flat
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.FlatBound

/-! # V5-SPACE-EXT: the literal class with the bond multiplier is the weighted flat observable

`twistedRecenteredModCX_bond_eq_flatFn`: the literal native class sum (`twistedRecenteredModCX` over
`canonFinsetK` of the start state), each member weighted by the bond weight of its own region, equals the weighted
flat observable `flatFnRMX` whose multiplier is the bond weight of the representative region. This generalizes
`VineSpaceK.twistedRecenteredModCX_upper_eq_flatFn` from `nodeWeight` at the top branch. -/

@[expose] public section
namespace WaveTurbulence.VineSpaceB
variable {kind : Bool}
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4
  VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4 VineSpaceK

variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem twistedRecenteredModCX_bond_eq_flat (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L z)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModCX G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
      (fun z => bW ψ κ0 z.1 z.2.U) κ0.L κ0.γ κ0.δ κ0.F κ0.base lam t0 t1 t2 e f g h =
    Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
      boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) *
      ((coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (Lvl.top B).region * clLocalZeta (Lvl.top B).region *
        lkRaw (Lvl.top B).region κ0.L κ0.base (spatialMul (lvW B RD hG layer hLayer ψ κ0 (Lvl.top B))
          (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime
            (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B)))) ![t0,t1,t2] ![e,f,g,h]) := by
  exact congrArg (fun z => Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) * z)
    (classSumB_eq_flat (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime
      (Lvl.top B) t0 t1 t2 e f g h)

theorem twistedRecenteredModCX_bond_eq_flatFn (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (hL : L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |F k (base + latticePoint L z)|) :
    (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) =>
      twistedRecenteredModCX G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        (fun z => bW ψ (kparOf L γ δ F base) z.1 z.2.U) L γ δ F base lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer
        (lvW B RD hG layer hLayer ψ (kparOf L γ δ F base) (Lvl.top B)) lam (G.sign a.toNode)
        (kparOf L γ δ F base) hprime (G.sign a.toNode) := by
  funext tt E
  have hh := twistedRecenteredModCX_bond_eq_flat (p := p) (kind := kind) B RD hG layer hLayer hprime lam ψ C hC hψ
    (kparOf L γ δ F base) hL hF (tt 0) (tt 1) (tt 2)
    (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
    (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at hh
  exact hh

end WaveTurbulence.VineSpaceB
