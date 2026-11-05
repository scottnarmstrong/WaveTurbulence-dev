/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftSigns
public import WaveTurbulence.Foundations.XChain.GraftEpsilon
public import WaveTurbulence.Foundations.XChain.GraftTimeSplit
/-! The exact phase-product factorization, without restrictions on the top-tree family. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem markedGardenGraft_phaseProd {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode (graftForest top (blockGraftTrees top P low)) → Mom d)
    (τ : GBranch (graftForest top (blockGraftTrees top P low)) → ℝ) :
    phaseProd L γ δ (markedGardenGraft sig top P low hsig) k τ =
      (∏ b : GBranch top, Complex.exp ((Real.pi * ((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) * δ *
        L ^ (2 * γ) *
        resFactor (k (topNodeEmbedding top P low (b.child 0)))
          (k (topNodeEmbedding top P low (b.child 1)))
          (k (topNodeEmbedding top P low (b.child 2)))
          (k (topNodeEmbedding top P low b.toNode)) *
        (graftTimeSplit top P low τ).1 b : ℝ) * Complex.I)) *
      ∏ B : P.parts, phaseProd L γ δ (low B)
        (fun a => k (lowerNodeEmbedding top P low B a))
        (fun b => (graftTimeSplit top P low τ).2 ⟨B, b⟩) := by
  let G := markedGardenGraft sig top P low hsig
  have he := prod_graft_branches top P low (fun b => Complex.exp
    ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      omegaNode G k b * τ b : ℝ) * Complex.I))
  have ht := Finset.prod_congr (s₁ := (univ : Finset (GBranch top))) rfl (fun b _ =>
    congrArg₂ (fun (ζ : ℤˣ) (ω : ℝ) => Complex.exp ((Real.pi * (ζ : ℤ) * δ *
      L ^ (2 * γ) * ω * τ (gardenBranchEquiv top P low (.inl b)) : ℝ) * Complex.I))
      (gardenBranchEquiv_top_sign sig top P low b)
      (markedGardenGraft_omega_top sig top P low hsig k b))
  have hl := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ =>
    Finset.prod_congr (s₁ := (univ : Finset (GBranch (low B).tree))) rfl (fun b _ =>
      congrArg₂ (fun (ζ : ℤˣ) (ω : ℝ) => Complex.exp ((Real.pi * (ζ : ℤ) * δ *
        L ^ (2 * γ) * ω * τ (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) : ℝ) * Complex.I))
        (gardenBranchEquiv_lower_sign sig top P low hsig B b)
        (markedGardenGraft_omega_lower sig top P low hsig k B b)))
  exact he.trans (congrArg₂ (· * ·) ht hl)

end WaveTurbulence.Induct
