/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapKernel
/-! FLOWER-P7: the decapitation identity (summed form). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- The outer labels: the six root labels subject to the two outer constraints. -/
def OuterLabels (d : ℕ) : Type :=
  {n : Fin (2 * 3) → (Fin d → ℤ) // ∀ j : Fin 2, n (idx j 0) - n (idx j 1) + n (idx j 2) = 0}

/-- Decorations of the six trees with outer constraints, grouped by the root labels. -/
def decSigma (G : Garden (2 * 3)) (d : ℕ) : (Σ n : OuterLabels d, GenDecoration G d n.1 0) ≃ Dec6 G d where
  toFun x := ⟨x.2.1, x.2.2.1, fun j => by
      have h := x.1.2 j
      have e : ∀ c, x.2.1 (GNode.root G.tree c) = x.1.1 c := x.2.2.2.1
      simp only [e]
      exact h, x.2.2.2.2⟩
  invFun κ' := ⟨⟨rootLabels κ'.1, κ'.2.2.1⟩, ⟨κ'.1, κ'.2.1, fun _ => rfl, κ'.2.2.2⟩⟩
  left_inv x := by
    rcases x with ⟨⟨n, hn⟩, ⟨κv, hκ⟩⟩
    have hr : rootLabels κv = n := funext fun c => hκ.2.1 c
    subst hr
    rfl
  right_inv κ' := rfl

theorem capDec_val (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (d : ℕ)
    (κ : GenDecoration (capGarden G hsig) d (fun _ => 0) 0) :
    κ.1 = upperDec (T := G.tree) ((capDecEquiv G hsig d κ).1) :=
  (upper_lower κ.1 fun j => κ.2.2.1 j).symm

/-- The cap summand, as a function of the six-tree decoration. -/
noncomputable def capSummand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : Dec6 LG.garden d) : ℂ :=
  kgTerm L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
    (fun _ => t) k (upperDec (T := LG.garden.tree) κ'.1)

theorem capSummand_equiv (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0) :
    capSummand L γ δ F LG hsig p hp t k (capDecEquiv LG.garden hsig d κ) =
      kgTerm L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
        (fun _ => t) k κ.1 := by
  unfold capSummand
  rw [← capDec_val]

theorem capSummand_sigma (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (x : Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0) :
    capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d x) = outerWeight L γ δ k t x.1.1 *
      kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k x.2.1 := by
  unfold capSummand
  have e : (decSigma LG.garden d x).1 = x.2.1 := rfl
  rw [e, kgTerm_cap]
  have hr : (fun c => x.2.1 (GNode.root LG.garden.tree c)) = x.1.1 := funext fun c => x.2.2.2.1 c
  rw [hr]

theorem kernelKgen_cap (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hsum : Summable fun κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0 =>
      kgTerm L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
        (fun _ => t) k κ.1) :
    kernelKgen L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
        (fun _ => t) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * ∑' n : OuterLabels d,
        outerWeight L γ δ k t n.1 *
          kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
  rw [kernelKgen_eq_tsum]
  have hsum1 : Summable (capSummand L γ δ F LG hsig p hp t k) := by
    rw [← (capDecEquiv LG.garden hsig d).summable_iff]
    exact hsum.congr fun κ => (capSummand_equiv L γ δ F LG hsig p hp t k κ).symm
  have h1 : ∑' κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0,
      kgTerm L γ δ F (capLayered LG hsig p hp) (pinRoots (T := LG.garden.tree) t) ∅ (fun _ => 1)
        (fun _ => t) k κ.1 = ∑' κ' : Dec6 LG.garden d, capSummand L γ δ F LG hsig p hp t k κ' := by
    rw [← (capDecEquiv LG.garden hsig d).tsum_eq (capSummand L γ δ F LG hsig p hp t k)]
    exact tsum_congr fun κ => (capSummand_equiv L γ δ F LG hsig p hp t k κ).symm
  have hsum2 : Summable fun x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0) =>
      capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d x) :=
    (Equiv.summable_iff (decSigma LG.garden d) (f := capSummand L γ δ F LG hsig p hp t k)).2 hsum1
  have h2 : ∑' κ' : Dec6 LG.garden d, capSummand L γ δ F LG hsig p hp t k κ' =
      ∑' x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0),
        capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d x) :=
    ((decSigma LG.garden d).tsum_eq (capSummand L γ δ F LG hsig p hp t k)).symm
  rw [h1, h2, Summable.tsum_sigma hsum2]
  have h3 : ∀ n : OuterLabels d,
      ∑' κ : GenDecoration LG.garden d n.1 0,
        capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d ⟨n, κ⟩) =
      outerWeight L γ δ k t n.1 * ∑' κ : GenDecoration LG.garden d n.1 0,
        kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 := by
    intro n
    rw [← tsum_mul_left]
    exact tsum_congr fun κ => capSummand_sigma L γ δ F LG hsig p hp t k ⟨n, κ⟩
  simp only [h3]
  have hc : ∀ n : OuterLabels d, kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d n.1 0,
          kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 :=
    fun n => kernelKgen_eq_tsum ..
  simp only [hc]
  rw [order_cap, zeta_cap, pow_add, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

end WaveTurbulence.FlowerP7
