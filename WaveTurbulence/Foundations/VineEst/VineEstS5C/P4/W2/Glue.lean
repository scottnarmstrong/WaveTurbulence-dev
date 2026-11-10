/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelFlat

/-! # P4-W2 (N1): the row form of a summand, and its gluing at a split

`RowForm R ψ Dm Qw Tw`: at every local decoration of the CL region `R = (U, a, b)` and for every clock `u`, the summand is
`ε_U(x) · 1_{Dm t u} · phase_U(x, u) · ∏_{pairs p of U} Qw p · ∏_{v ∈ U ∖ {a}} Tw v`, with arbitrary row weights `Qw`, `Tw` (functions of the
exterior clocks, the clock and the decoration) and an arbitrary time condition `Dm` (W2-D1: not the native domain in general).

* `rowForm_psiNat`: the native summand (`Dm` = `ClDom`, the native `qRow`/`tRow`).
* **`rowForm_step`**: the glue identity at a split `U = S ∪ T` (lower joint `b`): if `Ψ'` has a row form on `T`, then
  `x t u ↦ spartFrame(S, a, b, p₀)(rA x, u) · X(rA x, u) · Ψ'(rB x, (u b, t₁, t₂), u)` has a row form on `U`, with the frame rows of `S` at the
  ordinary pairs and branches, the whole exceptional factor `X` at the pair `p₀`, the weight `1` at the branch `b`, and the rows of `Ψ'` on
  `T`; time condition `DomF ∧ Dm'`.  Proof: `splitLocalEquiv` (every local decoration of `U` is glued), `eps_split`/`phase_split`,
  `eps_S_glue`/`eps_T_glue`/`phase_S_glue`/`phase_T_glue`, `split_pairs`/`split_interior` (VineEstS4.SplitSummand/SplitFactor).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory WaveTurbulence.VineEstS5C

variable {w d : ℕ} {G : Garden w}

/-- **The row form of a summand on a CL region.** -/
def RowForm (hG : G.IsPlain) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (L γ δ : ℝ)
    (base : Mom d) (ψ : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (Qw : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (Tw : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ) : Prop :=
  ∀ (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    ψ (clExtendIndices R κ.1) t u =
      (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
        ((open Classical in if Dm t u then (1 : ℂ) else 0) *
          (clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) u *
            ((∏ p ∈ clRegionalPairs hG U, Qw p t u (clExtendIndices R κ.1)) *
              ∏ v ∈ U.erase a, Tw v t u (clExtendIndices R κ.1))))

/-- **Base case**: the native summand has the row form with the native rows and the native time condition. -/
theorem rowForm_psiNat (D : ReconstructionData G) (hG : G.IsPlain) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) :
    RowForm hG R L γ δ base (psiNat D hG R L γ δ F layer hLayer base) (ClDom R fun v => layer (D.coreBranch hG v).toNode)
      (fun p t u x => qRow D hG L γ δ F layer hLayer base (t 0) x u p)
      (fun v t u x => tRow D hG L γ δ F layer hLayer base (t 0) x u v) := by
  classical
  intro β' κ t u
  unfold psiNat
  rw [starProd_eq_rows]
  split_ifs <;> simp

section Step
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)

theorem rA_glue (RS : CLRegionData G S a b) (xS xT : GNode G.tree → (Fin d → ℤ)) :
    rA RS (glue RS xS xT) = glue RS xS 0 := by
  funext y
  unfold rA glue
  by_cases hy : y ∈ splitA RS <;> simp [hy]

include hS hT hi hU in
theorem rB_glue (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) {base : Mom d}
    {xS : GNode G.tree → (Fin d → ℤ)} {β2 β3 : Mom d} (z : ↥(clLocalSupport RT) → (Fin d → ℤ))
    (hc : BdAt RT L base (bdT RT L base xS β2 β3) (clExtendIndices RT z)) :
    rB RT (glue RS xS (clExtendIndices RT z)) = clExtendIndices RT z := by
  conv_rhs => rw [← rB_ext RT z]
  funext y
  unfold rB
  by_cases hy : y ∈ clLocalSupport RT
  · simp only [hy, ite_true]
    exact glue_B hS hT hi hU RS RT hL hc hy
  · simp [hy]

include hS hT hi hU in
/-- **The glue identity at a split (N1).** -/
theorem rowForm_step (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (hL : L ≠ 0) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    (p0 : SourcePair G) (hp0 : p0 ∈ clRegionalPairs hG S) (hb : b ∈ S.erase a)
    (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (Ψ' : PsiT G d)
    {Dm' : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop}
    {Qw' : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    {Tw' : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (hΨ : RowForm hG RT L γ δ base Ψ' Dm' Qw' Tw') :
    open Classical in
    RowForm hG RU L γ δ base
      (fun x t u => spartFrame D hG L γ δ F layer hLayer base S a b p0 (rA RS x) u * X (rA RS x) u *
        Ψ' (rB RT x) ![u b, t 1, t 2] u)
      (fun t u => DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u ∧ Dm' ![u b, t 1, t 2] u)
      (fun p t u x => if p ∈ clRegionalPairs hG S then
          (if p = p0 then X (rA RS x) u else qRow D hG L γ δ F layer hLayer base (u a) (rA RS x) u p)
        else Qw' p ![u b, t 1, t 2] u (rB RT x))
      (fun v t u x => if v ∈ S.erase a then
          (if v = b then 1 else tRow D hG L γ δ F layer hLayer base (u a) (rA RS x) u v)
        else Tw' v ![u b, t 1, t 2] u (rB RT x)) := by
  classical
  intro βU κU t u
  -- every local decoration of `U` is glued from an upper-block decoration and a local decoration of `T`
  obtain ⟨q, rfl⟩ : ∃ q, κU = (splitLocalEquiv hS hT hi hU RU RS RT hL base βU).symm q :=
    ⟨splitLocalEquiv hS hT hi hU RU RS RT hL base βU κU, by simp⟩
  have hx := splitLocalEquiv_symm_val hS hT hi hU RU RS RT hL base βU q
  rw [hx]
  have hc : BdAt RT L base (bdT RT L base q.1.1 (βU 2) (βU 3)) (clExtendIndices RT q.2.1) := (clExtEquiv RT L base _ q.2).2.2
  have hrA : rA RS (glue RS q.1.1 (clExtendIndices RT q.2.1)) = glue RS q.1.1 0 := rA_glue RS q.1.1 (clExtendIndices RT q.2.1)
  have hrB : rB RT (glue RS q.1.1 (clExtendIndices RT q.2.1)) = (clExtendIndices RT q.2.1) := rB_glue hS hT hi hU RS RT hL q.2.1 hc
  have hIH := hΨ _ q.2 ![u b, t 1, t 2] u
  simp only [hrA, hrB]
  rw [hIH]
  -- ε and phase
  have heps : clRegionalEpsilon G (S ∪ T) (glue RS q.1.1 (clExtendIndices RT q.2.1)) =
      clRegionalEpsilon G (S.erase b) (glue RS q.1.1 0) * clRegionalEpsilon G T (clExtendIndices RT q.2.1) := by
    rw [eps_split hS hT hi hU, eps_S_glue hS hT hi hU RS q.1.1 (clExtendIndices RT q.2.1), eps_S_glue hS hT hi hU RS q.1.1 0,
      eps_T_glue hS hT hi hU RS RT hL hc]
  have hph : clRegionalPhase G (S ∪ T) L γ δ (cosetDecoration G L base (glue RS q.1.1 (clExtendIndices RT q.2.1))) u =
      clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base (glue RS q.1.1 0)) u *
        clRegionalPhase G T L γ δ (cosetDecoration G L base (clExtendIndices RT q.2.1)) u := by
    rw [phase_split hS hT hi hU, phase_S_glue hS hT hi hU L γ δ base RS q.1.1 (clExtendIndices RT q.2.1), phase_S_glue hS hT hi hU L γ δ base RS q.1.1 0,
      phase_T_glue hS hT hi hU L γ δ RS RT hL hc (fun _ _ => rfl)]
  -- the products over the pairs and branches of `U`
  have hpairs : ∀ f : SourcePair G → ℂ, ∏ p ∈ clRegionalPairs hG (S ∪ T), f p =
      (∏ p ∈ clRegionalPairs hG S, f p) * ∏ p ∈ clRegionalPairs hG T, f p := fun f => by
    rw [split_pairs hS hT hi hU hG, Finset.prod_union (split_pairs_disjoint hS hT hi hU hG)]
  have hbr : ∀ f : GBranch G.tree → ℂ, ∏ v ∈ (S ∪ T).erase a, f v = (∏ v ∈ S.erase a, f v) * ∏ v ∈ T.erase b, f v :=
    fun f => by rw [split_interior hS hT hi hU, Finset.prod_union (split_interior_disjoint hS hT hi hU)]
  have hQS : ∏ p ∈ clRegionalPairs hG S, (if p ∈ clRegionalPairs hG S then
        (if p = p0 then X (glue RS q.1.1 0) u else qRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u p)
      else Qw' p ![u b, t 1, t 2] u (clExtendIndices RT q.2.1)) =
      X (glue RS q.1.1 0) u * ∏ p ∈ (clRegionalPairs hG S).erase p0,
        qRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u p := by
    rw [← Finset.mul_prod_erase _ _ hp0, if_pos hp0, if_pos rfl]
    refine congrArg _ (Finset.prod_congr rfl fun p hp => ?_)
    rw [if_pos (Finset.mem_of_mem_erase hp), if_neg (Finset.ne_of_mem_erase hp)]
  have hQT : ∏ p ∈ clRegionalPairs hG T, (if p ∈ clRegionalPairs hG S then
        (if p = p0 then X (glue RS q.1.1 0) u else qRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u p)
      else Qw' p ![u b, t 1, t 2] u (clExtendIndices RT q.2.1)) = ∏ p ∈ clRegionalPairs hG T, Qw' p ![u b, t 1, t 2] u (clExtendIndices RT q.2.1) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [if_neg (Finset.disjoint_right.mp (split_pairs_disjoint hS hT hi hU hG) hp)]
  have hTS : ∏ v ∈ S.erase a, (if v ∈ S.erase a then
        (if v = b then 1 else tRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u v)
      else Tw' v ![u b, t 1, t 2] u (clExtendIndices RT q.2.1)) =
      ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u v := by
    rw [← Finset.mul_prod_erase _ _ hb, if_pos hb, if_pos rfl, one_mul]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_pos (Finset.mem_of_mem_erase hv), if_neg (Finset.ne_of_mem_erase hv)]
  have hTT : ∏ v ∈ T.erase b, (if v ∈ S.erase a then
        (if v = b then 1 else tRow D hG L γ δ F layer hLayer base (u a) (glue RS q.1.1 0) u v)
      else Tw' v ![u b, t 1, t 2] u (clExtendIndices RT q.2.1)) = ∏ v ∈ T.erase b, Tw' v ![u b, t 1, t 2] u (clExtendIndices RT q.2.1) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_neg (Finset.disjoint_right.mp (split_interior_disjoint hS hT hi hU) hv)]
  rw [heps, hph, hpairs, hbr, hQS, hQT, hTS, hTT]
  unfold spartFrame
  by_cases h1 : DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u <;>
    by_cases h2 : Dm' ![u b, t 1, t 2] u <;> simp only [h1, h2, if_true, if_false, and_true, and_false, true_and,
      false_and] <;> push_cast <;> ring

end Step

end WaveTurbulence.VineEstS5C.P4.W2
