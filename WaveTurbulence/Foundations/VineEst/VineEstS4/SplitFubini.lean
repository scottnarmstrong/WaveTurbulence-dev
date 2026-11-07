/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitLocal
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitKernel

/-! # Fubini form of the splitting of `K^U` at the joint `b` (V5 Step 4b, P2.3, TARGET (tildeJ2) before the twist sum)

`fU` is the summand of `K^U` at a glued decoration `(xS, κ)`.  Assuming its absolute convergence
(`AbsConv`: every `fU p` integrable and `∑_p ∫‖fU p‖ < ∞`), `clLocalKernel_split_fubini` separates the factors:
`K^U = coupling^{n₁(S)} ζ_S ∑_{xS} ∫_{σ ∈ times(S)} spart(xS, σ) · K^T(σ_b, t₁, t₂; E(xS), F(xS), g, h) dσ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- The kernel of `T` for an arbitrary boundary vector `β` and exterior clocks `t`. -/
@[expose] noncomputable def clLocalKernelVec (D : ReconstructionData G) (hG : G.IsPlain) (RT : CLRegionData G T b c)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (base : Mom d) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT *
    ∑' κ : CLLocalDecoration RT L base β, ∫ τ : CLInternalTime RT,
      clLocalSummand D hG RT L γ δ F layer hLayer base β t κ τ

theorem clLocalKernel_eq_vec (D : ReconstructionData G) (hG : G.IsPlain) (RT : CLRegionData G T b c)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (base : Mom d) (tU tP tN : ℝ) (e f g h : Mom d) :
    clLocalKernel D hG RT L γ δ F layer hLayer base tU tP tN e f g h =
      clLocalKernelVec D hG RT L γ δ F layer hLayer base ![e, f, g, h] ![tU, tP, tN] := rfl

instance countable_CLLocalDecoration {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d) :
    Countable (CLLocalDecoration R L base boundary) := by
  unfold CLLocalDecoration
  infer_instance

section Fubini
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

/-- The summand of `K^U` at the glued decoration `(xS, κ)`, as in `clLocalKernel_split_sigma`. -/
@[expose] noncomputable def fU
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (τ : CLInternalTime RU) : ℂ :=
  spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RU ![t0, t1, t2] τ) *
    clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
      (tT b RU ![t0, t1, t2] τ) p.2 (restrT hS hT hi hU RU RT τ)

/-- Absolute convergence of the glued summands: each is integrable and the integrals of the norms are summable. -/
@[expose] def AbsConv : Prop :=
  (∀ p, Integrable (fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p)) ∧
    Summable (fun p => ∫ τ, ‖fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ‖)

include hS hT hi hU in
/-- The glued summand in product coordinates `(σ, ρ)` of the times of `S` and `T`. -/
theorem exists_prodForm :
    ∃ E : (CLInternalTime RS × CLInternalTime RT) ≃ᵐ CLInternalTime RU, MeasurePreserving E volume volume ∧
      ∀ p σ ρ, fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p (E (σ, ρ)) =
        spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
            ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] p.2 ρ := by
  obtain ⟨E, hE, hl, hr⟩ := exists_timeSplit (clInteriorBranches RU) (S.erase a) (T.erase b)
    (split_interior hS hT hi hU) (split_interior_disjoint hS hT hi hU)
  refine ⟨E, hE, fun p σ ρ => ?_⟩
  have hclock : ∀ v ∈ S, clLocalClock RU ![t0, t1, t2] (E (σ, ρ)) v = clLocalClock RS ![t0, t1, t2] σ v := by
    intro v hv
    by_cases hva : v = a
    · subst hva
      rw [clLocalClock_upper, clLocalClock_upper]
    · have hv' : v ∈ S.erase a := Finset.mem_erase.mpr ⟨hva, hv⟩
      have h1 := clLocalClock_internal RU ![t0, t1, t2] (E (σ, ρ)) ⟨v, mem_interior_of_S hS hT hi hU hv'⟩
      have h2 := clLocalClock_internal RS ![t0, t1, t2] σ ⟨v, hv'⟩
      rw [h1, h2]
      exact hl σ ρ v hv'
  have hrestr : restrT hS hT hi hU RU RT (E (σ, ρ)) = ρ := by
    funext v
    exact hr σ ρ v.1 v.2
  have htT : tT b RU ![t0, t1, t2] (E (σ, ρ)) = ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] := by
    unfold tT
    rw [hclock b hS.2.2.1]
    rfl
  unfold fU
  have e1 := spart_congr D hG L γ δ F layer hLayer base hS RS p.1.1 hclock
  have e2 : clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
      (tT b RU ![t0, t1, t2] (E (σ, ρ))) p.2 (restrT hS hT hi hU RU RT (E (σ, ρ))) =
      clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
        ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] p.2 ρ := by
    rw [hrestr, htT]
  exact congrArg₂ (· * ·) e1 e2

/-- The time-`b` kernel integrand of `T`, integrated over the times of `T`. -/
@[expose] noncomputable def JT
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (u : ℝ) : ℂ :=
  ∫ ρ : CLInternalTime RT, clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
    ![u, t1, t2] p.2 ρ

/-- The separated integrand over the times of `S`. -/
@[expose] noncomputable def PhiS
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (σ : CLInternalTime RS) : ℂ :=
  spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
    JT RS RT D hG L γ δ F layer hLayer base t1 t2 e f g h p (clLocalClock RS ![t0, t1, t2] σ b)

include hS hT hi hU in
/-- Fubini for one glued summand. -/
theorem fubini_one
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (hp : Integrable (fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p)) :
    Integrable (PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p) ∧
      ∫ τ, fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ =
        ∫ σ, PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ ∧
      ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ‖ ≤
        ∫ τ, ‖fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ‖ := by
  obtain ⟨E, hE, hf⟩ := exists_prodForm hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h
  set f' := fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p with hf'
  have hg : Integrable (f' ∘ E) := (hE.integrable_comp_emb E.measurableEmbedding).mpr hp
  have hrow : ∀ σ, ∫ ρ, (f' ∘ E) (σ, ρ) = PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ := by
    intro σ
    simp only [Function.comp, hf' , hf p σ]
    unfold PhiS JT
    rw [integral_const_mul]
  have h1 : Integrable (PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p) := by
    have := hg.integral_prod_left
    simpa only [hrow] using this
  refine ⟨h1, ?_, ?_⟩
  · rw [← hE.integral_comp' f']
    change ∫ z, (f' ∘ E) z = _
    exact (integral_prod _ hg).trans (integral_congr_ae (Filter.Eventually.of_forall hrow))
  · have hn : Integrable (fun σ => ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖) := hg.norm.integral_prod_left
    calc ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ‖
        ≤ ∫ σ, ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖ := by
          refine integral_mono h1.norm hn (fun σ => ?_)
          rw [← hrow σ]
          exact norm_integral_le_integral_norm _
      _ = ∫ z, ‖(f' ∘ E) z‖ := (integral_prod _ hg.norm).symm
      _ = ∫ τ, ‖f' τ‖ := hE.integral_comp' (fun τ => ‖f' τ‖)

include hS hT hi hU in
/-- **Fubini form (TARGET (tildeJ2), before the twist sum).**  Under absolute convergence of the glued summands,
`K^U = coupling^{n₁(U)} ζ_U ∑'_{xS} ∫_σ spart(xS,σ) · (∑'_κ J^T(σ_b))`, the inner sum being `K^T` up to its constants. -/
theorem clLocalKernel_split_fubini (hL : L ≠ 0)
    (hA : AbsConv hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h) :
    clLocalKernel D hG RU L γ δ F layer hLayer base t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RU * clLocalZeta RU *
        ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
              JT RS RT D hG L γ δ F layer hLayer base t1 t2 e f g h ⟨xS, κ⟩ (clLocalClock RS ![t0, t1, t2] σ b) := by
  rw [clLocalKernel_split_sigma hS hT hi hU RU RS RT D hG hL γ δ F layer hLayer base t0 t1 t2 e f g h]
  congr 1
  obtain ⟨hint, hsum⟩ := hA
  have hone := fun p => fubini_one hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p (hint p)
  -- the sigma sum of the integrals of fU equals that of PhiS
  have h1 : ∀ p, ∫ τ, fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ =
      ∫ σ, PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ := fun p => (hone p).2.1
  have hsP : Summable (fun p => ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  have hsI : Summable (fun p => ∫ σ, PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ) :=
    Summable.of_norm_bounded hsP (fun p => norm_integral_le_integral_norm _)
  change ∑' p, ∫ τ, fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ = _
  simp_rw [h1]
  rw [hsI.tsum_sigma' (fun xS => hsI.sigma_factor xS)]
  refine tsum_congr (fun xS => ?_)
  have hsκ : Summable (fun κ => ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖) :=
    hsP.sigma_factor xS
  have := hasSum_integral_of_summable_integral_norm (fun κ => (hone ⟨xS, κ⟩).1) hsκ
  rw [this.tsum_eq]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun σ => by simp only [PhiS]; exact tsum_mul_left))

end Fubini

end WaveTurbulence.VineEstS4
