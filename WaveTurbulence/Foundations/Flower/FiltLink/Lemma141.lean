/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Filters
public import WaveTurbulence.Foundations.IncohInst.Links.Omega
/-! # D5a FILT-LINK: o82 Lemma 14.1 for the two filter layers of one link (exports)

A link of main's incoherent chain joins two branching nodes `b, b'` (branch set `E`, `#E ≤ 2`). On a decoration,
`Ω_b = 2⟨x_b, y_b⟩` and `ζ_{b'}Ω_{b'} = −ζ_bΩ_b` (IncohInst `omegaNode_eq`, `zeta_omega_link`), so every factor of
`filtWeight F ann M * filtWeight Fu false Mu` (ProtDefs; SCOPE F-D0-9: two layers, any `ann`) on a branch of `E` is a
function of the link's `|2⟨x, y⟩|`. Their product is `linkFiltWeight E F Fu ann M Mu`, at most four factors.

Exports:
- `exists_filtLink_decay`: **o82 Lemma 14.1, (14.1)**, the pair mass, in the exact form of main's
  `Incoh.exists_oneLink_decay` (same quantifiers, same right-hand side), for `filtLayerLinkMass … (linkFiltWeight …)`,
  uniformly in the branch sets, flags and scales `M, Mu ≥ L`;
- `exists_filtLink_trivial`: the sup bound (o82 §15 "the trivial supremum remains `C L^{2d}`"): `B (5L)^{2d}` for
  the filtered lattice sum, the filtered phase-coefficient mass, and the filtered mass (main's `(5L)^{2d}` of
  `replacedLinkMass`/`RootEnvelope`, times a fixed `B`);
- `presentedMult_linkFiltWeight`: **(14.2)**, the moment presentation (`K = filtMomentConst⁴`);
- the decoration bridge: `filtFactor_eq_link`, `prod_filtFactor_eq_linkFiltMult`, `prod_filtFactor_two_eq`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

/-- **The two-layer filter multiplier of one link** with branch set `E`, at bilinear frequency `u`: the factors of
`filtWeight F ann M` and `filtWeight Fu false Mu` on the branches of `E`, at `|Ω| = |2u|`. -/
def linkFiltWeight {ι : Type*} [DecidableEq ι] (E F Fu : Finset ι) (ann : ι → Bool) (M Mu : ι → ℝ) (u : ℝ) : ℂ :=
  linkFiltMult (F ∩ E) ann M u * linkFiltMult (Fu ∩ E) (fun _ => false) Mu u

/-- **o82 (14.2)** for one link: the two-layer multiplier is `filtMomentConst⁴`-presented at scale `L ≤ M, Mu`. -/
theorem presentedMult_linkFiltWeight {ι : Type*} [DecidableEq ι] (E F Fu : Finset ι) (ann : ι → Bool) (M Mu : ι → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hE : E.card ≤ 2) (hM : ∀ b ∈ F, L ≤ M b) (hMu : ∀ b ∈ Fu, L ≤ Mu b) :
    PresentedMult L (filtMomentConst ^ 4) (linkFiltWeight E F Fu ann M Mu) := by
  have h1 := presentedMult_linkFiltMult (F ∩ E) ann M hL fun b hb => hM b (Finset.mem_inter.mp hb).1
  have h2 := presentedMult_linkFiltMult (Fu ∩ E) (fun _ => false) Mu hL
    fun b hb => hMu b (Finset.mem_inter.mp hb).1
  refine (presentedMult_mul hL (by positivity [one_le_filtMomentConst]) h1 h2).mono ?_
  rw [← pow_add]
  apply pow_le_pow_right₀ one_le_filtMomentConst
  have := Finset.card_le_card (Finset.inter_subset_right (s₁ := F) (s₂ := E))
  have := Finset.card_le_card (Finset.inter_subset_right (s₁ := Fu) (s₂ := E))
  omega

/-- The sup bound of the two-layer multiplier of one link. -/
theorem exists_linkFiltWeight_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ {ι : Type*} [DecidableEq ι] (E F Fu : Finset ι) (ann : ι → Bool)
    (M Mu : ι → ℝ), E.card ≤ 2 → ∀ u, ‖linkFiltWeight E F Fu ann M Mu u‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_filtProf_bound
  refine ⟨B ^ 4, one_le_pow₀ hB, fun E F Fu ann M Mu hE u => ?_⟩
  unfold linkFiltWeight
  rw [norm_mul]
  have h1 := norm_linkFiltMult_le (F ∩ E) ann M hb u
  have h2 := norm_linkFiltMult_le (Fu ∩ E) (fun _ => false) Mu hb u
  have hc1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := F) (s₂ := E))
  have hc2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Fu) (s₂ := E))
  calc
    _ ≤ B ^ (F ∩ E).card * B ^ (Fu ∩ E).card := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = B ^ ((F ∩ E).card + (Fu ∩ E).card) := (pow_add _ _ _).symm
    _ ≤ B ^ 4 := pow_le_pow_right₀ hB (by omega)

/-! ### The decoration bridge: branch filters are link-frequency filters -/

section Bridge

variable {w d : ℕ} {G : Garden w}

/-- Linked branches have the same `|Ω|`: from `ζ_{b'}Ω_{b'} = −ζ_bΩ_b` (`zeta_omega_link`, `TreeLinks`). -/
theorem abs_omega_eq_of_signed {κ : GNode G.tree → Mom d} {b b' : GBranch G.tree}
    (h : ((G.sign b'.toNode : ℤ) : ℝ) * omegaNode G κ b' = -(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G κ b)) :
    |omegaNode G κ b'| = |omegaNode G κ b| := by
  have hu (s : ℤˣ) : |((s : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> norm_num
  have h2 := congrArg abs h
  rwa [abs_neg, abs_mul, abs_mul, hu, hu, one_mul, one_mul] at h2

/-- **The filters of a link block are its link multiplier**: if every branch of `E` has `|Ω| = |2u|`, the
`filtWeight`-type product over `F ∩ E` is `linkFiltMult (F ∩ E) ann M u`. -/
theorem prod_filtFactor_eq_linkFiltMult {κ : GNode G.tree → Mom d} (E F : Finset (GBranch G.tree))
    (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ) (u : ℝ)
    (hE : ∀ b ∈ E, |omegaNode G κ b| = |2 * u|) :
    (∏ b ∈ F ∩ E, (((if ann b then FlShell.chiD else chi0) (|omegaNode G κ b| / M b) : ℝ) : ℂ)) =
      linkFiltMult (F ∩ E) ann M u := by
  unfold linkFiltMult filtProf
  apply Finset.prod_congr rfl
  intro b hb
  rw [hE b (Finset.mem_inter.mp hb).2]

/-- The two filter layers on a link block are `linkFiltWeight`. -/
theorem prod_filtFactor_two_eq {κ : GNode G.tree → Mom d} (E F Fu : Finset (GBranch G.tree))
    (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (u : ℝ)
    (hE : ∀ b ∈ E, |omegaNode G κ b| = |2 * u|) :
    (∏ b ∈ F ∩ E, (((if ann b then FlShell.chiD else chi0) (|omegaNode G κ b| / M b) : ℝ) : ℂ)) *
      (∏ b ∈ Fu ∩ E, (((if (fun _ => false) b then FlShell.chiD else chi0)
        (|omegaNode G κ b| / Mu b) : ℝ) : ℂ)) =
      linkFiltWeight E F Fu ann M Mu u := by
  rw [prod_filtFactor_eq_linkFiltMult E F ann M u hE,
    prod_filtFactor_eq_linkFiltMult E Fu (fun _ => false) Mu u hE]
  rfl

/-- **Link factorization of a filter product**: if the filtered branches are covered by pairwise disjoint link
blocks `E j`, `j ∈ J`, the product over `F` is the product over the links of the block products. -/
theorem prod_filtFactor_eq_prod_blocks {ι : Type*} (κ : GNode G.tree → Mom d) (F : Finset (GBranch G.tree))
    (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ) (J : Finset ι) (E : ι → Finset (GBranch G.tree))
    (hdisj : (J : Set ι).PairwiseDisjoint E) (hcov : F ⊆ J.biUnion E) :
    (∏ b ∈ F, (((if ann b then FlShell.chiD else chi0) (|omegaNode G κ b| / M b) : ℝ) : ℂ)) =
      ∏ j ∈ J, ∏ b ∈ F ∩ E j, (((if ann b then FlShell.chiD else chi0) (|omegaNode G κ b| / M b) : ℝ) : ℂ) := by
  classical
  have hF : F = J.biUnion (fun j => F ∩ E j) := by
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hb
      obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp (hcov hb)
      exact ⟨j, hj, hb, hbj⟩
    · rintro ⟨j, _, hb, _⟩
      exact hb
  conv_lhs => rw [hF]
  exact Finset.prod_biUnion fun i hi j hj hij =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj hi hj hij))

end Bridge

end WaveTurbulence.Flower.FiltLink
