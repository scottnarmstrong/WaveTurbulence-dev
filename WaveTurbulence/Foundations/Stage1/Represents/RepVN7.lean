/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN3
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN6
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: a vine piece's outer form as a `RepIntC` (assembly of the modes)

`repIntC_vine_modes`: if the class sum of a vine piece has the INTERFACE v2 form
`Σ_i sgn_i Σ'_ξ (Π_s w_s(ξ_s)) outerValM(amp_ξ, frq_ξ, …, HkM_i)` over the modes `ξ` of the outer slot families
`fam i` (VINE-B♯ + VINE-C, `sum_tauClass_vineD_api`), the slot families carry the moments `Σ_l ⟨m_l/2⟩^θ w_l ≤ μ_{i,s}`
and, for every mode, the hinge side (`hhinge`: families `H`, masses `Mh`, with `Π_j Mh_j ≤ Kh_i Π_j (1+|λ_j|)^c`) is
available, then the value is a `RepIntC` of mass `Σ_i |sgn_i| B_i` with `Cχ^b ballCard^n Kh_i Π_s 9 μ_{i,s} ≤ B_i`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open scoped ENNReal

open scoped Classical in
theorem repIntC_vine_modes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1Piece P R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    {I : Type} [Fintype I] (sgn : I → ℂ) (fam : I → SlotFam π.Gsb P.d) (μ : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μ i s)
    (Kh : I → ℝ) (hKh : ∀ i, 0 ≤ Kh i)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp π tt base roots selSk hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : I → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hBi' : ∀ i, ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) * ∏ s, (9 * μ i s) ≤
        ENNReal.ofReal (Bi i)) :
    RepIntC π tt base roots
      (∑ i, sgn i * ∑' ξ : ∀ s, (fam i).Λ s, (((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ) *
        outerValM π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges (fun z => if selSk z then 1 else 0) hS
          (fun s => (fam i).a s (ξ s)) (fun s => (fam i).m s (ξ s)) route hclk hmom (HkM i))
      (∑ i, ‖sgn i‖ * Bi i) := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hKc0 : ∀ i, 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i := fun i => by
    have := hKh i; have := hCpos.le; positivity
  refine RepIntC.finset_sum Finset.univ _ _ (fun i _ => mul_nonneg (norm_nonneg _) (hBi i)) (fun i _ => ?_)
  refine RepIntC.smul ?_ (sgn i)
  have : ∀ s, Countable ((fam i).Λ s) := (fam i).cnt
  choose H Mh hMh hHk hMhb using hhinge i
  have hMh0 : ∀ ξ j, 0 ≤ Mh ξ j := fun ξ j => le_trans (tsum_nonneg fun l => (H ξ).w_nn j (fun _ _ => 0) l)
    (hMh ξ j (fun _ _ => 0))
  have hW : ∀ s l, 0 ≤ (fam i).w s l := (fam i).w_nn
  refine repIntC_modes hS hL0 _ _
    (fun ξ => Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh ξ j)
    (fun ξ => mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity))
      (Finset.prod_nonneg fun j _ => hMh0 ξ j))
    (fun ξ => repIntC_mode hd1 hL0 π hS tt base roots selSk hgsp (fun s => (fam i).a s (ξ s))
      (fun s => (fam i).n s (ξ s)) (fun s k => (fam i).a_one s _ k) (fun s => (fam i).a_snorm s _)
      (fun p k hk => (fam i).a_supp p _ k hk) (fun s => (fam i).m s (ξ s)) route hroute hclk hmom (HkM i)
      (H ξ) (Mh ξ) (hMh ξ) (hHk ξ) src src_dart src_root) (Bi i) (hBi i) ?_
  calc ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
        (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh ξ j))
      ≤ ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
        ((Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) *
          ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)) := by
        refine ENNReal.tsum_le_tsum fun ξ => ENNReal.ofReal_le_ofReal ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
            ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) := by have := hCpos.le; positivity
        calc _ ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
              ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
              (Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) :=
              mul_le_mul_of_nonneg_left (hMhb ξ) h0
          _ = _ := by ring
    _ ≤ ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) * ∏ s, (9 * μ i s) :=
        modes_mass_le route (fun s => (fam i).w s) hW (fun s => (fam i).m s) hc hc1 hcθ (μ i) (hμ i) _ (hKc0 i)
    _ ≤ _ := hBi' i

end WaveTurbulence.Represents
