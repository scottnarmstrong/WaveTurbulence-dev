/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Defs
public import WaveTurbulence.Foundations.Flower.Fam.Prof2
public import WaveTurbulence.Foundations.FC23.FrozenRadialBridge
public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite

/-! # A1 MK-DEFS: bounds and scaling of the marked weight.

* `abs_markedWeight_le`: `|markedWeight| ≤ b ^ #(non-cap input leaves) * ∏_j (selected ? Cχ |R_j|⁻¹ : 1)` when the
  profiles are pointwise bounded by `b` (and the garden layers are at most `p`).
* `leafProdCap_scale`, `markedWeight_scale`: the scaling identity `leafProdCap h = b ^ n leafProdCap (h / b)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

theorem chi0_eq_fourier : (chi0 : ℝ → ℝ) = Fourier.chi0 := funext FC23.frozen_chi0_eq

theorem abs_chi0_le_one (x : ℝ) : |chi0 x| ≤ 1 := by
  rw [FC23.frozen_chi0_eq, abs_of_nonneg (Fourier.chi0_nonneg x)]
  exact Fourier.chi0_le_one x

theorem exists_chiD_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |chiD u| ≤ C := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) Fourier.chi0 := Fourier.chi0_contDiff
  have hder : Continuous (deriv Fourier.chi0) := hcd.continuous_deriv (by simp)
  have hsupp : HasCompactSupport (deriv Fourier.chi0) := Fourier.chi0_hasCompactSupport.deriv
  have hg : Continuous fun u : ℝ => -u * deriv Fourier.chi0 u := by fun_prop
  have hgs : HasCompactSupport fun u : ℝ => -u * deriv Fourier.chi0 u :=
    hsupp.mul_left
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  have := hC u
  rw [Real.norm_eq_abs] at this
  unfold chiD
  rw [chi0_eq_fourier]
  exact this.trans (le_max_left _ _)

/-- A fixed bound for `chiD = -u χ₀'(u)` (an absolute constant). -/
def chiDConst : ℝ := Classical.choose exists_chiD_bound

theorem chiDConst_nonneg : 0 ≤ chiDConst := (Classical.choose_spec exists_chiD_bound).1

theorem abs_chiD_le (u : ℝ) : |chiD u| ≤ chiDConst := (Classical.choose_spec exists_chiD_bound).2 u

theorem abs_stemFilterCap_le_one {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ)
    (σ : Fin w → Option ℕ) (k : GNode LG.garden.tree → Mom d) : |stemFilterCap LG J L σ k| ≤ 1 := by
  unfold stemFilterCap
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  cases σ j with
  | none => simp
  | some i => exact XChain.ProductCut.abs_prodDyadicCut_le_one _ _ _ _

theorem abs_sibWeightCap_le_one {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (c : Fin w → Fin 3 → Mom d) (k : GNode LG.garden.tree → Mom d) : |sibWeightCap LG J c k| ≤ 1 := by
  unfold sibWeightCap
  have h0 : 0 ≤ ∏ b : GBranch LG.garden.tree, if IsCapFlowerParent LG J b then
      ∏ i : Fin 3, (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = b.child i) then (1 : ℝ) else
        if k (b.child i) = c b.1.1 i then 1 else 0) else 1 := by
    refine Finset.prod_nonneg fun b _ => ?_
    split_ifs
    · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
    · norm_num
  rw [abs_of_nonneg h0]
  refine Finset.prod_le_one₀ (fun b _ => ?_) fun b _ => ?_
  · split_ifs
    · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
    · norm_num
  · split_ifs
    · exact Finset.prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) (fun i _ => by split_ifs <;> norm_num)
    · exact le_refl _

theorem abs_selWeightCap_le {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (v : Fin w → Option (GBranch LG.garden.tree)) (Rs : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    |selWeightCap LG J v Rs k| ≤ ∏ j : Fin w, (if (v j).isSome then chiDConst * |Rs j|⁻¹ else 1) := by
  unfold selWeightCap
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  cases hv : v j with
  | none => simp
  | some vj =>
    simp only [Option.elim, Option.isSome_some, if_true]
    rw [abs_mul, abs_mul, abs_inv, Finset.abs_prod]
    have hprod : ∏ b ∈ (stemSetCap LG J j).erase vj, |chi0 (|omegaNode LG.garden k b| / Rs j)| ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_chi0_le_one _
    have h1 : |chiD (|omegaNode LG.garden k vj| / Rs j)| ≤ chiDConst := abs_chiD_le _
    calc |Rs j|⁻¹ * |chiD (|omegaNode LG.garden k vj| / Rs j)| *
          ∏ b ∈ (stemSetCap LG J j).erase vj, |chi0 (|omegaNode LG.garden k b| / Rs j)|
        ≤ |Rs j|⁻¹ * chiDConst * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hprod
            (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity [chiDConst_nonneg])
      _ = chiDConst * |Rs j|⁻¹ := by ring

/-- The non-cap input leaves: the leaves whose pair-type profile is not replaced by `1`. -/
def nonCapLeaves (LG : LayeredGarden w) (J : Finset (Fin w)) : Finset (GLeaf LG.garden.tree) :=
  (inputLeaves LG.garden).filter fun ℓ => ¬ (ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J)

theorem abs_typeProfiles_le {d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ)
    (b : ℝ) (hb : 0 ≤ b) (hh : ∀ q ≤ p, ∀ j j' x, |h q j j' x| ≤ b) (hlay : ∀ a, LG.layer a ≤ p)
    (a : Fin w × TTree.Path) (x : Mom d) : |LGSpine.typeProfiles LG h a x| ≤ b := by
  unfold LGSpine.typeProfiles
  split_ifs with hn
  · exact hh _ (hlay _) _ _ _
  · simpa using hb

theorem abs_leafProdCap_le {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hh : ∀ q ≤ p, ∀ j j' x, |h q j j' x| ≤ b) (hlay : ∀ a, LG.layer a ≤ p)
    (k : GNode LG.garden.tree → Mom d) :
    |leafProdCap LG J h k| ≤ b ^ (nonCapLeaves LG J).card := by
  unfold leafProdCap
  rw [Finset.abs_prod]
  have e : b ^ (nonCapLeaves LG J).card =
      ∏ ℓ ∈ inputLeaves LG.garden, (if ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J then (1 : ℝ) else b) := by
    unfold nonCapLeaves
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [e]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ℓ _ => ?_
  split_ifs
  · simp
  · exact abs_typeProfiles_le LG h p b hb hh hlay _ _

/-- The scaling identity: `leafProdCap h = b ^ #(non-cap input leaves) · leafProdCap (h / b)` (`b ≠ 0`). -/
theorem leafProdCap_scale {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (b : ℝ) (hb : b ≠ 0) (k : GNode LG.garden.tree → Mom d) :
    leafProdCap LG J h k =
      b ^ (nonCapLeaves LG J).card *
        leafProdCap LG J (fun q j j' x => h q j j' x / b) k := by
  unfold leafProdCap
  have e : b ^ (nonCapLeaves LG J).card =
      ∏ ℓ ∈ inputLeaves LG.garden, (if ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J then (1 : ℝ) else b) := by
    unfold nonCapLeaves
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [e, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  split_ifs
  · simp
  · unfold LGSpine.typeProfiles
    split_ifs with hn
    · field_simp
    · simp

/-- Pointwise bound of the profiles from `SNormR` (the zeroth-order term; `0 ≤ b`). -/
theorem abs_le_of_SNormR_le {d : ℕ} (Λ₁ Λ₂ : ℕ) (F : Mom d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hF : SNormR Λ₁ Λ₂ F ≤ ENNReal.ofReal b) (x : Mom d) : |F x| ≤ b := by
  unfold SNormR SNorm at hF
  split_ifs at hF with hc
  · have h0 := (le_iSup₂_of_le (f := fun (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁) =>
        ⨆ k : Mom d, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (fun k => (F k : ℂ)) k‖))
      (fun _ => 0) (by simp) (le_refl _)).trans hF
    have h1 := (le_iSup_of_le x (le_refl _)).trans h0
    have hit : iterPartial (fun _ : Fin d => 0) (fun k => (F k : ℂ)) x = (F x : ℂ) := by
      simp [iterPartial]
    rw [hit, ENNReal.ofReal_le_ofReal_iff hb] at h1
    have hj : 1 ≤ jbr x ^ Λ₂ := one_le_pow₀ (by
      unfold jbr; rw [Real.le_sqrt' one_pos]; nlinarith [norm_nonneg x])
    have : |F x| ≤ jbr x ^ Λ₂ * ‖(F x : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      nlinarith [abs_nonneg (F x)]
    linarith
  · simp at hF

end WaveTurbulence.Flower.MkDefs
