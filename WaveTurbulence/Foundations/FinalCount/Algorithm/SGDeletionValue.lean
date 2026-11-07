/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGLocalChoices
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGDeletionGraph
public import WaveTurbulence.Foundations.FinalCount.AppBGoodNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBGoodDeletionTransfer
import Mathlib.Tactic

/-! # The trivial deletion bound for the small-gap preprocessing

Deleting a set `Y` of atoms costs at most the box count `⌈2L+1⌉^(d·#removed bonds)` for the
local labels and `(log L)^(4|Y|)` for the vanished links; the circuit rank never rises, so
the normalising factor only improves (DH23 L1834, the trivial bound used for the SG atoms).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_trivial_normalization (Epre Epos : ℝ≥0∞) (χ : ℤ) (r b : ℕ)
    (L D' B Hpre Hpos N : ℝ) (hL : 1 ≤ L) (hD : 0 ≤ D') (hB : 0 < B) (hB1 : B ≤ 1) (hN : 0 ≤ N) (hH : 0 ≤ Hpre)
    (hlinks : Hpre ≤ (Real.log L)^b*Hpos) (hE : Epre ≤ ENNReal.ofReal N*Epos) :
    Epre*ENNReal.ofReal (L^(-D'*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre) ≤
      ENNReal.ofReal (N*(Real.log L)^b)*(Epos*ENNReal.ofReal (L^(-D'*(χ : ℝ))*B^χ*Hpos)) := by
  have hLp := zero_lt_one.trans_le hL
  have hlog := Real.log_nonneg hL
  have hbase : 0 ≤ L^(-D'*(χ : ℝ))*B^χ := by positivity
  have hstep : 0 ≤ L^(-D'*(r : ℝ))*B^r := by positivity
  have hstep1 : L^(-D'*(r : ℝ))*B^r ≤ 1 := by
    have h1 : L^(-D'*(r : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith only [hD,(Nat.cast_nonneg r : (0:ℝ) ≤ r)])
    calc _ ≤ 1*1 := mul_le_mul h1 (pow_le_one₀ hB.le hB1) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpre : L^(-D'*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre ≤
      ((Real.log L)^b)*(L^(-D'*(χ : ℝ))*B^χ*Hpos) := by
    rw [appb_normalization_step_nat χ r L D' B Hpre hLp hB.ne']
    calc (L^(-D'*(r : ℝ))*B^r)*(L^(-D'*(χ : ℝ))*B^χ*Hpre)
        ≤ 1*(L^(-D'*(χ : ℝ))*B^χ*Hpre) := by
          apply mul_le_mul_of_nonneg_right hstep1
          exact mul_nonneg hbase hH
      _ ≤ _ := by
          rw [one_mul]
          calc L^(-D'*(χ : ℝ))*B^χ*Hpre ≤ L^(-D'*(χ : ℝ))*B^χ*((Real.log L)^b*Hpos) :=
                mul_le_mul_of_nonneg_left hlinks hbase
            _ = _ := by ring
  have hw := ENNReal.ofReal_le_ofReal hpre
  rw [ENNReal.ofReal_mul (pow_nonneg hlog b)] at hw
  calc
    _ ≤ (ENNReal.ofReal N*Epos)*
        ENNReal.ofReal (L^(-D'*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre) := mul_le_mul_left hE _
    _ ≤ (ENNReal.ofReal N*Epos)*
        (ENNReal.ofReal ((Real.log L)^b)*
          ENNReal.ofReal (L^(-D'*(χ : ℝ))*B^χ*Hpos)) := mul_le_mul_right hw _
    _ = ENNReal.ofReal (N*(Real.log L)^b)*
        (Epos*ENNReal.ofReal (L^(-D'*(χ : ℝ))*B^χ*Hpos)) := by
      rw [ENNReal.ofReal_mul hN]
      ring

/-- The trivial deletion bound: the link count of `M` is at most a box factor times the link
count of an actual conditioned post problem. -/
theorem appb_deletion_value_le (M : Molecule V D) (hM : M.IsMolecule) {P : AppbPattern}
    (r : AppbRealization M P) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hγd : γ ≤ d) (hP : ∀ S,0 ≤ scales S) (hrank : r.post.circuitRank ≤ M.circuitRank) :
    ∃ q : Fin P.edges.length → (Fin d → ℤ),
      appbLinkCountA M L γ δ C1 w Adm scales ≤
        ENNReal.ofReal (((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)*
          (Real.log L)^(4*r.removedAtoms.card))*
        appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales := by
  have hLp := zero_lt_one.trans_le hL
  obtain ⟨p,q,-,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hbox := r.localChoices_card_le_box p hLp γ δ w Adm
  have hN : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast hbox
  have hE' : (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
      ENNReal.ofReal (((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) :=
    hcast.trans (mul_le_mul_left hN _)
  have hlinks := appbLinkProduct_eraseAtoms_bound M hM r.removedAtoms L γ δ scales hLp.le hlog
    hδ.1.le hP
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hHnon : 0 ≤ appbLinkProduct M L γ δ scales := by
    apply Finset.prod_nonneg
    intro S hS
    exact (appb_link_weight_bounds hLp.le hlog hδ.1.le (hP S) γ).1.trans' (by norm_num)
  obtain ⟨r0,hr0⟩ : ∃ r0 : ℕ, M.circuitRank = r.post.circuitRank+(r0 : ℤ) :=
    ⟨(M.circuitRank-r.post.circuitRank).toNat,by omega⟩
  have ha := appb_trivial_normalization (appbCountE M L γ δ w Adm : ℝ≥0∞)
    (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) r.post.circuitRank r0
    (4*r.removedAtoms.card) L ((d : ℝ)-γ) (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct M L γ δ scales)
    (appbLinkProduct r.post L γ δ scales) (((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)) hL
    (by linarith only [hγd]) hB hB1 (by positivity) hHnon hlinks hE'
  unfold appbLinkCountA
  rw [hr0]
  exact ha

end WaveTurbulence.Mole
