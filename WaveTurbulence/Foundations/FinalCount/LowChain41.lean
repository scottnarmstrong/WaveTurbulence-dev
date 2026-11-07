/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain40
/-! **FINALCOUNT LOW-CHAIN, session 6 (15): `hterm_coreL`** (copy of `hterm_core` with the loop credit): from the weighted cluster/component
count `rankFactor(k) · QS ≤ ∏_K clusterRHSs(j + k_K) · ∏_a 𝔄(a)` and the component bounds, `QS ≤ WPot (Ypk .. k R') gExp`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hterm_coreL {hf : HSt V D₀} {Tm : V → Prop} {R' r k : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ}
    {L γ η δ C₁ C₀ : ℝ} {crit : V → Prop} {𝒦 : Finset (Finset V)} {j : Finset V → ℤ} {Rs : Finset V} {B : Finset V}
    (hL1 : 1 ≤ L) (hγ0 : 0 ≤ gam0 γ) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hγη : 5 * η ≤ γ) (hC₀ : 1 ≤ C₀)
    (hg : Good R' hf.s) (hRk : r + k = R') (hBT : ∀ b ∈ B, b ∈ tameSet hf Tm) (hBdeg : ∀ b ∈ B, hf.s.M.deg b ≤ 2)
    (hBcard : B.card = k) (hcrit : critCount crit hf.s = 0)
    (hlab : ∀ v ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls v = .alpha ρ kp → L⁻¹ ≤ ρ ∧ ρ ≤ L ^ (-γ + η) ∧ (kp = 0 ∨ kp = 50))
    (hdpos : ∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) (hM4 : ∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4)
    (hcl : Clusters hf.s.M 𝒦) (h1 : 𝒦.biUnion id = tameSet hf Tm)
    (hrk : hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K)
    (hkK : ∑ K ∈ 𝒦, (K.filter fun a => a ∈ B).card = k)
    (hR : CompRep (hf.op5 Tm).s.M Rs) {gk : ℝ} (hgk : 0 < gk)
    (hQ : ENNReal.ofReal gk * QS L γ δ C₁ (0 : Mom d) P hf A ≤
      (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K + ((K.filter fun a => a ∈ B).card : ℤ)))) *
        ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P)
    (hcomp : ∀ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exaL γ η hf Tm r a))
    (hLF1 : r = 1 → tameSet hf Tm = ∅ → ∀ e ∈ hf.s.M.atoms, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e) :
    QS L γ δ C₁ (0 : Mom d) P hf A ≤
      WPot L γ η (Ypk L γ η ((η ^ 5 - 4 * η ^ 6) / 2) gk k R') (gExp η crit) hf := by
  have hL0 : 0 < L := by linarith
  have hρ1 : 1 ≤ r → 1 ≤ hf.s.M.rho := fun hr => one_le_rho_of_good (by omega) hg
  have hZ := hZ_ofL hg hRk hBT hBdeg hBcard h1 hR hLF1
  have hexp := term_exponentL hγ0 hη hη4 hC₀ hRk hkK hg hcl h1 hrk hR hdpos hM4 hZ hρ1
  have hap : ∀ v ∈ hf.s.M.atoms, 0 < apFactor L γ η (hf.s.cls v) ∧ apFactor L γ η (hf.s.cls v) ≤ 1 :=
    fun v hv => apFactor_pos_le_one hL1 hγη hη.le (fun ρ kp h => hlab v hv ρ kp h)
  have hapP : 0 < apProd L γ η hf.s := Finset.prod_pos fun v hv => (hap v hv).1
  have hAnn : ∀ a ∈ Rs, 0 ≤ ∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹ := by
    intro a ha
    refine Finset.prod_nonneg fun v hv => ?_
    have hv' : v ∈ hf.s.M.atoms := by
      rw [compMol_atoms_eq] at hv
      exact (Op5.atoms_sub (Finset.mem_filter.1 hv).1).1
    exact inv_nonneg.2 (hap v hv').1.le
  set ε0 : ℝ := (η ^ 5 - 4 * η ^ 6) / 2 with hε0
  set Ey : ℝ := eraseA γ η * (r : ℝ) + 4 * η * (((r - 1 : ℕ) : ℝ)) - (if 1 ≤ r then ε0 else 0) -
        4 * η ^ 6 * (hf.s.M.rho : ℝ) - eraseA γ η * (hf.s.M.numComponents : ℝ) + (gam0 γ + 2 * η ^ 2) * (vBeta hf.s : ℝ) with hEy
  have hglue := term_glue 𝒦 Rs (fun K => exK γ η C₀ K.card (eDart hf.s.M K) (j K + ((K.filter fun a => a ∈ B).card : ℤ)))
    (fun a => ∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) (exaL γ η hf Tm r)
    (fun a => (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
      (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P)
    (Q := ENNReal.ofReal gk * QS L γ δ C₁ (0 : Mom d) P hf A) (ap := apProd L γ η hf.s) (Ey := Ey)
    hL1 hapP hAnn (by simpa only [clusterRHSs_eq] using hQ) hcomp (alpha_part hR hap) hexp
  have hcrit' : (critCount crit hf.s : ℝ) = 0 := by exact_mod_cast hcrit
  have hYz : Yz L γ η ε0 ((R' : ℤ) - k) = L ^ (eraseA γ η * (r : ℝ) + 4 * η * (((r - 1 : ℕ) : ℝ)) - (if 1 ≤ r then ε0 else 0)) := by
    have hr' : ((R' : ℤ) - k) = (r : ℤ) := by omega
    rw [hr']
    unfold Yz
    have e1 : (((r : ℤ) : ℝ)) = (r : ℝ) := by push_cast; rfl
    have e2 : (((max ((r : ℤ) - 1) 0 : ℤ)) : ℝ) = (((r - 1 : ℕ) : ℝ)) := by
      have : max ((r : ℤ) - 1) 0 = ((r - 1 : ℕ) : ℤ) := by omega
      rw [this]; push_cast; rfl
    have e3 : (if (1 : ℤ) ≤ (r : ℤ) then ε0 else 0) = (if 1 ≤ r then ε0 else 0) := by
      simp only [Nat.one_le_cast]
    rw [e1, e2, e3]
  have hgk' : 0 ≤ gk⁻¹ := inv_nonneg.2 hgk.le
  have hE : L ^ (eraseA γ η * (r : ℝ) + 4 * η * (((r - 1 : ℕ) : ℝ)) - (if 1 ≤ r then ε0 else 0)) * L ^ (-(gExp η crit hf)) *
      L ^ (-(2 * min γ (1 - γ) + 5 * η ^ 2) * (hf.s.M.numComponents : ℝ) + (min γ (1 - γ) + 2 * η ^ 2) * (vBeta hf.s : ℝ)) = L ^ Ey := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    unfold gExp gam0 eraseA at *
    rw [hcrit']
    simp only [hEy, gam0, eraseA]
    ring
  unfold WPot potR Ypk
  rw [hYz]
  have hq : QS L γ δ C₁ (0 : Mom d) P hf A ≤ ENNReal.ofReal gk⁻¹ * ENNReal.ofReal (L ^ Ey / apProd L γ η hf.s) := by
    have h1 : ENNReal.ofReal gk⁻¹ * ENNReal.ofReal gk = 1 := by
      rw [← ENNReal.ofReal_mul hgk', inv_mul_cancel₀ hgk.ne', ENNReal.ofReal_one]
    calc QS L γ δ C₁ (0 : Mom d) P hf A = (ENNReal.ofReal gk⁻¹ * ENNReal.ofReal gk) * QS L γ δ C₁ (0 : Mom d) P hf A := by
          rw [h1, one_mul]
      _ = ENNReal.ofReal gk⁻¹ * (ENNReal.ofReal gk * QS L γ δ C₁ (0 : Mom d) P hf A) := by ring
      _ ≤ _ := by gcongr
  refine hq.trans ?_
  rw [← ENNReal.ofReal_mul hgk']
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [← hE]
  ring

end WaveTurbulence.FinalCountAsm
