/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm16a
public import WaveTurbulence.Foundations.FinalCount.AsmPotG
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 16b: the terminal bound at a state** (`hterm_core`): the cluster-family chain, the component
bounds, `term_glue`, `term_exponent`, `hZ_of`, `alpha_part`, and the comparison with the potential. -/
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

theorem hterm_core {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ}
    {L γ η δ C₁ C₀ : ℝ} {crit : V → Prop} {𝒦 : Finset (Finset V)} {j : Finset V → ℤ} {Rs : Finset V}
    (hL1 : 1 ≤ L) (hγ0 : 0 ≤ gam0 γ) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hγη : 5 * η ≤ γ) (hC₀ : 1 ≤ C₀)
    (hg : Good R hf.s) (hst : FinalStructE R 0 hf.s) (hR1 : 1 ≤ R) (hcrit : critCount crit hf.s = 0)
    (hlab : ∀ v ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls v = .alpha ρ kp → L⁻¹ ≤ ρ ∧ ρ ≤ L ^ (-γ + η) ∧ (kp = 0 ∨ kp = 50))
    (hdpos : ∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) (hM4 : ∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4)
    (hcl : Clusters hf.s.M 𝒦) (h1 : 𝒦.biUnion id = tameSet hf Tm)
    (hrk : hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K)
    (hR : CompRep (hf.op5 Tm).s.M Rs)
    (hQ : QS L γ δ C₁ (0 : Mom d) P hf A ≤ (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K))) *
          ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
            (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P)
    (hcomp : ∀ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exa γ η hf Tm R a)) :
    QS L γ δ C₁ (0 : Mom d) P hf A ≤
      WPot L γ η (L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2)) (gExp η crit) hf := by
  have hL0 : 0 < L := by linarith
  have hρ1 := one_le_rho_of_good hR1 hg
  have hZ := hZ_of hst hR1 h1 hR
  have hexp := term_exponent hγ0 hη hη4 hC₀ hg hcl h1 hrk hR hdpos hM4 hZ (by exact_mod_cast hρ1)
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
  have hglue := term_glue 𝒦 Rs (fun K => exK γ η C₀ K.card (eDart hf.s.M K) (j K))
    (fun a => ∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) (exa γ η hf Tm R)
    (fun a => (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
      (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P)
    (Q := QS L γ δ C₁ (0 : Mom d) P hf A) (ap := apProd L γ η hf.s)
    (Ey := eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * (hf.s.M.rho : ℝ)
        - eraseA γ η * (hf.s.M.numComponents : ℝ) + (gam0 γ + 2 * η ^ 2) * (vBeta hf.s : ℝ))
    hL1 hapP hAnn (by simpa only [clusterRHSs_eq] using hQ) hcomp (alpha_part hR hap) hexp
  refine hglue.trans ?_
  unfold WPot potR gExp
  have hcrit' : (critCount crit hf.s : ℝ) = 0 := by exact_mod_cast hcrit
  rw [hcrit']
  refine ENNReal.ofReal_le_ofReal ?_
  have e : L ^ (-(4 * η ^ 6 * ((hf.s.M.rho : ℝ) + 0))) * 1 = L ^ (-(4 * η ^ 6 * ((hf.s.M.rho : ℝ) + 0))) := mul_one _
  rw [div_le_div_iff_of_pos_right hapP]
  rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
  refine Real.rpow_le_rpow_of_exponent_le hL1 (le_of_eq ?_)
  unfold eraseA gam0
  ring

end WaveTurbulence.FinalCountAsm
