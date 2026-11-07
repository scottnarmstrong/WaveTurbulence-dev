/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew6
public import WaveTurbulence.Foundations.FinalCount.VCStmt
/-! # VINE-COUNT part 29 (session 4): **TARGET excessprop1 (2) for a single vine** (`prop94_vine_newcomp_single`, (excesseqn2+), L2167--L2177),
from `VINEPARAM`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

section Defs
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The source's fixed-set fact for an Operation 1 that creates a new component** (TARGET L2174): for each parameter
triple `(c, β, k⁰)`, in every restricted `(c_v)`-decoration of `M` the two bonds `ℓ₁, ℓ₂` of the removed vine `K`
satisfy: `k_{ℓ₁} - k_{ℓ₂} = k_{x₁} - k_{x₂}` equals a fixed nonzero lattice vector `n₀` (the gap of the SG joint is fixed and
nonzero), and the lower-joint energy `|k_{y₂}|² - |k_{y₁}|²` lies in a fixed interval of length `2ν δ⁻¹ L^{-2γ}` (`ν = n_sb`,
L2174). It holds because the new component is attached to the vine by a bridge, whose label is determined by the parameters. -/
def NewCompFixed (M : Molecule V D) (K : VineCut M) (L γ δ ν : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ n₀ : Fin d → ℤ, n₀ ≠ 0 ∧ ∃ e₀ : ℝ, ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      κ K.x₁ - κ K.x₂ = n₀ ∧
      |‖Molecule.kvec L w κ K.y₂‖ ^ 2 - ‖Molecule.kvec L w κ K.y₁‖ ^ 2 - e₀| ≤ ν * δ⁻¹ * L ^ (-2 * γ)

/-- The new-component label count in the form of the cover lemma (`labelSet` bound), under `NewCompFixed`. -/
def VineCountNew {M : Molecule V D} (K : VineCut M) (L γ δ ν Cf C₂ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (e : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    (K.labelSet L γ δ w Adm c β k0).encard ≤
      ENNReal.ofReal (vineFN d L γ δ ν Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card e)

end Defs

/-- **The new-component vine label count** (corollary of `vine_count_set_new`): for `NewCompFixed` classes. -/
theorem vine_count_main_new (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ ν : ℝ, 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) → (∃ X, M.IsVine X K.C.atoms K.C.upper K.C.lower) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (VCLadderScale K L w P) → NewCompFixed M K L γ δ ν w Adm →
        VineCountNew K L γ δ ν Cf C₂ w Adm P 4 := by
  obtain ⟨Cf, C₂, hCf, hC₂, h⟩ := vine_count_set_new hvp hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hL⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hLL ν hν V D _ _ _ M K hMol hM hvine w Adm P hP0 hscale hfix => ?_⟩
  intro c β k0 hparam
  obtain ⟨n₀, hn₀, e₀, hne⟩ := hfix c β k0 hparam
  exact hL L hLL ν hν M K hMol hM hvine w P hP0 β k0 n₀ e₀ (decSet M L γ δ w Adm c β k0) hn₀
    (fun κ hκ => ⟨c, hκ.1, hparam.1, (fun v hv _ => hκ.2.1.1 v hv), hκ.2.1.2,
      hscale c κ hκ.1 hparam.1 hκ.2.2, (hne κ hκ).1, (hne κ hκ).2⟩)

section Dev
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **TARGET excessprop1 (2) for a single vine, given the new-component count** (the analogue of `vine_excess_single'`). -/
theorem vine_excess_new (K : VineCut M) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ C₂ η ν : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂) (hle : C₂ ≤ C₁) (hν : 0 ≤ ν) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1)
    (hF : K.post.numComponents = M.numComponents + 1)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 2 ≤ K.C.atoms.card)
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountNew K L γ δ ν Cf C₂ w Adm P e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (K.post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) * (((e + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (e + 8)) *
        (L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hΛ1 := K.ladderProdVC_ge_one L γ δ P hL hδ.le hP0
  have hΛ0 : 0 < K.ladderProdVC L γ δ P := lt_of_lt_of_le zero_lt_one hΛ1
  set Λ := K.ladderProdVC L γ δ P with hΛ
  obtain ⟨k, hk⟩ : ∃ k, K.C.atoms.card = k + 1 := ⟨K.C.atoms.card - 1, by omega⟩
  set Fv := vineFN d L γ δ ν Cf C₂ Λ (k + 1) e with hFv
  have hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ ((⌊Fv⌋₊ : ℕ) : ℕ∞) := by
    intro c β k0 hp
    have := hcount c β k0 hp
    rw [hk] at this
    exact encard_le_floor this
  have h := K.vine_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P hL hδ hC hP0 hP1 hP2 ⌊Fv⌋₊ hN
  have hrk : M.circuitRank - K.post.circuitRank = ((k : ℕ) : ℤ) := by
    rw [circuitRank_diff_new K hF hB (by omega), hk]; simp
  rw [hrk] at h
  refine isDeviation_mono h ?_
  rw [rankFactor_nat d L γ δ C₁ hL0 k]
  have hΛd : ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S = Λ := rfl
  rw [hΛd]
  have hNx : ((⌊Fv⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8 * Λ) =
      ENNReal.ofReal ((⌊Fv⌋₊ : ℝ) * ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8 * Λ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hNx]
  refine ENNReal.ofReal_le_ofReal ?_
  have hreal := vine_real_new d k e (γ := γ) (C₁ := C₁) (C₂ := C₂) (ν := ν) (Cf := Cf) hL1 hδ hC hC₂ hle hν hCf hΛ0 hlog1
  have hε : 0 < η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 2, pow_pos hη 3]
  have hlogp := log_pow_le (e + 8) (by omega) L (η ^ 2 - η ^ 3) hL1 hε
  have hexc : excessRHS L γ η [] 1 2 = L ^ (-η ^ 3 + η ^ 2) := by
    have := excessRHS_beta L γ η hL0
    simpa using this
  have hKc : 0 ≤ Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) := by
    have h0 : 0 ≤ δ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hδ.le _
    have := hδ
    positivity
  calc _ ≤ Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) * (L ^ (min γ (1 - γ)) * Real.log L ^ (e + 8)) := hreal
    _ ≤ Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) * (L ^ (min γ (1 - γ)) *
        ((((e + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (e + 8) * L ^ (η ^ 2 - η ^ 3))) := by
        gcongr
    _ = _ := by
        rw [hexc, show -η ^ 3 + η ^ 2 = η ^ 2 - η ^ 3 by ring]
        ring

end Dev

end WaveTurbulence.VineCount
