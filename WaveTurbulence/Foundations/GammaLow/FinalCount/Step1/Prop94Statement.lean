/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.Prop94Statement`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # DH23 Proposition 9.4 (`excessprop1`, L1785): the statement, per operation of `Stage2Op` (FINALCOUNT-G2)

"After each operation in Steps 1--4, `𝔇 ≲ L^{-η³} ∏^{(α)}_v L^{(γ+3η)/2-κ_vη} R_v · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}`
for any `R_v ∈ [L⁻¹, L^{-γ+η}]`, the product over the newly created α-atoms; `κ_v = 0` if `ι_v = 0`, `κ_v = 50` if
`ι_v ≠ 0`."

The right-hand side is `excessRHS L γ η αs ΔF ΔV_β` (`Prop94Cut`); the deviation is `IsDeviation 𝔄_pre 𝔄_pos _`.
Per constructor of `Stage2Op` (`Prop94Ops`):

* `cut`, α: `prop94_alpha` (αs = [(R,κ),(R,κ)], ΔF = ΔV_β = 0);
* `cut`, β: `prop94_beta` (αs = [], ΔF = 1, ΔV_β = 2);
* `triangle`: `prop94_triangle` (αs = `T.alphaLabels`, ΔF = F(kept) - F(M), ΔV_β = 3 - |αs|);
* `vine`: `prop94_vine_single` / `prop94_vine_double`, **conditional on the vine label count `𝔉`**
  (`VineCountInput`, `VineCountInputDouble`: the named obligation of L1799--L1801, not proved here).

Readings (details in HANDOFF.md): the `ι_v ≠ 0` ball of L1801 is the hypothesis `IotaReading` (`Prop94Iota`), a
condition on the decoration alone; the fixed ball of L1801 is then derived (`ball_of_iota`), and the lattice
spacing `L⁻¹ ≤ L^{-50η}R` (needed for the vine count; `0 < |r ± r'|` with `r ± r' ∈ L⁻¹ℤ^d`) is `iota_radius_ge`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

instance (M : Molecule V D) (op : Stage2Op g M) : Fintype op.PostD := by
  cases op <;> (unfold Stage2Op.PostD; infer_instance)

instance (M : Molecule V D) (op : Stage2Op g M) : DecidableEq op.PostD := by
  cases op <;> (unfold Stage2Op.PostD; infer_instance)

-- (`prop94_alpha`, `prop94_beta`, `prop94_triangle` concern the family-free operations `.cut`, `.triangle`: main's.)

/-- **The vine label count, a VC formed by two double bonds** (L1801, last sentence). -/
def VineCountInputDouble {M : Molecule V D} (K : VineCut g M) (L γ δ R ρ Cf : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (e : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    (K.labelSet L γ δ w Adm c β k0).encard ≤ ENNReal.ofReal (vineG d L γ δ R ρ Cf e)

/-- **Prop 9.4, Step 1, a VC formed by two double bonds**, given the label count. -/
theorem prop94_vine_double {M : Molecule V D} (K : VineCut g M) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ) (hγ1 : γ < 1)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 4) (hA : K.C.atoms.card = 3) (hlad : K.vc.maximalLadders = ∅)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountInputDouble K L γ δ R ρ Cf w Adm e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) * (1 + δ⁻¹)) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) :=
  K.vine_excess_double hd hM L γ δ C₁ η w Adm Adm' hAdm' P hL hδ hδ1 hC hP0 hP1 hP2 hη hη1 hηγ hγ1 hF hB hA hlad
    R hRl hRu κ ρ (hρ.imp id (fun h => ⟨h.1, h.2.1⟩)) Cf hCf e hcount

end WaveTurbulence.GammaLow.FinalCount.Step1
