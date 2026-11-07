/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount4
/-! # VINE-COUNT part 23: Prop 9.4, Step 1, single vine (DH23 L1797--L1801), from `VINEPARAM`. -/
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

section Bonds
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M)
  (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
include hB

/-- The bonds of the removed vine are the internal bonds of the block. -/
theorem vc_bonds_card : K.vc.bonds.card = (internalBondSet M K.C.atoms).card := by
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have ho : K.vc.out x = true := (Finset.mem_filter.mp hx).2
    unfold internalBondSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, (vc_dart_iff K hB x.1).mp x.2⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro y hy
    unfold internalBondSet at hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y, (vc_dart_iff K hB y).mpr hy2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy1).2⟩, rfl⟩

end Bonds

section Single
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **Prop 9.4, Step 1, a single vine, given the re-scoped count `𝔉`** -- `prop94_vine_single'` (R17):
the same statement as `FinalCount.prop94_vine_single` with `VineCountInput'` and `C₂ ≤ C₁`. -/
theorem prop94_vine_single' (K : VineCut M) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ C₂ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂) (hle : C₂ ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 2 ≤ K.C.atoms.card)
    (R : ℝ) (hR0 : 0 ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountInput' K L γ δ ρ Cf C₂ w Adm P e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1))) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) :=
  vine_excess_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL hδ hC hC₂ hle hP0 hP1 hP2 hη hη1 hηγ hF hB hm
    R hR0 hRu κ ρ (hρ.imp id (fun h => ⟨h.1, h.2.1⟩)) Cf hCf e hcount

/-- **DH23 Prop 9.4, Step 1, a single vine (L1797--L1801), from `VINEPARAM` alone.** For `d ≥ 3`, `γ ∈ (0,1)`
there are constants `Cf, C₂` (depending on `d, γ`) such that for all `δ ∈ (0,1]`, `L` large, every `C₁ ≥ C₂`, every
`η ≤ γ`, every molecule `M` (`M.IsMolecule`, degrees `≤ 4`) and every vine removal `K` (Stage-2 operation `vine`)
whose removed object is a single vine, with `ΔF = 0` (`hF`, L1798), the new `α`-atoms labelled by `R ∈ [L⁻¹, L^{-γ+η}]`
(`κ ∈ {0, 50}`; for `κ = 50` the `ι`-condition `IotaReading`), and an admissible class `Adm` that carries the ladder scales
(`VCLadderScale`), the deviation of the operation is `≲ L^{-η³} ∏ L^{(γ+3η)/2-κη}R` (excesseqn2). -/
theorem prop94_vine_final (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (∃ X, M.IsVine X K.C.atoms K.C.upper K.C.lower) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (R : ℝ), L⁻¹ ≤ R → R ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R) →
        (κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * R)) →
        DecScale M L w Adm (VCLadderScale K L w P) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := vine_count_main hvp hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ => ?_⟩
  intro V D _ _ _ M K hMol hM hvine w Adm Adm' hAdm' P hP0 hP1 hP2 hF R hRl hRu κ ρ hρ hgap hι hscale
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hRL : 1 ≤ R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1' (by linarith))
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0.le
  have hρ2 : ρ ≤ 2 := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · have : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1' (by linarith)
      nlinarith [Real.rpow_nonneg hL0.le (-50 * η)]
  have hρL : 1 ≤ ρ * L := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact ball_of_iota (hι hκ50) c β k0 hp
  have hcount := hcnt L hL M K hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball
  obtain ⟨X, hX⟩ := hvine
  obtain ⟨A⟩ := hvp V D M hMol X _ _ _ hX
  have hcard := card_atoms_eq K A
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [vc_bonds_card K hX.1, A.bond_count]; omega
  have hn1 : 1 ≤ A.indexing.shape.n := by unfold Shape.n; omega
  exact prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith) hC₁
    hP0 hP1 hP2 hη hη1 hηγ hF hbc (by omega) R hR0.le hRu κ ρ hρ Cf hCf 4 hcount

end Single

end WaveTurbulence.VineCount
