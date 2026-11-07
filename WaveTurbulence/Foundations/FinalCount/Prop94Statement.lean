/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess5
public import WaveTurbulence.Foundations.FinalCount.VineDouble7
public import WaveTurbulence.Foundations.FinalCount.TriDev4
public import WaveTurbulence.Foundations.FinalCount.Prop94Iota
/-! # DH23 Proposition 9.4 (`excessprop1`, L1785): the statement, per operation of `Stage2Op` (FINALCOUNT-G2)

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
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

instance (M : Molecule V D) (op : Stage2Op M) : Fintype op.PostD := by
  cases op <;> (unfold Stage2Op.PostD; infer_instance)

instance (M : Molecule V D) (op : Stage2Op M) : DecidableEq op.PostD := by
  cases op <;> (unfold Stage2Op.PostD; infer_instance)

/-- **Prop 9.4, `α`-cut (Steps 3--4).** -/
theorem prop94_alpha {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D} (hd : 3 ≤ d) (hcd : M.IsCutData v v₂ x₁ x₂)
    (hdeg : M.deg v ≤ 4) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hα : M.IsAlphaCut v v₂ x₁ x₂)
    (L γ η δ C₁ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hηγ : η ≤ γ) (hη1 : η ≤ (1 - γ) / 200)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (hκ : κ = 0 ∨ κ = 50)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' x₁ x₂‖ ≤ 2 * R)
    (hι : κ = 50 → IotaReading M L w Adm x₁ x₂ (L ^ (-50 * η) * R)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.cut v v₂ x₁ x₂ hcd).post.countA L γ δ C₁ w Adm P)
      (ENNReal.ofReal ((26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) :=
  alphaCut_excess M hd hcd hdeg hM hα L γ η δ C₁ hγ0 hγ1 hη hηγ hη1 w Adm P hL hδ0 hδ1 hC hP0 hPinh R hRl hRu κ hκ
    hgap (fun h c β k0 hp => ball_of_iota (hι h) c β k0 hp)

/-- **Prop 9.4, `β`-cut (Steps 3--4).** -/
theorem prop94_beta {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D} (hcd : M.IsCutData v v₂ x₁ x₂)
    (hdeg : M.deg v ≤ 4) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hβ : ¬ M.IsAlphaCut v v₂ x₁ x₂)
    (L γ η δ C₁ : ℝ) (hη : 0 < η) (hη1 : η < 1) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hC : 0 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.cut v v₂ x₁ x₂ hcd).post.countA L γ δ C₁ w Adm P)
      (ENNReal.ofReal ((10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4)) * excessRHS L γ η [] 1 2)) :=
  betaCut_excess M hcd hdeg hM hβ L γ η δ C₁ hη hη1 c hn w Adm P hL hδ0 hC hP0 hPinh

/-- **Prop 9.4, triangles (Step 2).** `hnz`: the gaps at the three triangle atoms are nonzero (Remark
`subcondition`: the SG triples). -/
theorem prop94_triangle {M : Molecule V D} (T : TriData M) {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hι0 : κ₀ = 50 → IotaReading M L w Adm (T.a 0) (T.b 0) (L ^ (-50 * η) * R₀))
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hι1 : κ₁ = 50 → IotaReading M L w Adm (T.a 1) (T.b 1) (L ^ (-50 * η) * R₁)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.triangle T).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ *
        excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁) ((T.kept.numComponents : ℤ) - M.numComponents)
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ)))) :=
  T.triangle_excess H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ hκ₀ hκ₁ hR₀l hR₀u hR₁l hR₁u
    hgap0 (fun h c β k0 hp => ball_of_iota (hι0 h) c β k0 hp)
    hgap1 (fun h c β k0 hp => ball_of_iota (hι1 h) c β k0 hp)

/-- **The vine label count (the named obligation of L1799--L1801), single vine.** For every admissible parameter triple
the number of label vectors of the removed vine is at most
`𝔉 = Cf · L^d (ρL)^d L^{(m-2)(d-γ)} δ^{-m/2} (log L)^e / ∏_{𝕃_j ⊂ 𝕍ℂ} 𝔛_j^{z_j}`, `m = |𝕍ℂ|`
(`ρ = 2R` if `κ = 0`, `ρ = L^{-50η}R` if `κ = 50`). -/
def VineCountInput {M : Molecule V D} (K : VineCut M) (L γ δ ρ Cf : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (e : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    (K.labelSet L γ δ w Adm c β k0).encard ≤
      ENNReal.ofReal (vineF d L γ δ ρ Cf (K.ladderProdVC L γ δ P) K.C.atoms.card e)

/-- **The vine label count, a VC formed by two double bonds** (L1801, last sentence). -/
def VineCountInputDouble {M : Molecule V D} (K : VineCut M) (L γ δ R ρ Cf : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (e : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    (K.labelSet L γ δ w Adm c β k0).encard ≤ ENNReal.ofReal (vineG d L γ δ R ρ Cf e)

/-- **Prop 9.4, Step 1, a single vine**, given the label count. -/
theorem prop94_vine_single {M : Molecule V D} (K : VineCut M) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 2 ≤ K.C.atoms.card)
    (R : ℝ) (hR0 : 0 ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountInput K L γ δ ρ Cf w Adm P e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1))) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) :=
  K.vine_excess_single hd hM L γ δ C₁ η w Adm Adm' hAdm' P hL hδ hC hP0 hP1 hP2 hη hη1 hηγ hF hB hm R hR0 hRu κ ρ
    (hρ.imp id (fun h => ⟨h.1, h.2.1⟩)) Cf hCf e hcount

/-- **Prop 9.4, Step 1, a VC formed by two double bonds**, given the label count. -/
theorem prop94_vine_double {M : Molecule V D} (K : VineCut M) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
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

/-- **Prop 9.4, Step 1, a VC formed by two double bonds `a = x = b`: unconditional** (the count `𝔉` of L1801, last
sentence, is `DoubleShape.labelSet_le_vineG`). Source facts assumed: the shape `S`; `ΔF = 0` (`hF`, L1798);
`4` bonds in the VC (`hB`, two double bonds); no ladder in the VC (`hlad`); the label `|r| ~ R` of the new
`α`-atoms (`hgap`: `|r| <= 2R`, `hlow`: `|r| >= R/2`); for `κ = 50` the `ι` condition (`hι`). -/
theorem prop94_vine_double_full {M : Molecule V D} (K : VineCut M) (S : DoubleShape K) (hd : 3 ≤ d)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ) (hγ1 : γ < 1)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 4) (hlad : K.vc.maximalLadders = ∅)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R)
    (hlow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖)
    (hι : κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * R)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (((9 ^ d * 5 ^ d * (2 * d)) * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (0 + 8 + 1)) *
        (1 + δ⁻¹)) * excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hA : K.C.atoms.card = 3 := by
    rw [S.atoms_eq]
    have h1 : K.C.upper ≠ S.x := S.x_ne_a.symm
    have h2 : S.x ≠ K.C.lower := S.x_ne_b
    have h3 : K.C.upper ≠ K.C.lower := K.ab_ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h3]), Finset.card_pair h2]
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR.le
  have hρL : 1 ≤ ρ * L := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · have : 1 ≤ R * L := by
        have := mul_le_mul_of_nonneg_right hRl hL0.le
        rwa [inv_mul_cancel₀ hL0.ne'] at this
      nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact ball_of_iota (hι hκ50) c β k0 hp
  have hcount : VineCountInputDouble K L γ δ R ρ (9 ^ d * 5 ^ d * (2 * d)) w Adm 0 :=
    S.labelSet_le_vineG (by omega) hL1 hδ hδ1 R ρ hR hρ0 hρL hlow hball
  exact prop94_vine_double K hd hM L γ δ C₁ η w Adm Adm' hAdm' P hL hδ hδ1 hC hP0 hP1 hP2 hη hη1 hηγ hγ1 hF hB hA hlad
    R hRl hRu κ ρ hρ _ (by positivity) 0 hcount

end WaveTurbulence.FinalCount
