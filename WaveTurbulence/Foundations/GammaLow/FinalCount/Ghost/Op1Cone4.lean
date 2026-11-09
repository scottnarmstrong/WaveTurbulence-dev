/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Centre
/-! **L6E2, part 4: the Operation-1 creation step with the cone, assembled** (M1-R2 Theorem 6.1 (e) at Op 1).

**Exports.**
* `prop94_vine_all_cone`: L6-STEP1's `Step1.prop94_vine_all` (charted vines) at `κ = 0`, for a removal that is the
  creation step `s(P)` of NC critical pairs: the same premises without `ι` (`κ = 0`), plus a critical label
  (`Crit L γ η Rg`), the creation cone of the joint gap (`JointCone`) and `200η ≤ γ`, `200η ≤ 1 - γ` (`TriReal`);
  the conclusion is L6-STEP1's bound times `3·5^d · L^{-5ηk}` for every `k ≤ 2`.
* **`prop94_vine_all_gamma_cone`**: the same for `𝒱_γ` (`Step1.SingleVineVCGamma`, L4's Theorem C), i.e. the cone
  form of `Step1.prop94_vine_all_gamma`, which is what L6's run uses at Op-1 steps.
* `jointCone_of_present` (Lemma 6.2(iii) at Op 1): the decoration-level cone around the gap of a present degree-2 atom
  (the earlier ghost `x`) gives `JointCone` (centre `c_x`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

/-- **DH23 Prop 9.4, Step 1, at a creation step `s(P)` with the cone** (charted vines; cf. `Step1.prop94_vine_all`). -/
theorem prop94_vine_all_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (Step1.SingleVineVC K ∨ Nonempty (Step1.DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (VineCount.SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → Crit L γ η Rg →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        JointCone K L γ δ η w Adm → ∀ k : ℕ, k ≤ 2 →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0)) := by
  obtain ⟨Cf₁, C₂₁, hCf₁, hC₂₁, h₁⟩ := prop94_vine_final_cone (g := g) hd hγ
  obtain ⟨Cf₂, C₂₂, hCf₂, hC₂₂, h₂⟩ := prop94_hyper_final_cone (g := g) hd hγ
  refine ⟨max (max Cf₁ Cf₂) ((9 : ℝ) ^ d * 5 ^ d * (2 * d)), le_max_of_le_left (le_max_of_le_left hCf₁),
    max C₂₁ C₂₂, le_max_of_le_left hC₂₁, ?_⟩
  intro δ hδ
  obtain ⟨L₁, hL₁, hh₁⟩ := h₁ δ hδ
  obtain ⟨L₂, hL₂, hh₂⟩ := h₂ δ hδ
  refine ⟨max (max L₁ L₂) (Real.exp 1), le_max_right _ _, ?_⟩
  intro L hL C₁ η hC₁ hη hη1 hηγ h200a h200b V D _ _ _ M K hMol hM hcls w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF
    Rg hRl hRu hcrit hgap hlow hcone k hk
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL0 : 0 < L := by linarith
  have hLa : L ≥ L₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLb : L ≥ L₂ := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hCa : C₂₁ ≤ C₁ := (le_max_left _ _).trans hC₁
  have hCb : C₂₂ ≤ C₁ := (le_max_right _ _).trans hC₁
  have ht : 0 < 2 * η - η ^ 3 := by nlinarith [sq_nonneg η, mul_pos hη hη]
  have ht2 : 2 * η - η ^ 3 ≤ 2 := by nlinarith [sq_nonneg η, pow_pos hη 3]
  have hE : 0 ≤ excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0 := by
    rw [excessRHS_alpha]; positivity
  have hXY := coneX_le_transfer d hL1' hη.le hd k hk
  have hX0 := coneX_nonneg d (η := η) hL0
  rcases hcls with hs | hS
  · unfold Step1.SingleVineVC at hs
    rcases hsh : K.C.shape with hv | R
    · rw [hsh] at hs
      have hscale : VineCount.DecScale M L w Adm (Step1.VCLadderScale K L w P) :=
        fun c κ' hdec hc0 hk' => Step1.vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hdec hc0
          (hAdm c κ' hdec hc0 hk')
      have := hh₁ L hLa C₁ η hCa hη hη1 hηγ h200a h200b M K hMol hM hs w Adm Adm' hAdm' P hP0 hP1 hP2 hF Rg hRl hRu
        hcrit hgap hcone hscale
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact cone_const_single d hCf₁ (le_max_of_le_left (le_max_left _ _)) ht hδ.1 hE hX0 hXY
    · rw [hsh] at hs
      have := hh₂ L hLb C₁ η hCb hη hη1 hηγ h200a h200b M K R hsh hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF
        Rg hRl hRu hcrit hgap hcone
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact cone_const_single d hCf₂ (le_max_of_le_left (le_max_right _ _)) ht hδ.1 hE hX0 hXY
  · obtain ⟨S⟩ := hS
    have hC1 : 1 ≤ C₁ := hC₂₁.trans hCa
    have := prop94_vine_double_cone K S hd hM L γ δ C₁ η w Adm Adm' hAdm' P hLe hδ.1 hδ.2 hC1 hP0 hP1 hP2 hγ hη hη1
      hηγ h200a h200b hF Rg hRl hRu hcrit hgap hlow hcone
    refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
    exact cone_const_double d (by positivity) (le_max_right _ _) ht ht2 hδ.1 hE hX0 hXY

/-- **The Operation-1 creation step of `𝒱_γ` with the cone** (cone form of `Step1.prop94_vine_all_gamma`; vine
hypothesis: L4's Theorem C only). For a removal `K : Step1.VineCut γ M` with `ΔF = 0` whose joints are the later
ghosts of `k ≤ 2` NC critical pairs (`κ = 0`, critical label, joint gap in the creation cone), the Step-1 deviation
holds with the extra factor `3·5^d · L^{-5ηk}`. -/
theorem prop94_vine_all_gamma_cone (hT : TVine.Chart.TVineChartExists) (hd : 3 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        (Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (VineCount.SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → Crit L γ η Rg →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        JointCone K L γ δ η w Adm → ∀ k : ℕ, k ≤ 2 →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, h⟩ := prop94_vine_all_cone (g := γ) hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ h200a h200b V D _ _ _ M K hMol hM hcls => ?_⟩
  exact hh L hL C₁ η hC₁ hη hη1 hηγ h200a h200b M K hMol hM (hcls.imp_left (Step1.singleVineVC_of_gamma hT hMol K))

/-- **Lemma 6.2(iii) at an Op-1 step**: the cone of the joint gap around the gap of a present degree-2 atom `v` (darts
`x₁'` out, `x₂'` in; nonzero gap) is a cone around the fixed centre `c v` in each parameter class. For the joint at the
other end (gap `±r`), use `inCone_neg`. -/
theorem jointCone_of_present {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : Step1.VineCut g M) {L γ δ η : ℝ} (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (v : V) (hv : v ∈ M.atoms)
    (x₁' x₂' : D) (hx : x₁' ≠ x₂') (hdarts : M.dartsAt v = {x₁', x₂'}) (h1 : M.out x₁' = true)
    (h2 : M.out x₂' = false) (hd : 0 < d) (hnz : ∀ κ', Adm κ' → Molecule.gapAt L w κ' x₁' x₂' ≠ 0)
    (hcone : ∀ κ', Adm κ' →
      InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ' K.x₁ K.x₂) (Molecule.gapAt L w κ' x₁' x₂')) :
    JointCone K L γ δ η w Adm := by
  intro c β k0 _
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  · obtain ⟨κs, hκs⟩ := hne
    refine ⟨c v, ?_, fun κ' hκ' => ?_⟩
    · rw [← gap_eq_param_deg2 M hκs.1 v hv x₁' x₂' hx hdarts h1 h2]; exact hnz κs hκs.2.2
    · have := hcone κ' hκ'.2.2
      rwa [gap_eq_param_deg2 M hκ'.1 v hv x₁' x₂' hx hdarts h1 h2] at this
  · refine ⟨EuclideanSpace.single ⟨0, hd⟩ 1, ?_, fun κ' hκ' => absurd ⟨κ', hκ'⟩ hne⟩
    intro h
    have := congrArg (fun u : Mom d => u ⟨0, hd⟩) h
    simp at this

end WaveTurbulence.GammaLow.FinalCount.Ghost
