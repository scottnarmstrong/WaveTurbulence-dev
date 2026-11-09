/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCCount4`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 22: **the single-vine label count `𝔉`** (DH23 L1799--L1801), of a charted vine (main: from `VINEPARAM`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
variable {d : ℕ}
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

/-- **A label vector that the count applies to** (the restricted-decoration facts of one `κ`, as used by the count):
a `c`-decoration of the molecule with `c = 0` at the degree-`4` atoms, the `Γ`-windows at the degree-`4` atoms
(the interior atoms of the vine), the unit-ball localisation, the ladder scales of the removed vine and the gap in a ball.
Only the degree-`4` atoms matter, so a decoration of an adjoint (hyper case) qualifies. -/
def GoodLabel {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M)
    (L γ δ : ℝ) (w : Mom d) (P : Finset V → ℝ) (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (ρ : ℝ)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ c : V → Mom d, M.IsDecoration L w c κ ∧ (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) ∧
    (∀ v ∈ M.atoms, M.deg v = 4 → |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ)) ∧
    (∀ x, ‖Molecule.kvec L w κ x - k0 x‖ ≤ 1) ∧ VCLadderScale K L w P κ ∧
    ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ

/-- **A charted block** (L6-STEP1): a block `S` with joints `a, b` carrying a full chart (main's `FullVineChart`, for
some type index `X`). This is all that main's Step-1 count uses of a vine (the chart and `IsBlock`); every member of
`𝒱_γ` is charted (`Step1.Chart`: drawn vines by main's `Vine.Param.vineparam`, T-vines by L4's Theorem C). It replaces
main's premise `VINEPARAM` together with `∃ X, M.IsVine X S a b`. -/
def Charted {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsBlock S a b ∧ ∃ X : VineType, Nonempty (FullVineChart M X S a b)

/-- **The vine label count** `𝔉` (DH23 L1799--L1801), single vine, of a charted block (main: from `VINEPARAM`). For every `d ≥ 3`, `γ ∈ (0,1)`
there are constants `Cf, C₂` (depending only on `d, γ`) such that for every `δ ∈ (0,1]` and `L` large enough, for every
molecule `M` of degree `≤ 4` and every `VineCut g K` of `M` whose removed object is a single vine,
the number of label vectors of the removed vine is at most `vineF'` (with `e = 4`),
provided the admissible class `Adm` carries the ladder scales of the maximal ladders of the vine. -/
theorem vine_count_set (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) → Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 2 → 1 ≤ ρ * L →
        ∀ (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (T : Set (D → (Fin d → ℤ))),
        (∀ κ ∈ T, GoodLabel M K L γ δ w P β k0 r₀ ρ κ) →
        (K.restrS '' T).encard ≤
          ENNReal.ofReal (vineF' d L γ δ ρ Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card 4) := by
  obtain ⟨Cp, hCp0, hCp⟩ := pairSet_count hd hγ (c₀ := 8) (by norm_num)
  obtain ⟨Ct, hCt0, hCt⟩ := tripleSet_count hd hγ
  refine ⟨(coverNum d : ℝ) * 9 ^ d, max 1 (max Cp Ct), by positivity, le_max_left _ _, ?_⟩
  intro δ hδ
  obtain ⟨L₀p, hL₀p⟩ := hCp δ hδ
  obtain ⟨L₀t, hL₀t⟩ := hCt δ hδ
  refine ⟨max (max L₀p L₀t) (Real.exp 1), le_max_right _ _, ?_⟩
  intro L hL V D _ _ _ M K hMol hM hvine w P hP0 ρ hρ0 hρ2 hρL β k0 r₀ T hT
  have hLp : L ≥ L₀p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLt : L ≥ L₀t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL1 : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL1
  have hlog : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL1
    rwa [Real.log_exp] at this
  have hδ0 := hδ.1
  have hδ1 := hδ.2
  have hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := by positivity
  have hpair : PairProp d γ δ Cp L := fun nr Pr h1 h2 cx cy α β' ζ0 ζ1 hz0 hz1 hne =>
    hL₀p L hLp nr Pr h1 h2 cx cy α β' ζ0 ζ1 hz0 hz1 hne
  have htrip : TripleProp d γ δ Ct L := fun c0 c1 c2 lin α β' => hL₀t L hLt c0 c1 c2 lin α β'
  by_cases hne : (K.restrS '' T).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  obtain ⟨hB, X, ⟨A⟩⟩ := hvine
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hr₀ : ∀ κ ∈ T, ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ := fun κ hκ => (hT κ hκ).choose_spec.2.2.2.2.2
  have hballκ : ∀ κ ∈ T, ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ 2 := fun κ hκ => (hr₀ κ hκ).trans hρ2
  -- the set of occurring gaps
  let Rocc : Set (Fin d → ℤ) := rint K '' T
  have hRsub : Rocc ⊆ {n | ‖latticePoint L n - r₀‖ ≤ ρ} := by
    rintro _ ⟨κ, hκ, rfl⟩
    show ‖latticePoint L (rint K κ) - r₀‖ ≤ ρ
    rw [← gapAt_eq_lattice K L w κ]; exact hr₀ κ hκ
  have hRfin : Rocc.Finite := (finite_ball hL0 r₀ ρ).subset hRsub
  have hRcard : (hRfin.toFinset.card : ℝ) ≤ (3 * (ρ * L)) ^ d := by
    have h1 : hRfin.toFinset.card = Rocc.ncard := (Set.ncard_eq_toFinset_card _ hRfin).symm
    have h2 : (Rocc.ncard : ℝ) ≤ ({n : Fin d → ℤ | ‖latticePoint L n - r₀‖ ≤ ρ}.ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hRsub (finite_ball hL0 r₀ ρ)
    have h3 := ncard_ball_le hL0 r₀ hρ0
    rw [h1]
    exact h2.trans (h3.trans (pow_le_pow_left₀ (by positivity) (by linarith) d))
  -- weights
  let W : Finset V → ℝ := fun S' => Molecule.ladderWeight L γ δ (P S')
  let wj : Fin A.indexing.shape.m → ℝ := fun j => (gl K A P j).elim 1 W
  have hwj1 : ∀ j, 1 ≤ wj j := by
    intro j
    cases hg : gl K A P j with
    | none => simp [wj, hg]
    | some S' => simp only [wj, hg, Option.elim_some, W]; exact ladderWeight_ge_one L γ δ (P S') hL1 hδ0.le (hP0 S')
  let bP : Fin A.indexing.shape.m → ℝ := fun j => Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (wj j)⁻¹
  let gainJ : Fin A.indexing.shape.m → Prop := fun j => gl K A P j ≠ none
  have hP : ∀ r ∈ hRfin.toFinset, ∀ j,
      (if gainJ j then rungSet K A L w k0 r₀ β τ r j else rungSet0 K A L w k0 r₀ β τ j).Finite ∧
      ((if gainJ j then rungSet K A L w k0 r₀ β τ r j else rungSet0 K A L w k0 r₀ β τ j).ncard : ℝ) ≤ bP j := by
    intro r hr j
    obtain ⟨κr, hκr, hrr⟩ := hRfin.mem_toFinset.mp hr
    by_cases hgj : gainJ j
    · rw [if_pos hgj]
      obtain ⟨S', hg⟩ := Option.ne_none_iff_exists'.mp hgj
      obtain ⟨c, hdec, hc0, -, -, hsc, -⟩ := hT κr hκr
      obtain ⟨⟨h1, h2⟩, hs1, hz⟩ := gain_scale K hB hMol hM A P hg L hL0 w c κr hdec hc0 hsc
      have hnorm : ‖latticePoint L r‖ = ‖Molecule.gapAt L w κr K.x₁ K.x₂‖ := by
        rw [← hrr, ← gapAt_eq_lattice]
      have := rung_ncard_gain K A hpair hL0 w k0 r₀ β r (P S') h1 h2 (by rw [hnorm]; exact hs1) j hz
      rw [← hτdef] at this
      simpa only [bP, wj, hg, W, Option.elim_some] using this
    · rw [if_neg hgj]
      have hg : gl K A P j = none := not_not.mp hgj
      have := rung_ncard_nogain K A hpair hlog hτ w k0 r₀ β j
      rw [← hτdef] at this
      simpa only [bP, wj, hg, Option.elim_none, inv_one, mul_one] using this
  -- the fibre bound
  have fibre : ∀ (coreP : (Fin A.indexing.shape.n → Fin d → ℤ) → Prop) (U1 : ℝ),
      (∀ κ ∈ T, coreP (xint K A κ)) →
      (∀ r ∈ hRfin.toFinset, (Xset K A L w k0 r₀ β τ r gainJ coreP).Finite ∧
        ((Xset K A L w k0 r₀ β τ r gainJ coreP).ncard : ℝ) ≤ ((coverNum d : ℝ) * (2 * L + 1) ^ d) * (∏ j, bP j) * U1) →
      (K.restrS '' T).Finite ∧
      ((K.restrS '' T).ncard : ℝ) ≤
        hRfin.toFinset.card * (((coverNum d : ℝ) * (2 * L + 1) ^ d) * (∏ j, bP j) * U1) := by
    intro coreP U1 hcore hXb
    have hmem : ∀ κ ∈ T, xint K A κ ∈ Xset K A L w k0 r₀ β τ (rint K κ) gainJ coreP := by
      intro κ hκ
      obtain ⟨c, hdec, hc0, hres1, hres2, -, -⟩ := hT κ hκ
      refine ⟨near4_xint K A L w κ k0 r₀ hres2 (hballκ κ hκ) _, fun j => ?_, hcore κ hκ⟩
      have hm := rung_mem_pairSet K hB hMol hM A L γ δ w c κ hdec hc0 β hres1 hτ k0 r₀ hres2 (hballκ κ hκ) j
      by_cases hgj : gainJ j
      · rw [if_pos hgj]; exact hm
      · rw [if_neg hgj]; exact rungSet_sub_rungSet0 K A L w k0 r₀ β τ hτ (rint K κ) j hm
    refine ncard_fibre_bound hRfin.toFinset (fun r => Xset K A L w k0 r₀ β τ r gainJ coreP) _ hXb
      (K.restrS '' T) (fun κ' => (rint K κ', xint K A κ')) ?_ ?_
    · intro κ' hκ'
      obtain ⟨κ, hκ, rfl⟩ := hκ'
      refine ⟨?_, ?_⟩
      · show rint K (K.restrS κ) ∈ hRfin.toFinset
        rw [rint_restrS K hB]; exact hRfin.mem_toFinset.mpr ⟨κ, hκ, rfl⟩
      · show xint K A (K.restrS κ) ∈ Xset K A L w k0 r₀ β τ (rint K (K.restrS κ)) gainJ coreP
        have hxr : xint K A (K.restrS κ) = xint K A κ := funext (xint_restrS K hB A κ)
        rw [rint_restrS K hB, hxr]; exact hmem κ hκ
    · intro κ'₁ hκ'₁ κ'₂ hκ'₂ h
      obtain ⟨κ₁, hκ₁, rfl⟩ := hκ'₁
      obtain ⟨κ₂, hκ₂, rfl⟩ := hκ'₂
      have h1 : rint K (K.restrS κ₁) = rint K (K.restrS κ₂) := congrArg Prod.fst h
      have h2 : xint K A (K.restrS κ₁) = xint K A (K.restrS κ₂) := congrArg Prod.snd h
      rw [rint_restrS K hB, rint_restrS K hB] at h1
      have hx : ∀ i, xint K A κ₁ i = xint K A κ₂ i := by
        intro i
        have := congrFun h2 i
        rwa [xint_restrS K hB A, xint_restrS K hB A] at this
      obtain ⟨c₁, hd₁, hc₁, -, -, -, -⟩ := hT κ₁ hκ₁
      obtain ⟨c₂, hd₂, hc₂, -, -, -, -⟩ := hT κ₂ hκ₂
      exact restrS_eq_of_coords K hB hMol hM A hL0.ne' w c₁ c₂ κ₁ κ₂ hd₁ hd₂ hc₁ hc₂ hx h1
  -- common facts for the final assembly
  have hΛ1 := K.ladderProdVC_ge_one L γ δ P hL1 hδ0.le hP0
  have hΛW := ladderProdVC_le_gain K hB hM A P L γ δ hL1 hδ0.le hP0
  have hWp1 : 1 ≤ ∏ j, wj j := by
    calc (1 : ℝ) = ∏ _j : Fin A.indexing.shape.m, (1 : ℝ) := by simp
      _ ≤ ∏ j, wj j := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => hwj1 j)
  have hprod : ∏ j, bP j = (Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ A.indexing.shape.m * (∏ j, wj j)⁻¹ := by
    simp only [bP, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_inv_distrib]
    ring
  have hCpC : Cp ≤ max 1 (max Cp Ct) := (le_max_left _ _).trans (le_max_right _ _)
  have hCtC : Ct ≤ max 1 (max Cp Ct) := (le_max_right _ _).trans (le_max_right _ _)
  have hlogd : (Real.log L) ^ 4 * (∏ j, wj j) = Real.log L ^ 4 * ∏ j, (gl K A P j).elim 1 W := rfl
  by_cases hbad : X.IsBad = true
  · -- bad vine
    have hcard : K.C.atoms.card = 2 * A.indexing.shape.m + 2 := by
      have := card_atoms_eq K A; have := shape_n_bad K A hbad; omega
    have hfib := fibre (fun _ => True) 1 (fun _ _ => trivial)
      (fun r hr => xset_bound_bad K A hbad hL0 w k0 r₀ β τ r gainJ bP (hP r hr))
    apply encard_le_ofReal_of_ncard hfib.1
    refine hfib.2.trans ?_
    rw [hcard, hprod]
    exact assemble_bad (le_trans (by linarith [Real.add_one_le_exp 1]) hL1) hlog hδ0 hδ1 hCp0 (le_max_left _ _) hCpC
      (by positivity) hρ0 hρL (by positivity) hRcard hΛ1 hWp1 hΛW
  · have hn : X.IsBad = false := by simpa using hbad
    have hcard : K.C.atoms.card = 2 * A.indexing.shape.m + 5 := by
      have := card_atoms_eq K A; have := shape_n_normal K A hn; omega
    have hfib := fibre (fun x => (x (A.indexing.shape.uSlot hn 0), x (A.indexing.shape.uSlot hn 1),
        x (A.indexing.shape.uSlot hn 2)) ∈ TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2))
        A.coreLinear (-((A.coreFirstSign : ℤ) : ℝ) * β (av A (A.indexing.shape.uSlot hn 0)) / 2)
        (-((A.coreFirstSign : ℤ) : ℝ) * (if A.coreLinear then 1 else ((A.coreSign : ℤ) : ℝ)) *
          β (av A (A.indexing.shape.uSlot hn 1)) / 2) τ)
      (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))
      (fun κ hκ => by
        obtain ⟨c, hd, hc0, hres1, hres2, -, -⟩ := hT κ hκ
        exact core_mem_tripleSet K hB hMol hM A hn L γ δ w c κ hd hc0 β hres1 hτ k0 r₀ hres2 (hballκ κ hκ))
      (fun r hr => xset_bound_normal K A hn hL0 w k0 r₀ β τ r gainJ bP (hP r hr) _ _ _
        (htrip _ _ _ _ _ _))
    apply encard_le_ofReal_of_ncard hfib.1
    refine hfib.2.trans ?_
    rw [hcard, hprod]
    exact assemble_normal (le_trans (by linarith [Real.add_one_le_exp 1]) hL1) hlog hδ0 hδ1 hCp0 hCt0
      (le_max_left _ _) hCpC hCtC (by positivity) hρ0 hρL (by positivity) hRcard hΛ1 hWp1 hΛW

/-- **The vine label count `𝔉`** (DH23 L1799--L1801), single vine, in the form of `VineCountInput'`:
the labelSet of the decorations of `M` restricted by `(c, β, k⁰)` and `Adm`. -/
theorem vine_count_main (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) → Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (VCLadderScale K L w P) → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 2 → 1 ≤ ρ * L →
        (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
          ∃ r₀ : Mom d, ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ) →
        VineCountInput' K L γ δ ρ Cf C₂ w Adm P 4 := by
  obtain ⟨Cf, C₂, hCf, hC₂, h⟩ := vine_count_set hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hL⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hLL V D _ _ _ M K hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball => ?_⟩
  intro c β k0 hparam
  obtain ⟨r₀, hr₀⟩ := hball c β k0 hparam
  exact hL L hLL M K hMol hM hvine w P hP0 ρ hρ0 hρ2 hρL β k0 r₀ (decSet M L γ δ w Adm c β k0)
    (fun κ hκ => ⟨c, hκ.1, hparam.1, (fun v hv _ => hκ.2.1.1 v hv), hκ.2.1.2, hscale c κ hκ.1 hparam.1 hκ.2.2, hr₀ κ hκ⟩)

end WaveTurbulence.GammaLow.FinalCount.Step1
