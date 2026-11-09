/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew3
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCNew5`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 27 (session 4): **the single-vine label count for an Operation 1 that creates a new component**
(TARGET excessprop1 (2), L2169--L2177), of a charted vine (main: from `VINEPARAM`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- **A label vector of the new-component count.** As `GoodLabel`, but the gap `k_{x₁} - k_{x₂}` equals the fixed
vector `n₀` (TARGET L2174: "`k_{ℓ₁} ± k_{ℓ₂}` equals a fixed constant") and the lower-joint energy
`|k_{y₂}|² - |k_{y₁}|²` lies in a fixed interval `[e₀ - ντ, e₀ + ντ]`, `τ = δ⁻¹L^{-2γ}`, `ν = n_sb` (L2174: "fixed interval of
length at most `n_sb δ⁻¹ L^{-2γ}`"). -/
def GoodLabelN {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M)
    (L γ δ ν : ℝ) (w : Mom d) (P : Finset V → ℝ) (β : V → ℝ) (k0 : D → Mom d) (n₀ : Fin d → ℤ) (e₀ : ℝ)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ c : V → Mom d, M.IsDecoration L w c κ ∧ (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) ∧
    (∀ v ∈ M.atoms, M.deg v = 4 → |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ)) ∧
    (∀ x, ‖Molecule.kvec L w κ x - k0 x‖ ≤ 1) ∧ VCLadderScale K L w P κ ∧
    rint K κ = n₀ ∧ |lowerG K L w κ - e₀| ≤ ν * δ⁻¹ * L ^ (-2 * γ)

/-- **The new-component vine label count** (TARGET L2174--L2177), charted single vine (main: from `VINEPARAM`): at most `vineFN` label
vectors (`e = 4`). -/
theorem vine_count_set_new (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ ν : ℝ, 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) → Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        ∀ (β : V → ℝ) (k0 : D → Mom d) (n₀ : Fin d → ℤ) (e₀ : ℝ) (T : Set (D → (Fin d → ℤ))), n₀ ≠ 0 →
        (∀ κ ∈ T, GoodLabelN M K L γ δ ν w P β k0 n₀ e₀ κ) →
        (K.restrS '' T).encard ≤
          ENNReal.ofReal (vineFN d L γ δ ν Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card 4) := by
  obtain ⟨Cp, hCp0, hCp⟩ := pairSet_count hd hγ (c₀ := 8) (by norm_num)
  obtain ⟨Ct, hCt0, hCt⟩ := tripleSet_count hd hγ
  obtain ⟨Cs, L₀s, hCs0, hL₀s1, hslab⟩ := slab_count hd hγ
  refine ⟨(coverNum d : ℝ) * Cs, max 1 (max Cp Ct), mul_nonneg (Nat.cast_nonneg _) hCs0, le_max_left _ _, ?_⟩
  intro δ hδ
  obtain ⟨L₀p, hL₀p⟩ := hCp δ hδ
  obtain ⟨L₀t, hL₀t⟩ := hCt δ hδ
  refine ⟨max (max (max L₀p L₀t) L₀s) (Real.exp 1), le_max_right _ _, ?_⟩
  intro L hL ν hν V D _ _ _ M K hMol hM hvine w P hP0 β k0 n₀ e₀ T hn₀ hT
  have hLp : L ≥ L₀p := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hL
  have hLt : L ≥ L₀t := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hL
  have hLs : L ≥ L₀s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
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
  set r₀ : Mom d := latticePoint L n₀ with hr₀def
  have hballκ : ∀ κ ∈ T, ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ 2 := by
    intro κ hκ
    obtain ⟨c, -, -, -, -, -, hrint, -⟩ := hT κ hκ
    rw [gapAt_eq_lattice, hrint, hr₀def, sub_self, norm_zero]; norm_num
  -- the joint slab
  let β' : ℝ := -e₀ + ‖w‖ ^ 2 - ‖w - latticePoint L n₀‖ ^ 2
  let Bs : Set (Fin d → ℤ) := slabSet L (cenI K A w k0 r₀ A.indexing.shape.x0) n₀ β' (ν * δ⁻¹ * L ^ (-2 * γ))
  obtain ⟨hBfin, hBcard⟩ := hslab L hLs δ hδ ν hν n₀ hn₀ (cenI K A w k0 r₀ A.indexing.shape.x0) β'
  have hL1' : 1 ≤ L := le_trans hL₀s1 hLs
  -- weights
  let W : Finset V → ℝ := fun S' => Molecule.ladderWeight L γ δ (P S')
  let wj : Fin A.indexing.shape.m → ℝ := fun j => (gl K A P j).elim 1 W
  have hwj1 : ∀ j, 1 ≤ wj j := by
    intro j
    cases hg : gl K A P j with
    | none => simp [wj, hg]
    | some S' => simp only [wj, hg, Option.elim_some, W]; exact ladderWeight_ge_one L γ δ (P S') (le_trans (le_max_right _ _) hL) hδ0.le (hP0 S')
  let bP : Fin A.indexing.shape.m → ℝ := fun j => Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (wj j)⁻¹
  let gainJ : Fin A.indexing.shape.m → Prop := fun j => gl K A P j ≠ none
  obtain ⟨_, κ₀, hκ₀T, -⟩ := hne
  have hP : ∀ r ∈ ({n₀} : Finset (Fin d → ℤ)), ∀ j,
      (if gainJ j then rungSet K A L w k0 r₀ β τ r j else rungSet0 K A L w k0 r₀ β τ j).Finite ∧
      ((if gainJ j then rungSet K A L w k0 r₀ β τ r j else rungSet0 K A L w k0 r₀ β τ j).ncard : ℝ) ≤ bP j := by
    intro r hr j
    have hrn : r = n₀ := Finset.mem_singleton.mp hr
    by_cases hgj : gainJ j
    · rw [if_pos hgj]
      obtain ⟨S', hg⟩ := Option.ne_none_iff_exists'.mp hgj
      obtain ⟨c, hdec, hc0, -, -, hsc, hrint, -⟩ := hT κ₀ hκ₀T
      obtain ⟨⟨h1, h2⟩, hs1, hz⟩ := gain_scale K hB hMol hM A P hg L hL0 w c κ₀ hdec hc0 hsc
      have hnorm : ‖latticePoint L r‖ = ‖Molecule.gapAt L w κ₀ K.x₁ K.x₂‖ := by
        rw [hrn, ← hrint, ← gapAt_eq_lattice]
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
      (∀ r ∈ ({n₀} : Finset (Fin d → ℤ)), (XsetB K A L w k0 r₀ β τ r gainJ coreP Bs).Finite ∧
        ((XsetB K A L w k0 r₀ β τ r gainJ coreP Bs).ncard : ℝ) ≤
          ((coverNum d : ℝ) * Cs * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ))) * (∏ j, bP j) * U1) →
      (K.restrS '' T).Finite ∧
      ((K.restrS '' T).ncard : ℝ) ≤
        ({n₀} : Finset (Fin d → ℤ)).card * (((coverNum d : ℝ) * Cs * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ))) *
          (∏ j, bP j) * U1) := by
    intro coreP U1 hcore hXb
    have hmem : ∀ κ ∈ T, xint K A κ ∈ XsetB K A L w k0 r₀ β τ (rint K κ) gainJ coreP Bs := by
      intro κ hκ
      obtain ⟨c, hdec, hc0, hres1, hres2, -, hrint, hG⟩ := hT κ hκ
      refine ⟨⟨near4_xint K A L w κ k0 r₀ hres2 (hballκ κ hκ) _, ?_⟩, fun j => ?_, hcore κ hκ⟩
      · have hph := x0_phase K hB hMol hM A L w c κ hdec hc0
        rw [hrint] at hph
        have e : 2 * inner ℝ (latticePoint L n₀) (latticePoint L (xint K A κ A.indexing.shape.x0)) - β' =
            -(lowerG K L w κ - e₀) := by
          rw [hph]; simp only [β']; ring
        rw [e, abs_neg]; exact hG
      · have hm := rung_mem_pairSet K hB hMol hM A L γ δ w c κ hdec hc0 β hres1 hτ k0 r₀ hres2 (hballκ κ hκ) j
        by_cases hgj : gainJ j
        · rw [if_pos hgj]; exact hm
        · rw [if_neg hgj]; exact rungSet_sub_rungSet0 K A L w k0 r₀ β τ hτ (rint K κ) j hm
    refine ncard_fibre_bound ({n₀} : Finset (Fin d → ℤ)) (fun r => XsetB K A L w k0 r₀ β τ r gainJ coreP Bs) _ hXb
      (K.restrS '' T) (fun κ' => (rint K κ', xint K A κ')) ?_ ?_
    · intro κ' hκ'
      obtain ⟨κ, hκ, rfl⟩ := hκ'
      obtain ⟨c, hdec, hc0, hres1, hres2, -, hrint, hG⟩ := hT κ hκ
      refine ⟨?_, ?_⟩
      · show rint K (K.restrS κ) ∈ ({n₀} : Finset (Fin d → ℤ))
        rw [rint_restrS K hB, hrint]; exact Finset.mem_singleton_self _
      · show xint K A (K.restrS κ) ∈ XsetB K A L w k0 r₀ β τ (rint K (K.restrS κ)) gainJ coreP Bs
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
      obtain ⟨c₁, hd₁, hc₁, -, -, -, -, -⟩ := hT κ₁ hκ₁
      obtain ⟨c₂, hd₂, hc₂, -, -, -, -, -⟩ := hT κ₂ hκ₂
      exact restrS_eq_of_coords K hB hMol hM A hL0.ne' w c₁ c₂ κ₁ κ₂ hd₁ hd₂ hc₁ hc₂ hx h1
  -- common facts for the final assembly
  have hΛ1 := K.ladderProdVC_ge_one L γ δ P (le_trans (le_max_right _ _) hL) hδ0.le hP0
  have hΛW := ladderProdVC_le_gain K hB hM A P L γ δ (le_trans (le_max_right _ _) hL) hδ0.le hP0
  have hWp1 : 1 ≤ ∏ j, wj j := by
    calc (1 : ℝ) = ∏ _j : Fin A.indexing.shape.m, (1 : ℝ) := by simp
      _ ≤ ∏ j, wj j := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => hwj1 j)
  have hprod : ∏ j, bP j = (Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ A.indexing.shape.m * (∏ j, wj j)⁻¹ := by
    simp only [bP, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_inv_distrib]
    ring
  have hCpC : Cp ≤ max 1 (max Cp Ct) := (le_max_left _ _).trans (le_max_right _ _)
  have hCtC : Ct ≤ max 1 (max Cp Ct) := (le_max_right _ _).trans (le_max_right _ _)
  have hBq : 0 ≤ (coverNum d : ℝ) * Cs * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) := by
    have : 0 < ν := by linarith
    positivity
  by_cases hbad : X.IsBad = true
  · have hcard : K.C.atoms.card = 2 * A.indexing.shape.m + 2 := by
      have := card_atoms_eq K A; have := shape_n_bad K A hbad; omega
    have hfib := fibre (fun _ => True) 1 (fun _ _ => trivial)
      (fun r hr => by
        have := xsetB_bound_bad K A hbad L w k0 r₀ β τ r gainJ bP (hP r hr) Bs hBfin _ hBcard
        exact this)
    apply encard_le_ofReal_of_ncard hfib.1
    refine hfib.2.trans ?_
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    rw [hprod]
    have := assemble_bad_new (m := A.indexing.shape.m) (d := d) (γ := γ) (Cp := Cp) (C₂ := max 1 (max Cp Ct))
      hL1' hlog hδ0 hδ1 hCp0 (le_max_left _ _) hCpC hBq hΛ1 hWp1 hΛW
    refine this.trans (le_of_eq ?_)
    rw [hcard]; unfold vineFN; ring
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
        obtain ⟨c, hd, hc0, hres1, hres2, -, -, -⟩ := hT κ hκ
        exact core_mem_tripleSet K hB hMol hM A hn L γ δ w c κ hd hc0 β hres1 hτ k0 r₀ hres2 (hballκ κ hκ))
      (fun r hr => xsetB_bound_normal K A hn L w k0 r₀ β τ r gainJ bP (hP r hr) _ _ _
        (htrip _ _ _ _ _ _) Bs hBfin _ hBcard)
    apply encard_le_ofReal_of_ncard hfib.1
    refine hfib.2.trans ?_
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    rw [hprod]
    have := assemble_normal_new (m := A.indexing.shape.m) (d := d) (γ := γ) (Cp := Cp) (Ct := Ct)
      (C₂ := max 1 (max Cp Ct)) hL1' hlog hδ0 hδ1 hCp0 hCt0 (le_max_left _ _) hCpC hCtC hBq hΛ1 hWp1 hΛW
    refine this.trans (le_of_eq ?_)
    rw [hcard]; unfold vineFN; ring

end WaveTurbulence.GammaLow.FinalCount.Step1
