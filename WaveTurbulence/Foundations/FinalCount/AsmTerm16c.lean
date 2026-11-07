/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm16b
public import WaveTurbulence.Foundations.FinalCount.AsmChain2
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 16c: `hterm` of `chain_cover` at base `0`** (`hterm_main`), with the ladder-gap clauses of the
components as the two named hypotheses `hmaxU`, `hmaxD` (discharged in `AsmMaxGap*`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u v

theorem hterm_main {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {Rn : ℕ} {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀}
        {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {Tm : V → Prop},
        SubHyp Rn M₀ → LadderHered M₀ P → (∀ S, 0 ≤ P S) →
        (∀ κ ∈ A0, SubproOblG C L γ η (0 : Mom d) κ) → TripleDesig C →
        (∀ κ ∈ A0, C.UnselOK L γ η (0 : Mom d) κ (Un κ)) →
        (∀ κ ∈ A0, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∀ k0 ∈ A0, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
        (∀ k0 ∈ A0, ∀ x, k0 (M₀.mate x) = k0 x) →
        (∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M₀.atom x = v → k0 x = k) →
        (∀ κ ∈ A0, ∀ a, crit a → SGat M₀ L γ η (0 : Mom d) κ a) →
        (((2 * M₀.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) →
        (∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), A ⊆ A0 → LCtx M₀ h.s → ∀ a : V,
          MaxLadderGapAdm (compMol h.s.M a) L (0 : Mom d) P (MoleProp.GapScale L) (compAdm h a (fun k => k ∈ A))) →
        (∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), A ⊆ A0 → LCtx M₀ h.s → ∀ a : V,
          MaxLadderGapAdm (compMol (h.op5 Tm).s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
            (compAdm (h.op5 Tm) a (fun k => k ∈ A))) →
        ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀),
          Inv4 M₀ Rn (Reach4 C Un Fst L γ η (0 : Mom d)) L (0 : Mom d) A0 A h →
          (∀ k ∈ A, NoBetaCut L (0 : Mom d) k h.s) →
          QS L γ δ C1 (0 : Mom d) P h A ≤
            WPot L γ η (L ^ (eraseA γ η * (Rn : ℝ) + 4 * η * ((Rn : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2)) (gExp η crit) h := by
  have hγ0 : 0 < γ := by linarith [hγ.1]
  have hγ1 : γ < 1 := hγ.2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hηd : η ≤ (d : ℝ) * η := by nlinarith
  have hg0 : gam0 γ ≤ γ := min_le_left _ _
  have hg0' : 0 < gam0 γ := lt_min hγ0 (by linarith)
  have hη1 : η ≤ gam0 γ / 1000 := le_trans hηd hsm
  have hη4 : η ≤ 1 / 4 := by linarith
  have hγη : 5 * η ≤ γ := by linarith
  have hC0η : (1 : ℝ) * η ^ 4 ≤ 1 := by
    have h1 : η ≤ 1 := by linarith
    have : η ^ 4 ≤ 1 := pow_le_one₀ hη.le h1
    linarith
  obtain ⟨Cu, hCu1, hUnt⟩ := unt_comp_bound.{v, u} hd hγ hη hsm hsm2 hηs
  obtain ⟨Cd, hCd1, hDam⟩ := dam_comp_bound.{v, u} hd ⟨hγ0, hγ1⟩ hη hsm hηs
  obtain ⟨Lf, hLf1, hFam⟩ := terminal_familyU.{u, v} (d := d) hd hγ0 hγ1 hη hη1 (C₀ := 1) zero_le_one hC0η
  refine ⟨max Cu Cd, le_trans hCu1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨Ru, hRu1, hUnt'⟩ := hUnt m C1 (le_trans (le_max_left _ _) hC1) δ hδ
  obtain ⟨Rd, hRd1, hDam'⟩ := hDam m C1 (le_trans (le_max_right _ _) hC1) δ hδ
  refine ⟨max Ru (max Rd (max Lf (Real.exp 1))), le_trans hRu1 (le_max_left _ _), fun L hL => ?_⟩
  have hLu : Ru ≤ L := le_trans (le_max_left _ _) hL
  have hLd : Rd ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLf : Lf ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  intro V _ _ D₀ _ _ M₀ Rn P A0 C Un Fst crit Tm hS hP hP0 hobl hT3 hU hdeg h0 hTame hmate hfix hcrit hcard hmaxU hmaxD A h hA hn
  by_cases hAe : A = ∅
  · subst hAe; simp [QS_empty]
  obtain ⟨κ₀, hκ₀⟩ := Set.nonempty_iff_ne_empty.2 hAe
  obtain ⟨hA0, h2⟩ := hA
  rcases h2 with he | ⟨hc, hap, hr⟩
  · exact absurd he hAe
  have hLC : LCtx M₀ h.s := LCtx.of_inv hc.good.1 ⟨h.anc, hc.anc⟩ hc.rel
  have hRun : RunDataN L γ η M₀ h (fun k => k ∈ A) := fun κ hκ =>
    ⟨C, Un κ, hobl κ (hA0 hκ), hT3, hU κ (hA0 hκ), (hr κ hκ).toRunNC (hn κ hκ)⟩
  have hCon : Prop95ConclN L γ η (0 : Mom d) κ₀ Tm Rn h :=
    (hr κ₀ hκ₀).toRunNC (hn κ₀ hκ₀) |>.toHRunN.prop95N hS (hobl κ₀ (hA0 hκ₀)) hT3 (hdeg κ₀ (hA0 hκ₀)) (h0 κ₀ (hA0 hκ₀))
  have hst := hCon.struct
  have hlab : ∀ v ∈ h.s.M.atoms, ∀ ρ kp, h.s.cls v = .alpha ρ kp → L⁻¹ ≤ ρ ∧ ρ ≤ L ^ (-γ + η) ∧ (kp = 0 ∨ kp = 50) :=
    fun v hv ρ kp hc' => by
      obtain ⟨hl, hk, -⟩ := hCon.label v hv ρ kp hc'
      exact ⟨hl.2.1, hl.2.2, hk⟩
  have hdpos : ∀ a ∈ h.s.M.atoms, 1 ≤ h.s.M.deg a := fun a ha => (hst.deg_range a ha).1
  have hM4 : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => (hst.deg_range a ha).2
  have hcrit0 : critCount crit h.s = 0 := by
    unfold critCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha ⟨hε, hca⟩
    obtain ⟨h₁, h₂, h₃, -, -, -, -, -, hsg, g⟩ := hr κ₀ hκ₀
    obtain ⟨-, hε3⟩ := HRunN.eps_back g a ha hε
    exact hsg a (HRunN.eps_back g a ha hε).1 hε3 (hcrit κ₀ (hA0 hκ₀) a hca)
  obtain ⟨𝒦, j, Rs, h1, hcl, hrk, hR, hQ⟩ := hFam L hLf C1 δ (le_trans hCu1 (le_trans (le_max_left _ _) hC1)) hδ.1 hδ.2
    hP hP0 hLC (fun k0 hk0 => hTame k0 (hA0 hk0)) (fun k0 hk0 => hmate k0 (hA0 hk0))
    (fun v hv hT hd4 => by
      obtain ⟨k, hk⟩ := hfix v hv hT hd4
      exact ⟨k, fun k0 hk0 => hk k0 (hA0 hk0)⟩) hCon.noloop hM4 hdpos
  have hcardh : (h.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by exact_mod_cast UCtx.card_atoms_le hS hc) hcard
  refine hterm_core (C₀ := 1) hL1 hg0'.le hη hη4 hγη le_rfl hc.good hst hS.one_le hcrit0 hlab hdpos hM4 hcl h1 hrk hR hQ ?_
  intro a ha
  have ha5 := hR.mem a ha
  by_cases hu : UntC h Tm Rn a
  · exact hUnt' L hLu hS hRun (fun κ hκ => hdeg κ (hA0 hκ)) (fun κ hκ => h0 κ (hA0 hκ)) ⟨κ₀, hκ₀⟩ hP0 hcardh ha5 hu
      (hmaxU A h hA0 hLC a)
  · exact hDam' L hLd hS hRun (fun κ hκ => hdeg κ (hA0 hκ)) (fun κ hκ => h0 κ (hA0 hκ)) ⟨κ₀, hκ₀⟩ hP0 hcardh hc.good ha5 hu
      (hmaxD A h hA0 hLC a)

end WaveTurbulence.FinalCountAsm
