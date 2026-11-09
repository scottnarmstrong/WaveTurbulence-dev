/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenLoopMain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): the garden-level LOW bound for gardens with a loop.**

`LowGardenBoundLoop` (conditional helper, distinct name): `LowGardenBound` for gardens with at least two atoms and a loop.
`lowGardenLoop_of_molecule2`: `LowMoleculeBound2` gives it, by `countA_unloop_le` (GL17), `lowClassHyps2_unloop` on `M.unloop`
(index `R + k`) and the numerics `loop_gain_le`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp WaveTurbulence.Mole WaveTurbulence.VineCount

/-- `LowGardenBound` restricted to the gardens with at least two atoms and a loop (conditional helper, distinct name). -/
def LowGardenBoundLoop (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → G.Irreducible → IsBalancedSig G.sig → 1 ≤ G.order →
      1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c → ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ (D : SplicedKernelData G d) (C : Src.CountingChoices Src.γL G d), D.hinges = C.subpro.hinges → Src.CountingGeometry G C →
      ¬ RegGeom G → (2 ≤ G.molecule.atoms.card ∧ ∃ x, G.molecule.atom x = G.molecule.atom (G.molecule.mate x)) →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

theorem lowGardenLoop_of_molecule2 {d : ℕ} {γ η : ℝ} (hLM : LowMoleculeBound2 d γ η) : LowGardenBoundLoop d γ η := by
  obtain ⟨Cs, hCs, hmol⟩ := hLM
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁, hb⟩ := hmol m (max c m + 1) C1 hC1 δ hδ
  refine ⟨max R₁ (Real.exp 1), le_trans hR₁ (le_max_left _ _),
    fun L hL R G hp hirr hbal hord hR hRc hordm D C hD hg hnreg hloop base roots Adm hA => ?_⟩
  obtain ⟨h2a, x0, hx0⟩ := hloop
  have hLa : R₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans hR₁ hLa
  have hL0 : 0 < L := by linarith
  have hC1' : 1 ≤ C1 := by linarith
  have hC10 : 0 ≤ C1 := by linarith
  by_cases hne : ∃ κ, Adm κ
  swap
  · push Not at hne
    have h0 := countA_union_le G.molecule L γ δ C1 base (∅ : Finset Bool) (Adm := Adm) (fun _ _ => True)
      (fun κ hκ => absurd hκ (hne κ)) C.ladderScale
    simp only [Finset.sum_empty] at h0
    exact h0.trans bot_le
  obtain ⟨κ0, hκ0⟩ := hne
  set M := inlMol G.molecule with hMdef
  have hS : SubHypLoop R M := subHypLoop_mapAtoms (inlEmb _) (subHypLoop_of_geometry hg hR h2a)
  have hb4 : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hS.bounds a ha)
  have hx0' : M.atom x0 = M.atom (M.mate x0) := by
    simp only [hMdef, mapAtoms_atom, mapAtoms_mate, inlEmb_apply, Sum.inl.injEq]; exact hx0
  have hy : ∃ y, M.out y = true ∧ M.atom y = M.atom (M.mate y) := by
    by_cases ho : M.out x0 = true
    · exact ⟨x0, ho, hx0'⟩
    · refine ⟨M.mate x0, ?_, ?_⟩
      · have := M.out_mate x0
        have ho' : M.out x0 = false := by simpa using ho
        simpa [ho'] using this
      · rw [M.mate_mate]; exact hx0'.symm
  have hkpos : 0 < M.loopBonds.card := by
    obtain ⟨y, hy1, hy2⟩ := hy
    exact Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨by simp [Molecule.bonds, hy1], hy2⟩⟩
  set k := M.loopBonds.card with hk
  have hdet := inl_loop_det hp hg hD hA
  have hcard : ((2 * M.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m := by
    rw [hMdef, inlMol_atoms, Finset.card_map, hg.atom_count]; exact hordm
  have hD0 := lowLoopData_garden hp hR hD hg h2a hL0 hA ⟨κ0, hκ0⟩ m hcard
  have hSU : SubHypL (R + k) M.unloop := hS.unloop
  -- the omitted vines on `M.unloop`
  let Un' : (NonLoop M → Fin d → ℤ) → Set (Src.Object Src.γL M.unloop) := fun κ' =>
    if h : ∃ κ, Adm κ ∧ κ' = fun y : NonLoop M => κ y.1 then unloopSet M (Un0 C L γ η (Classical.choose h)) else ∅
  have hUn' : ∀ κ, Adm κ → Un' (fun y : NonLoop M => κ y.1) = unloopSet M (Un0 C L γ η κ) := by
    intro κ hκ
    have h : ∃ κ₂, Adm κ₂ ∧ (fun y : NonLoop M => κ y.1) = fun y : NonLoop M => κ₂ y.1 := ⟨κ, hκ, rfl⟩
    have hch : Classical.choose h = κ := by
      obtain ⟨h1, h2⟩ := Classical.choose_spec h
      exact hdet _ _ h1 hκ (fun x hx => (congrFun h2 ⟨x, hx⟩).symm)
    simp only [Un', h, ↓reduceDIte, hch]
  have hkF : (kFix0 C base).card ≤ 2 * (R + k) :=
    (Finset.card_image_le.trans hg.fixedRoots_card).trans (by omega)
  have hmate' : ∀ κ', unloopAdm M Adm κ' → ∀ x, κ' (M.unloop.mate x) = κ' x := by
    rintro κ' ⟨κ, hκ, rfl⟩ x
    exact hD0.hmate κ hκ x.1
  have hT2 : 2 ≤ 1 + Real.log L := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) hLe
    rw [Real.log_exp] at h1; linarith
  have hT1 : 1 ≤ 1 + Real.log L := by linarith
  have hkle : (k : ℝ) ≤ (1 + Real.log L) ^ m := by
    have h1 : k ≤ M.bonds.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := hS.count
    have h3 : k ≤ 2 * M.atoms.card := by omega
    refine le_trans ?_ hcard
    exact_mod_cast h3
  have hRk : (((R + k : ℕ)) : ℝ) ≤ (1 + Real.log L) ^ (max c m + 1) := by
    have h1 : (1 + Real.log L) ^ c ≤ (1 + Real.log L) ^ (max c m) := pow_le_pow_right₀ hT1 (le_max_left _ _)
    have h2 : (1 + Real.log L) ^ m ≤ (1 + Real.log L) ^ (max c m) := pow_le_pow_right₀ hT1 (le_max_right _ _)
    have h3 : 0 ≤ (1 + Real.log L) ^ (max c m) := by positivity
    push_cast
    calc (R : ℝ) + k ≤ 2 * (1 + Real.log L) ^ (max c m) := by linarith
      _ ≤ (1 + Real.log L) * (1 + Real.log L) ^ (max c m) := by nlinarith
      _ = _ := by rw [pow_succ']
  have hclass : ∀ lab ∈ labelSet M.unloop (kFix0 C base),
      (∃ κ, unloopAdm M Adm κ ∧ InClass M.unloop L (0 : Mom d) (kFix0 C base) lab.1 lab.2 κ) →
      LowClassHyps2 (d := d) M.unloop (R + k) (heredScale' M.unloop (scaleMap (inlEmb _) C.ladderScale))
        {κ | unloopAdm M Adm κ ∧ InClass M.unloop L (0 : Mom d) (kFix0 C base) lab.1 lab.2 κ} (C0 C).unloop Un'
        (unloopSet M (Fst0 C)) (critMap (inlEmb _) C) (fun v => v ∈ lab.1) L γ η m :=
    fun lab _ hne' => lowClassHyps2_unloop hD0 hkpos hL0.ne' hUn' lab hne'
  have hres := hb L hLa (M₀ := M.unloop) (Rn := R + k) (P := heredScale' M.unloop (scaleMap (inlEmb _) C.ladderScale))
    (Adm := unloopAdm M Adm) (C := (C0 C).unloop) (Un := Un') (Fst := unloopSet M (Fst0 C)) (crit := critMap (inlEmb _) C)
    (kFix0 C base) hSU hkF hRk hmate' hclass
  have ecrit : (M.unloop.atoms.filter (critMap (inlEmb _) C)).card = C.numCriticalSG := (numCriticalSG_eq (inlEmb _) C).symm
  have erho : M.rho = G.molecule.rho := rho_inl G.molecule
  rw [unloop_rho, erho, ecrit] at hres
  have hP0' : ∀ S ∈ M.unloop.maximalLadders, 0 ≤ scaleMap (inlEmb _) C.ladderScale S := by
    rw [unloop_maximalLadders]; exact hD0.hP0
  have hc : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hδ' : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1'
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul this hδ' (Real.rpow_nonneg hδ.1.le _) zero_le_one
      _ = 1 := one_mul 1
  have hc0 : 0 ≤ C1⁻¹ * δ ^ (1 / 2 : ℝ) := mul_nonneg (inv_nonneg.2 hC10) (Real.rpow_nonneg hδ.1.le _)
  have hexp : (((R + k : ℕ) : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) =
      ((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) + k * (((d : ℝ) - γ) - (1 / 4 + 1 / 40)) := by
    push_cast; ring
  rw [hexp] at hres
  calc G.molecule.countA L γ δ C1 base Adm C.ladderScale
      = G.molecule.countA L γ δ C1 0 Adm C.ladderScale := countA_base_eq_of_molecule G.molecule hg.molecule L γ δ C1 base 0 Adm _
    _ = M.countA L γ δ C1 0 Adm (scaleMap (inlEmb _) C.ladderScale) := (countA_inl_scale G.molecule L γ δ C1 0 Adm C.ladderScale).symm
    _ ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
          M.unloop.countA L γ δ C1 0 (unloopAdm M Adm) (scaleMap (inlEmb _) C.ladderScale) :=
        countA_unloop_le M hb4 L γ δ C1 hL0 (by linarith) hδ.1 0 Adm hdet _
    _ ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
          M.unloop.countA L γ δ C1 0 (unloopAdm M Adm) (heredScale' M.unloop (scaleMap (inlEmb _) C.ladderScale)) := by
        gcongr
        exact countA_le_hered M.unloop L γ δ C1 0 _ hL0 hδ.1.le hC10 hP0'
    _ ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
          ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ))) *
            L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) + k * (((d : ℝ) - γ) - (1 / 4 + 1 / 40)))) := by
        gcongr
    _ = ENNReal.ofReal (_ * _) := (ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (Real.rpow_nonneg hL0.le _) hc0) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (loop_gain_le hL1 hc0 hc (by norm_num))

end WaveTurbulence.GammaLow.FinalCount.H
