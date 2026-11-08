/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKCrude.Weights
public import WaveTurbulence.Foundations.Flower.LadFilt.Defs
public import WaveTurbulence.Foundations.Spine.CoarseSpliced.Final2
public import WaveTurbulence.Foundations.FlowerTop.Port.CoarseFinal1ST

/-! # C2 FINALMK-CRUDE: the coarse estimate with pins, filters and indicators at fixed parameters

Copy-thread of Port's `coarse_fixedST` (itself a copy-thread of main's `coarse_fixed`), with:
- general pins `fix` (`⊆ split`), the selection of ladders at `D.hinges ∪ split` (`selection_claim`);
- the filters of the ladder atoms handled by C3's `LadderL1AtFilt` (unfiltered ladder atoms get a fixed bump `ψ₀`
  with `R_a ≥ max_{T₀} |Ω_a|`; its cost `max 1 (𝔟 ψ₀)` goes into `C₁`);
- the non-ladder filters and the indicator have modulus `≤ 1` and are constant along a class. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKCrude
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.CoarseSpliced
  WaveTurbulence.FlowerP5 Finset MeasureTheory Set
open WaveTurbulence.Flower.MkDefs (SplicedKernelDataMK splicedKernelMK splicedTimeIntegralMK)
open WaveTurbulence.Flower.LadFilt (LadderL1AtFilt filterB)
open WaveTurbulence.Flower.FinalMKDefs (AtomOK CoarseSplicedAtMK SplicedGeomPremises)
open scoped Classical

variable {w d : ℕ} {G : Garden w}

/-- The filter profile used on the ladder: the given one, or the fixed bump. -/
noncomputable def psiOf (D : SplicedKernelDataMK G d) (ψ₀ : SchwartzMap ℝ ℂ) (a : GBranch G.tree) :
    SchwartzMap ℝ ℂ := (D.filt a).elim ψ₀ fun q => q.2

/-- The scale used on the ladder: the given one, or `R0 a`. -/
noncomputable def RvOf (D : SplicedKernelDataMK G d) (R0 : GBranch G.tree → ℝ) (a : GBranch G.tree) : ℝ :=
  (D.filt a).elim (R0 a) fun q => q.1

theorem ladW_eq_psi (D : SplicedKernelDataMK G d) (ψ₀ : SchwartzMap ℝ ℂ) (hψ₀ : ∀ x : ℝ, |x| ≤ 1 → ψ₀ x = 1)
    (S : Finset (GBranch G.tree)) (L : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (R0 : GBranch G.tree → ℝ)
    (hR : ∀ a ∈ S, 0 < R0 a ∧ |omegaNode G (cosetDecoration G L base z) a| ≤ R0 a) :
    ladW D S L base z = ∏ a ∈ S, psiOf D ψ₀ a (omegaNode G (cosetDecoration G L base z) a / RvOf D R0 a) := by
  unfold ladW
  refine Finset.prod_congr rfl (fun a ha => ?_)
  unfold filtFac psiOf RvOf
  cases h : D.filt a with
  | some q => rfl
  | none =>
    obtain ⟨h0, h1⟩ := hR a ha
    simp only [Option.elim]
    rw [hψ₀]
    rw [abs_div, abs_of_pos h0, div_le_one h0]
    exact h1

theorem filterB_psiOf_le (D : SplicedKernelDataMK G d) (ψ₀ : SchwartzMap ℝ ℂ) (cθ : ℝ) (hcθ : 1 ≤ cθ)
    (hq : ∀ a q, D.filt a = some q → filterB ⇑q.2 ≤ cθ) (a : GBranch G.tree) :
    max 1 (filterB ⇑(psiOf D ψ₀ a)) ≤ cθ * max 1 (filterB ⇑ψ₀) := by
  have hcb : 1 ≤ max 1 (filterB ⇑ψ₀) := le_max_left _ _
  unfold psiOf
  cases h : D.filt a with
  | none =>
    simp only [Option.elim]
    nlinarith
  | some q =>
    simp only [Option.elim]
    have := hq a q h
    exact max_le (by nlinarith) (by nlinarith)

/-- **The coarse spliced estimate with pins, filters and indicators, at fixed parameters.** -/
theorem coarse_fixedMK (Pg : WTParams) (hd : 3 ≤ Pg.d) (hγ0 : 0 < Pg.γ) (hγ1 : Pg.γ < 1)
    (hη0 : 0 < Pg.η) (hx : 4 * Pg.η ≤ Pg.gamma1 - Real.sqrt Pg.η) (hη1 : Pg.η ≤ 1)
    (hδ0 : 0 < Pg.δ) (hδ1 : Pg.δ ≤ 1) (hL : 1 ≤ Pg.L) (hC : 1 ≤ Pg.C₁)
    (ψ₀ : SchwartzMap ℝ ℂ) (hψ₀ : ∀ x : ℝ, |x| ≤ 1 → ψ₀ x = 1)
    (hgate : LadderL1AtFilt Pg) :
    CoarseSplicedAtMK { Pg with C₁ := Pg.C₁ * max 1 (filterB ⇑ψ₀) ^ 2 * 3 ^ (2 * Pg.d), C₂ := 1 } := by
  set cb : ℝ := max 1 (filterB ⇑ψ₀) with hcbdef
  have hcb1 : 1 ≤ cb := le_max_left _ _
  intro p hp R hR1 hR2 G hplain hirr hbal hord1 hord2 D split cθ hcθ hD hlayers hok hfixs A base roots hprem
  have hR2' : R ≤ 10 * Pg.R (p + 1) := by
    have := R_congr { Pg with C₁ := Pg.C₁ * cb ^ 2 * 3 ^ (2 * Pg.d), C₂ := 1 } Pg rfl rfl rfl (p + 1)
    rw [← this]; exact hR2
  have hord2' : G.order ≤ Pg.N (p + 1) ^ 4 := by
    have := N_congr { Pg with C₁ := Pg.C₁ * cb ^ 2 * 3 ^ (2 * Pg.d), C₂ := 1 } Pg rfl rfl rfl (p + 1)
    rw [← this]; exact hord2
  have hL0 : 0 < Pg.L := by linarith
  obtain ⟨F, hSA, hSB, hSC⟩ := selection_claim G D.layer (D.hinges ∪ split) hprem.molecule hprem.connected
    hprem.atom_count ⟨A.length, A.upper, A.lower, A.ladder, A.atoms⟩
  set S : F.ι → Finset (GBranch G.tree) := fun i => Molecule.ladderAtoms (F.u i) (F.v i) with hSdef
  have hS : ∀ i j, i ≠ j → Disjoint (S i) (S j) := F.disj
  have hH : ∀ i, Disjoint (S i) D.hinges := fun i => (Finset.disjoint_union_right.mp (F.hing i)).1
  have hHs : ∀ i, Disjoint (S i) split := fun i => (Finset.disjoint_union_right.mp (F.hing i)).2
  have hfree : ∀ i, ∀ v ∈ S i, D.fix v = none := by
    intro i v hv
    by_contra hne
    exact Finset.disjoint_left.mp (hHs i) hv (hfixs v (Option.isSome_iff_ne_none.mpr hne))
  have hsplit : ∀ a ∈ split, a ∉ Uni S := by
    intro a ha hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
    exact Finset.disjoint_left.mp (hHs i) hi ha
  have hcoup : 0 < ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ := by
    unfold coupling
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_pos.mpr (by positivity)
  have hcoupv : ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ = Pg.δ / (2 * Pg.L ^ ((Pg.d : ℝ) - Pg.γ)) := by
    unfold coupling
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  -- ladder facts
  have hm1 : ∀ i, 1 ≤ F.m i := fun i => (F.ladder i).1
  have hcardS : ∀ i, (S i).card = 2 * F.m i + 2 := fun i => card_ladderAtoms_ladder (F.ladder i)
  have hsubS : ∀ i, S i ⊆ G.molecule.atoms := fun i => ladderAtoms_subset_atoms (F.ladder i)
  have hTle : ∑ i, (2 * F.m i + 2) ≤ G.order := by
    rw [← hprem.atom_count]
    calc ∑ i, (2 * F.m i + 2) = ∑ i, (S i).card := Finset.sum_congr rfl (fun i _ => (hcardS i).symm)
      _ = (Finset.univ.biUnion S).card := by
        rw [Finset.card_biUnion]
        intro i _ j _ hij
        exact hS i j hij
      _ ≤ G.molecule.atoms.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
        exact hsubS i hi
  have hkk : ∀ i, 4 * F.m i + 2 ≤ (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card :=
    fun i => card_bonds_inGroup_ge (F.ladder i)
  have hk1 : ∀ i, (S i).card - 1 = 2 * F.m i + 1 := fun i => by rw [hcardS i]; omega
  have hq : Fintype.card F.ι ≤ ∑ i, (2 * F.m i + 2) := by
    calc Fintype.card F.ι = ∑ _i : F.ι, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by omega)
  have hsumk : ∑ i, ((S i).card - 1) = ∑ i, (2 * F.m i + 2) - Fintype.card F.ι := by
    have : ∑ i, ((S i).card - 1) + Fintype.card F.ι = ∑ i, (2 * F.m i + 2) := by
      rw [← Finset.card_univ (α := F.ι), Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by have := hk1 i; omega)
    omega
  have hk : ∑ i, ((S i).card - 1) ≤ G.order := by omega
  -- the ladder bounds
  obtain ⟨C1s, hC1s⟩ : ∃ C1s : ℝ, C1s = Pg.C₁ * cb ^ 2 := ⟨_, rfl⟩
  have hC1s1 : 1 ≤ C1s := by
    have : 1 ≤ cb ^ 2 := one_le_pow₀ hcb1
    rw [hC1s]; nlinarith
  have hC1s0 : 0 < C1s := by linarith
  have hC0 : 0 < Pg.C₁ := by linarith
  set bs : F.ι → ℝ := fun i => C1s * (C1s * Pg.δ) ^ (F.m i) *
    Pg.L ^ (-(Pg.gamma1 - Real.sqrt Pg.η) * (sourceLadderIncoherency G D.layer (F.u i) (F.v i) : ℝ) +
      20 * (Pg.d : ℝ)) with hbs_def
  set b : F.ι → ℝ := fun i => cθ ^ (2 * F.m i + 2) * bs i with hb_def
  have hφ : ∀ z₀ : GenDecoration G Pg.d roots 0, ∃ r : ℂ, ‖r‖ ≤ 1 ∧
      ∀ z : GenDecoration G Pg.d roots 0, AgreeOff S z z₀ →
        D.atomW (cosetDecoration G Pg.L base z.1) = r * ∏ i, ladW D (S i) Pg.L base z.1 := fun z₀ =>
    ⟨_, norm_rest_le_one D (fun a q h u => (hok.1 a q h).2.2.1 u) hok.2.1 (univ \ Uni S) _,
      atomW_factor hplain D S hS split hsplit hok.2.2 Pg.L base z₀⟩
  have hφi : ∀ i (z z' : GenDecoration G Pg.d roots 0),
      (∀ x, G.molecule.atom x ∈ S i → bondIndex G z.1 x = bondIndex G z'.1 x) →
      ladW D (S i) Pg.L base z.1 = ladW D (S i) Pg.L base z'.1 :=
    fun i z z' h => ladW_congr hplain D (S i) Pg.L base z z' h
  have hb : ∀ (z₀ : GenDecoration G Pg.d roots 0)
      (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))),
      (∀ i ζ, ζ ∉ T i → ladderWeight D.toSplicedKernelData (S i) Pg.L Pg.γ Pg.η base ζ.1.1 = 0) → ∀ i,
      ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ ((S i).card - 1) *
        ∫ s in LadderDecay.timeBox G D.layer (S i),
          ‖LamW D.toSplicedKernelData S (fun i z => ladW D (S i) Pg.L base z) Pg.L Pg.γ Pg.η Pg.δ base z₀ T i s‖
        ≤ b i := by
    intro z₀ T hT i
    set R0 : GBranch G.tree → ℝ := fun a =>
      1 + ∑ ζ ∈ T i, |omegaNode G (cosetDecoration G Pg.L base ζ.1.1) a| with hR0
    have hR01 : ∀ a, 1 ≤ R0 a := fun a => by
      have : 0 ≤ ∑ ζ ∈ T i, |omegaNode G (cosetDecoration G Pg.L base ζ.1.1) a| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      simp only [hR0]; linarith
    have hRv : ∀ a, 1 ≤ RvOf D R0 a := by
      intro a
      unfold RvOf
      cases h : D.filt a with
      | none => exact hR01 a
      | some q => exact (hok.1 a q h).2.1
    have hgt := hgate p hp R hR1 hR2' G hplain hirr hbal hord1 hord2' D.toSplicedKernelData hD hlayers
      (F.m i) (F.u i) (F.v i) (hm1 i) (F.ladder i) (hH i) base roots (bondIndex G z₀.1) (T i)
      (psiOf D ψ₀) (RvOf D R0) hRv (hT i)
    have heq : ∀ s : S i → ℝ,
        LamW D.toSplicedKernelData S (fun i z => ladW D (S i) Pg.L base z) Pg.L Pg.γ Pg.η Pg.δ base z₀ T i s =
        ∑ z ∈ T i, (∏ a ∈ S i, psiOf D ψ₀ a
            (omegaNode G (cosetDecoration G Pg.L base z.1.1) a / RvOf D R0 a)) *
          ladderWeight D.toSplicedKernelData (S i) Pg.L Pg.γ Pg.η base z.1.1 *
          ladderPhase D.toSplicedKernelData (S i) Pg.L Pg.γ Pg.δ base z.1.1 s := by
      intro s
      unfold LamW
      refine Finset.sum_congr rfl (fun ζ hζ => ?_)
      have hRb : ∀ a ∈ S i, 0 < R0 a ∧ |omegaNode G (cosetDecoration G Pg.L base ζ.1.1) a| ≤ R0 a := by
        intro a _
        have h1 : |omegaNode G (cosetDecoration G Pg.L base ζ.1.1) a| ≤
            ∑ ζ' ∈ T i, |omegaNode G (cosetDecoration G Pg.L base ζ'.1.1) a| :=
          Finset.single_le_sum (f := fun ζ' : ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)) =>
            |omegaNode G (cosetDecoration G Pg.L base ζ'.1.1) a|) (fun _ _ => abs_nonneg _) hζ
        exact ⟨by linarith [hR01 a], by simp only [hR0]; linarith⟩
      beta_reduce
      rw [ladW_eq_psi D ψ₀ hψ₀ (S i) Pg.L base ζ.1.1 R0 hRb]
    have hP : ∏ a ∈ S i, max 1 (filterB ⇑(psiOf D ψ₀ a)) ≤ (cθ * cb) ^ ((S i).card) := by
      calc _ ≤ ∏ _a ∈ S i, (cθ * cb) :=
            Finset.prod_le_prod₀ (fun a _ => le_trans zero_le_one (le_max_left _ _))
              (fun a _ => filterB_psiOf_le D ψ₀ cθ hcθ (fun a q h => (hok.1 a q h).2.2.2) a)
        _ = _ := Finset.prod_const _
    calc ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ ((S i).card - 1) *
          ∫ s in LadderDecay.timeBox G D.layer (S i),
            ‖LamW D.toSplicedKernelData S (fun i z => ladW D (S i) Pg.L base z) Pg.L Pg.γ Pg.η Pg.δ base z₀ T i s‖
        = ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ ((S i).card - 1) *
          ∫ s in LadderDecay.timeBox G D.layer (S i),
            ‖∑ z ∈ T i, (∏ a ∈ S i, psiOf D ψ₀ a
              (omegaNode G (cosetDecoration G Pg.L base z.1.1) a / RvOf D R0 a)) *
            ladderWeight D.toSplicedKernelData (S i) Pg.L Pg.γ Pg.η base z.1.1 *
            ladderPhase D.toSplicedKernelData (S i) Pg.L Pg.γ Pg.δ base z.1.1 s‖ := by
          simp only [heq]
      _ ≤ _ := hgt
      _ ≤ (cθ * cb) ^ ((S i).card) * Pg.C₁ * (Pg.C₁ * Pg.δ) ^ (F.m i) *
          Pg.L ^ (-(Pg.gamma1 - Real.sqrt Pg.η) * (sourceLadderIncoherency G D.layer (F.u i) (F.v i) : ℝ) +
            20 * (Pg.d : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hP hC0.le) (by positivity)) (Real.rpow_nonneg hL0.le _)
      _ = b i := by
          rw [hcardS i]
          simp only [hb_def, hbs_def, hC1s]
          ring
  have hN := card_classes_le hplain D.toSplicedKernelData hD S hS hL0 Pg.γ Pg.η base roots
    (fun i => (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card) (fun i => rfl)
  -- numerology
  set q := Fintype.card F.ι with hqdef
  set Tn := ∑ i, (2 * F.m i + 2) with hTn
  set a := G.order - Tn with ha
  have hr : G.order - ∑ i, ((S i).card - 1) = a + q := by omega
  have hbonds : G.molecule.bonds.card - ∑ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card ≤
      2 * (a + q) := by
    have h1 := hprem.bond_count
    have h2 : ∑ i, (4 * F.m i + 2) ≤ ∑ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card :=
      Finset.sum_le_sum (fun i _ => hkk i)
    have h3 : ∑ i, (4 * F.m i + 2) = 2 * Tn - 2 * q := by
      have : ∑ i, (4 * F.m i + 2) + 2 * q = 2 * Tn := by
        have e1 : ∑ i : F.ι, ((4 * F.m i + 2) + 2) = 2 * Tn := by
          rw [hTn, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e1
        rw [hqdef]; linarith
      omega
    omega
  have hNle : ((((finite_momAmp_support G hplain D.toSplicedKernelData hD hL0 Pg.γ Pg.η base roots).toFinset.image
      (kappa S)).card : ℕ) : ℝ) ≤ (3 * Pg.L) ^ (2 * Pg.d * (a + q)) := by
    refine hN.trans ?_
    have h3 : (2 * Pg.L + 1) ≤ 3 * Pg.L := by linarith
    calc (2 * Pg.L + 1) ^ (Pg.d * (G.molecule.bonds.card -
          ∑ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card))
        ≤ (3 * Pg.L) ^ (Pg.d * (G.molecule.bonds.card -
          ∑ i, (G.molecule.bonds.filter (G.molecule.InGroup (S i))).card)) :=
          pow_le_pow_left₀ (by positivity) h3 _
      _ ≤ (3 * Pg.L) ^ (2 * Pg.d * (a + q)) := by
          apply pow_le_pow_right₀ (by linarith)
          calc _ ≤ Pg.d * (2 * (a + q)) := Nat.mul_le_mul_left _ hbonds
            _ = 2 * Pg.d * (a + q) := by ring
  have hmain0 := integral_freeBox_le_classes hplain D hD S hS hfree hH hL0 Pg.γ Pg.η Pg.δ base roots hcoup
    (fun z => D.atomW (cosetDecoration G Pg.L base z)) (fun i z => ladW D (S i) Pg.L base z) hφ hφi b hb hk
  have hfin := finite_momAmp_support G hplain D.toSplicedKernelData hD hL0 Pg.γ Pg.η base roots
  have hmain := (splicedKernelMK_norm_le D Pg.γ Pg.η Pg.δ base roots hfin.toFinset
    (fun z hz => hfin.mem_toFinset.mpr hz)).trans hmain0
  rw [hr] at hmain
  have hcθ0 : 0 ≤ cθ := by linarith
  have hbsnn : ∀ i, 0 ≤ bs i := fun i => by simp only [hbs_def]; positivity
  have hbnn : 0 ≤ ∏ i, b i := Finset.prod_nonneg (fun i _ => mul_nonneg (pow_nonneg hcθ0 _) (hbsnn i))
  have hprodb : ∏ i, b i = cθ ^ Tn * ∏ i, bs i := by
    simp only [hb_def]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hfa := final_arith Pg.d hd Pg.γ Pg.η Pg.δ (Pg.gamma1 - Real.sqrt Pg.η) Pg.L C1s hγ0 hγ1 hδ0 hδ1 hL hC1s1
    hη0.le hx hη1 F.m (fun i => sourceLadderIncoherency G D.layer (F.u i) (F.v i)) a
    (G.molecule.rho + (D.hinges ∪ split).card) (A.totalIncoherency D.layer) hSA hSB (by rw [← hqdef]; omega)
  have hnT : Tn + a = G.order := by omega
  show ‖splicedKernelMK G D Pg.L Pg.γ Pg.η Pg.δ base roots‖ ≤
    (1 : ℝ) * (cθ * (Pg.C₁ * cb ^ 2 * 3 ^ (2 * Pg.d)) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + ((D.hinges ∪ split).card : ℝ)))
  rw [← hC1s]
  have hfa' : (Pg.δ / (2 * Pg.L ^ ((Pg.d : ℝ) - Pg.γ))) ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) *
      ∏ i, bs i ≤ (C1s * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + ((D.hinges ∪ split).card : ℝ))) := by
    rw [← hnT]
    push_cast at hfa
    exact hfa
  have hTle : Tn ≤ G.order := by omega
  have hcpow : cθ ^ Tn ≤ cθ ^ G.order := pow_le_pow_right₀ hcθ hTle
  have hrhs0 : 0 ≤ (C1s * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + ((D.hinges ∪ split).card : ℝ))) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hL0.le _)
  calc ‖splicedKernelMK G D Pg.L Pg.γ Pg.η Pg.δ base roots‖
      ≤ ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ (a + q) *
          ((((finite_momAmp_support G hplain D.toSplicedKernelData hD hL0 Pg.γ Pg.η base roots).toFinset.image
            (kappa S)).card : ℕ) : ℝ) * ∏ i, b i := hmain
    _ ≤ ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) * ∏ i, b i := by
        gcongr
    _ = cθ ^ Tn * ((Pg.δ / (2 * Pg.L ^ ((Pg.d : ℝ) - Pg.γ))) ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) *
        ∏ i, bs i) := by rw [hcoupv, hprodb]; ring
    _ ≤ cθ ^ Tn * ((C1s * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + ((D.hinges ∪ split).card : ℝ)))) :=
        mul_le_mul_of_nonneg_left hfa' (pow_nonneg hcθ0 _)
    _ ≤ cθ ^ G.order * ((C1s * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + ((D.hinges ∪ split).card : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcpow hrhs0
    _ = _ := by rw [one_mul, mul_assoc cθ, mul_pow]; ring

end WaveTurbulence.Flower.FinalMKCrude
