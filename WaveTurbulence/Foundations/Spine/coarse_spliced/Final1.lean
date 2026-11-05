/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Selection2
public import WaveTurbulence.Foundations.Spine.Arith
public import WaveTurbulence.Foundations.Spine.coarse_spliced.Count
/-! # The coarse spliced estimate at fixed parameters (S3c)

TARGET finalsbest1 (L2075-L2077).  From the time-L1 ladder bound (`LadderL1At`, the intermediate bound
of redladder2 before the time ordering is used) and the ladder selection. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

theorem Rdown_congr (P P' : WTParams) (hd : P.d = P'.d) (hL : P.L = P'.L) :
    ∀ k, P.Rdown k = P'.Rdown k := by
  intro k
  induction k with
  | zero => simp only [WTParams.Rdown, hd, hL]
  | succ k ih => simp only [WTParams.Rdown, ih, hd]

theorem R_congr (P P' : WTParams) (hd : P.d = P'.d) (hL : P.L = P'.L) (hD : P.D = P'.D) (q : ℕ) :
    P.R q = P'.R q := by
  simp only [WTParams.R, hD, Rdown_congr P P' hd hL]

theorem N_congr (P P' : WTParams) (hd : P.d = P'.d) (hL : P.L = P'.L) (hD : P.D = P'.D) (q : ℕ) :
    P.N q = P'.N q := by
  simp only [WTParams.N, R_congr P P' hd hL hD, hd]

theorem coarse_fixed (Pg : WTParams) (hd : 3 ≤ Pg.d) (hγ0 : 0 < Pg.γ) (hγ1 : Pg.γ < 1)
    (hη0 : 0 < Pg.η) (hx : 4 * Pg.η ≤ Pg.gamma1 - Real.sqrt Pg.η) (hη1 : Pg.η ≤ 1)
    (hδ0 : 0 < Pg.δ) (hδ1 : Pg.δ ≤ 1) (hL : 1 ≤ Pg.L) (hC : 1 ≤ Pg.C₁)
    (hgate : LadderL1At Pg) :
    CoarseSplicedAtC { Pg with C₁ := Pg.C₁ * 3 ^ (2 * Pg.d), C₂ := 1 } := by
  intro p hp R hR1 hR2 G hplain hirr hbal hord1 hord2 D hD hlayers A base roots hprem
  have hR2' : R ≤ 10 * Pg.R (p + 1) := by
    have := R_congr { Pg with C₁ := Pg.C₁ * 3 ^ (2 * Pg.d), C₂ := 1 } Pg rfl rfl rfl (p + 1)
    rw [← this]; exact hR2
  have hord2' : G.order ≤ Pg.N (p + 1) ^ 4 := by
    have := N_congr { Pg with C₁ := Pg.C₁ * 3 ^ (2 * Pg.d), C₂ := 1 } Pg rfl rfl rfl (p + 1)
    rw [← this]; exact hord2
  have hL0 : 0 < Pg.L := by linarith
  obtain ⟨F, hSA, hSB, hSC⟩ := selection_claim G D.layer D.hinges hprem.molecule hprem.connected
    hprem.atom_count A
  set S : F.ι → Finset (GBranch G.tree) := fun i => Molecule.ladderAtoms (F.u i) (F.v i) with hSdef
  have hS : ∀ i j, i ≠ j → Disjoint (S i) (S j) := F.disj
  have hH : ∀ i, Disjoint (S i) D.hinges := F.hing
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
  set b : F.ι → ℝ := fun i => Pg.C₁ * (Pg.C₁ * Pg.δ) ^ (F.m i) *
    Pg.L ^ (-(Pg.gamma1 - Real.sqrt Pg.η) * (sourceLadderIncoherency G D.layer (F.u i) (F.v i) : ℝ) +
      20 * (Pg.d : ℝ)) with hb_def
  have hb : ∀ (z₀ : GenDecoration G Pg.d roots 0)
      (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))),
      (∀ i ζ, ζ ∉ T i → ladderWeight D (S i) Pg.L Pg.γ Pg.η base ζ.1.1 = 0) → ∀ i,
      ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ ((S i).card - 1) *
        ∫ s in LadderDecay.timeBox G D.layer (S i), ‖Lam D S Pg.L Pg.γ Pg.η Pg.δ base z₀ T i s‖ ≤ b i := by
    intro z₀ T hT i
    exact hgate p hp R hR1 hR2' G hplain hirr hbal hord1 hord2' D hD hlayers (F.m i) (F.u i) (F.v i)
      (hm1 i) (F.ladder i) (F.hing i) base roots (bondIndex G z₀.1) (T i) (hT i)
  have hmain := splicedKernel_le_classes hplain D hD S hS hH hL0 Pg.γ Pg.η Pg.δ base roots hcoup b hb hk
  have hN := card_classes_le hplain D hD S hS hL0 Pg.γ Pg.η base roots
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
  have hNle : ((((finite_momAmp_support G hplain D hD hL0 Pg.γ Pg.η base roots).toFinset.image
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
  rw [hr] at hmain
  have hprodb : ∏ i, b i = ∏ i, (Pg.C₁ * (Pg.C₁ * Pg.δ) ^ (F.m i) *
      Pg.L ^ (-(Pg.gamma1 - Real.sqrt Pg.η) * (sourceLadderIncoherency G D.layer (F.u i) (F.v i) : ℝ) +
        20 * (Pg.d : ℝ))) := rfl
  have hbnn : 0 ≤ ∏ i, b i := Finset.prod_nonneg (fun i _ => by
    simp only [hb_def]; positivity)
  have hfa := final_arith Pg.d hd Pg.γ Pg.η Pg.δ (Pg.gamma1 - Real.sqrt Pg.η) Pg.L Pg.C₁ hγ0 hγ1 hδ0 hδ1 hL hC
    hη0.le hx hη1 F.m (fun i => sourceLadderIncoherency G D.layer (F.u i) (F.v i)) a
    (G.molecule.rho + D.hinges.card) (A.totalIncoherency D.layer) hSA hSB (by rw [← hqdef]; omega)
  have hnT : Tn + a = G.order := by omega
  -- assemble
  show ‖splicedKernel G D Pg.L Pg.γ Pg.η Pg.δ base roots‖ ≤
    (1 : ℝ) * (Pg.C₁ * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + (D.hinges.card : ℝ)))
  have hfa' : (Pg.δ / (2 * Pg.L ^ ((Pg.d : ℝ) - Pg.γ))) ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) *
      ∏ i, b i ≤ (Pg.C₁ * 3 ^ (2 * Pg.d) * Real.sqrt Pg.δ) ^ G.order *
      Pg.L ^ (-Pg.η * (A.totalIncoherency D.layer : ℝ) +
        80 * (Pg.d : ℝ) * ((G.molecule.rho : ℝ) + (D.hinges.card : ℝ))) := by
    rw [← hnT]
    push_cast at hfa
    exact hfa
  calc ‖splicedKernel G D Pg.L Pg.γ Pg.η Pg.δ base roots‖
      ≤ ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ (a + q) *
          ((((finite_momAmp_support G hplain D hD hL0 Pg.γ Pg.η base roots).toFinset.image
            (kappa S)).card : ℕ) : ℝ) * ∏ i, b i := hmain
    _ ≤ ‖(coupling Pg.d Pg.L Pg.γ Pg.δ : ℂ)‖ ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) * ∏ i, b i := by
        gcongr
    _ = (Pg.δ / (2 * Pg.L ^ ((Pg.d : ℝ) - Pg.γ))) ^ (a + q) * (3 * Pg.L) ^ (2 * Pg.d * (a + q)) *
        ∏ i, b i := by rw [hcoupv]
    _ ≤ _ := by rw [one_mul]; exact hfa'

end WaveTurbulence.CoarseSpliced
