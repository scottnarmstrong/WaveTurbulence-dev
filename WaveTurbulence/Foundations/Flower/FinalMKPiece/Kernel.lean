/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.FinalMKPiece.Interp

/-! # C5a PIECE-MK: the pointwise kernel bound of a marked piece

Crude (`CoarseSplicedAtMK`, split `= joints ∪ prot`) and fine (`FineSplicedAtMK`, `E = prot`) bounds interpolated at
`θ = 40ν` (`mk_interpolation`). The extra exponent fits `markedExtra` once `1 ≤ d` (SCOPE §4.4). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open scoped Classical

theorem joints_card_le {w : ℕ} {G : Garden w} (S : SurvivorData G) : S.joints.card ≤ 2 * S.m := by
  unfold SurvivorData.joints
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ i : Fin S.m, ({(S.surv i).upper, (S.surv i).lower} : Finset _).card ≤ ∑ _i : Fin S.m, 2 :=
        Finset.sum_le_sum fun i _ => Finset.card_le_two
    _ = 2 * S.m := by simp [mul_comm]

/-- The arithmetic of the extras: coarse `40ν · 80d · |split|` and fine `2m + 2(5d+4)|E|` fit `markedExtra`. -/
theorem extra_le {d ν m np K E : ℝ} (hd : 1 ≤ d) (_hν0 : 0 ≤ ν) (hν : 40 * ν ≤ 1 / 100) (hm : 0 ≤ m)
    (hnp : 0 ≤ np) (hK0 : 0 ≤ K) (hK : K ≤ 2 * m + 2 * np) (_hE0 : 0 ≤ E) (hE : E ≤ 2 * np) :
    40 * ν * (80 * d * K) + (2 * m + 2 * ((5 * d + 4) * E)) ≤
      (60 * d + 2) * (2 * m + 2 * np) + 2 * m := by
  have h1 : 40 * ν * (80 * d * K) ≤ (1 / 100) * (80 * d * K) :=
    mul_le_mul_of_nonneg_right hν (by positivity)
  have h2 : d * K ≤ d * (2 * m + 2 * np) := mul_le_mul_of_nonneg_left hK (by linarith)
  have h3 : (5 * d + 4) * E ≤ (5 * d + 4) * (2 * np) :=
    mul_le_mul_of_nonneg_left hE (by linarith)
  have h4 : 0 ≤ (d - 1) * np := mul_nonneg (by linarith) hnp
  have h5 : 0 ≤ d * m := by positivity
  nlinarith


theorem pow_card_le {N : ℕ} {L o : ℝ} (hL : 1 ≤ L) (ho : o + 1 ≤ L) (ho0 : 0 ≤ o) :
    ((o + 1) * L) ^ N ≤ L ^ ((2 * N : ℕ) : ℝ) := by
  have hL0 : 0 < L := by linarith
  have h1 : (o + 1) * L ≤ L * L := mul_le_mul_of_nonneg_right ho hL0.le
  calc ((o + 1) * L) ^ N ≤ (L * L) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = L ^ ((2 * N : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, pow_mul, sq]

/-- **The pointwise marked kernel bound** (`θ = 40ν` interpolation). -/
theorem kernel_bound {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMK P.d R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFull π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt c e h f)) :
    ‖splicedKernelMK π.Gsb (π.dataMK tt c e h f) P.L P.γ P.η P.δ base roots‖ ≤
      (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L)) *
      (cθ ^ (40 * P.ν)) ^ π.Gsb.order *
      P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)) := by

  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  set D := π.dataMK tt c e h f with hDdef
  set split : Finset (GBranch π.Gsb.tree) := π.surv.joints ∪ π.surv.prot with hsplit
  have hgeom : SplicedGeomPremises π.Gsb :=
    ⟨hπ.molecule, hπ.connected, hπ.atom_count, hπ.bond_count⟩
  have hok : AtomOK D split cθ := by
    refine ⟨fun a q hq => ?_, hπ.ind_ok, fun k k' hk => hπ.ind_local k k' ?_⟩
    · exact hπ.filt_ok a q hq
    · intro a ha i
      exact hk a (by simpa [hsplit, Finset.mem_union] using ha) i
  have hfixs : ∀ b, (D.fix b).isSome → b ∈ split := fun b hb =>
    Finset.mem_union_right _ (hπ.fix_prot b hb)
  have hc := hcoarse p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
    hπ.order_le D split cθ hcθ hamp (fun v => hπ.layer_le v) hok hfixs π.ladders base roots hgeom
  have hconc : SubproConclusionsMK π.Gsb D.toSplicedKernelData π.Cs π.surv P.L P.γ P.η base roots :=
    ⟨hπ.structural, hπ.survivors, hπ.chainOrder, rfl, fun z he hg => hπ.support z he hg,
      hπ.hingeOutsideFirst, hπ.tripleDesignated, hπ.hingeNoLoop⟩
  have hf := hfine p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
    hπ.order_le D π.Cs π.surv π.surv.prot hamp (fun v => hπ.layer_le v)
    (fun a q hq u => (hπ.filt_ok a q hq).2.2.1 u) hπ.ind_ok
    (fun b hb => hπ.fix_prot b hb) hπ.fix_layer base roots hgeom hconc
  have hC1 : 0 < P.C₁ := by linarith [hs.c1_ge]
  have hC2 : 0 < P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  have hν0 : 0 ≤ P.ν := hs.nu_pos.le
  have hδ0 : 0 < P.δ := hs.delta_pos
  have hordL : (π.Gsb.order : ℝ) + 1 ≤ P.L :=
    le_trans (by have : (π.Gsb.order : ℝ) ≤ n := by exact_mod_cast hnsb
                 linarith) hnL
  set K : ℝ := (split.card : ℝ) with hK
  set ρ : ℝ := (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) with hρ
  set Ncard : ℕ := (5 * P.d + 4) * π.surv.prot.card with hNcard
  have hρ0 : 0 ≤ ρ := by positivity
  have hcard : (((D.hinges ∪ split).card : ℕ) : ℝ) ≤ (π.Cs.hinges.card : ℝ) + K := by
    have := Finset.card_union_le D.hinges split
    have h2 : ((D.hinges ∪ split).card : ℝ) ≤ (D.hinges.card : ℝ) + (split.card : ℝ) := by
      exact_mod_cast this
    exact h2
  have hc2 : ‖splicedKernelMK π.Gsb D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (cθ * P.C₁ * Real.sqrt P.δ) ^ π.Gsb.order *
        P.L ^ (-P.η * (π.gsb : ℝ) + 80 * (P.d : ℝ) * ρ + 80 * (P.d : ℝ) * K) := by
    refine hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 ?_) (by positivity))
    have h80 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 80 * (P.d : ℝ))
    have hg : (π.ladders.totalIncoherency D.layer : ℝ) = (π.gsb : ℝ) := rfl
    rw [hg]
    nlinarith
  have hE : ((π.surv.prot.card : ℕ) : ℝ) ≤ 2 * (π.nProt : ℝ) := by exact_mod_cast hπ.prot_card
  have hf2 : ‖splicedKernelMK π.Gsb D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ π.Gsb.order * P.L ^ (-P.η ^ 6 * ρ) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) *
        P.L ^ (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) := by
    refine hf.trans ?_
    have hp1 := pow_card_le (N := Ncard) hL1 hordL (Nat.cast_nonneg _)
    have hpow : P.L ^ (2 * (π.surv.m : ℝ)) * (((π.Gsb.order : ℝ) + 1) * P.L) ^ Ncard ≤
        P.L ^ (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) := by
      rw [Real.rpow_add hL0]
      exact mul_le_mul_of_nonneg_left hp1 (by positivity)
    calc _ = P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ π.Gsb.order *
          P.L ^ (-P.η ^ 6 * ρ) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) *
          (P.L ^ (2 * (π.surv.m : ℝ)) * (((π.Gsb.order : ℝ) + 1) * P.L) ^ Ncard) := by
            have hh : D.hinges = π.Cs.hinges := rfl
            simp only [hρ, hh]; ring
      _ ≤ _ := by gcongr
  have hi := mk_interpolation (z := splicedKernelMK π.Gsb D P.L P.γ P.η P.δ base roots)
    (C := P.C₁) (H := P.C₂) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν) (d := (P.d : ℝ)) (ρ := ρ)
    (g := (π.gsb : ℝ)) (R := (R : ℝ)) (cθ := cθ) (e1 := 80 * (P.d : ℝ) * K)
    (e2 := 2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) π.Gsb.order hC1 hC2 hs.c1_le_c2 hcθ
    hs.delta_pos hs.delta_le hL1 hν0 hs.nu_small hs.cost hρ0 (by exact_mod_cast hR) (by positivity)
    hc2 hf2
  have hKle : K ≤ 2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ) := by
    have h1 : split.card ≤ π.surv.joints.card + π.surv.prot.card := Finset.card_union_le _ _
    have h2 := joints_card_le π.surv
    have h3 := hπ.prot_card
    have : split.card ≤ 2 * π.surv.m + 2 * π.nProt := by omega
    have h4 : (split.card : ℝ) ≤ 2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ) := by exact_mod_cast this
    exact h4
  have hextra : 40 * P.ν * (80 * (P.d : ℝ) * K) + (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) ≤
      (60 * (P.d : ℝ) + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) := by
    have := extra_le (d := (P.d : ℝ)) (ν := P.ν) (m := (π.surv.m : ℝ)) (np := (π.nProt : ℝ))
      (K := K) (E := ((π.surv.prot.card : ℕ) : ℝ)) (by exact_mod_cast hd) hν0 hs.nu_small
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKle (Nat.cast_nonneg _) hE
    have hN : ((2 * Ncard : ℕ) : ℝ) = 2 * (((5 * (P.d : ℝ) + 4)) * ((π.surv.prot.card : ℕ) : ℝ)) := by
      simp only [hNcard]; push_cast; ring
    rw [hN]; exact this
  have hcθ0 : 0 < cθ := by linarith
  have hexp : P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ +
        40 * P.ν * Real.log cθ) +
      (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ρ / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60) +
        40 * P.ν * (80 * (P.d : ℝ) * K) + (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ))) * Real.log P.L) =
      (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ρ / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
          Real.log P.L)) * (cθ ^ (40 * P.ν)) ^ π.Gsb.order *
      P.L ^ (40 * P.ν * (80 * (P.d : ℝ) * K) + (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hcθ0, ← Real.exp_nat_mul, Real.rpow_def_of_pos hL0]
    simp only [mul_assoc]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  refine hi.trans (le_of_eq_of_le hexp ?_)
  have hmono := Real.rpow_le_rpow_of_exponent_le hL1 hextra
  have hpos : 0 ≤ (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ρ / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
          Real.log P.L)) * (cθ ^ (40 * P.ν)) ^ π.Gsb.order := by positivity
  exact mul_le_mul_of_nonneg_left hmono hpos

end WaveTurbulence.Flower.FinalMKPiece
