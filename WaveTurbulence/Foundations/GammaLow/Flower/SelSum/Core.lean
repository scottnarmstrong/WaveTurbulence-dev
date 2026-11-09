/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.Flower.SelRes.Check

/-! # FLOWER-LOW (packet L8), item G: D7's selected class sum over `𝒱_γ`

Main's `Flower.SelRes.{Point, Gate, Bound, Sum, Check}` and `Flower.FinalMKPiece.Kernel.joints_card_le`
carrier-dependent declarations, copied by source (sha256 in `COPIED-SHA256SUMS`) onto the `𝒱_γ` marked carrier of
`Carrier/` (`Stage1PieceMKG`, `SoundMKFullG`, `RepresentsIntMKSelG`, `FineSplicedAtMKG`, `Fama.Stage1CountsG`). The
proof never inspects the vine family: the fine gate `FineSplicedAtMKG` is a hypothesis of the target, consumed per
piece. Everything family-free (SelRes's cells, faces, patterns, pins, arithmetic; FinalMKPiece's kernel lemmas) is
main's, by import.

**`selSumTargetTG : SelSumTargetTG`** (no hypotheses). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open scoped Classical

theorem joints_card_leLow {γ : ℝ} {w : ℕ} {G : Garden w} (S : SurvivorDataG γ G) : S.joints.card ≤ 2 * S.m := by
  unfold SurvivorDataG.joints
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ i : Fin S.m, ({(S.surv i).upper, (S.surv i).lower} : Finset _).card ≤ ∑ _i : Fin S.m, 2 :=
        Finset.sum_le_sum fun i _ => Finset.card_le_two
    _ = 2 * S.m := by simp [mul_comm]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece

/-- **The gate bound for the modified piece data** (C5a's `kernel_bound` with split `joints ∪ prot ∪ sel ∪ Rc`
and `E = prot ∪ sel ∪ Rc`, `#Rc ≤ #sel`). -/
theorem kernel_bound_modLow {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMKG P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMKG P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFullG π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Fama.Stage1PieceG.data π.toStage1PieceGD tt c e h f))
    (sel : Finset (GBranch π.Gsb.tree)) (D' : SplicedKernelDataMK π.Gsb P.d)
    (hD' : ModOK sel (π.dataMK tt c e h f) D') :
    ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤
      (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L)) *
      (cθ ^ (40 * P.ν)) ^ π.Gsb.order *
      P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) +
        (22 * P.d + 16) * (sel.card : ℝ)) := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  set D := π.dataMK tt c e h f with hDdef
  obtain ⟨hdata, hfilt, ⟨g, hg, hgl, hind⟩, ⟨Rc, hRc, hchg, hbox⟩, hlbeq⟩ := hD'
  set X : Finset (GBranch π.Gsb.tree) := sel ∪ Rc with hX
  have hXcard : X.card ≤ 2 * sel.card := by
    have h1 : (sel ∪ Rc).card ≤ sel.card + Rc.card := card_union_le sel Rc
    rw [hX]; omega
  set split : Finset (GBranch π.Gsb.tree) := π.surv.joints ∪ π.surv.prot ∪ X with hsplit
  set E : Finset (GBranch π.Gsb.tree) := π.surv.prot ∪ X with hE
  have hD'd : D'.toSplicedKernelData = Fama.Stage1PieceG.data π.toStage1PieceGD tt c e h f := hdata
  have hlay : D'.layer = π.layer := by rw [show D'.layer = D'.toSplicedKernelData.layer from rfl, hD'd]; rfl
  have hhin : D'.hinges = π.Cs.hinges := by
    rw [show D'.hinges = D'.toSplicedKernelData.hinges from rfl, hD'd]; rfl
  have hamp' : SplicedAmplitudeBounds π.Gsb D'.toSplicedKernelData := by rw [hD'd]; exact hamp
  have hgeom : SplicedGeomPremises π.Gsb := ⟨hπ.molecule, hπ.connected, hπ.atom_count, hπ.bond_count⟩
  have hfilt' : ∀ a q, D'.filt a = some q → D'.filt a = π.filt a := fun a q _ => by rw [hfilt]; rfl
  have hok : AtomOK D' split cθ := by
    refine ⟨fun a q hq => ?_, fun k => ?_, fun k k' hk => ?_⟩
    · have hq' : π.filt a = some q := (hfilt' a q hq).symm.trans hq
      rw [hhin]; exact hπ.filt_ok a q hq'
    · rw [hind]
      have h1 := hπ.ind_ok k
      exact ⟨mul_nonneg h1.1 (hg k).1, (mul_le_mul h1.2 (hg k).2 (hg k).1 zero_le_one).trans_eq (one_mul 1)⟩
    · rw [hind, hind]
      show π.ind k * g k = π.ind k' * g k'
      rw [hπ.ind_local k k' fun a ha i => hk a (by simp only [hsplit, Finset.mem_union] at ha ⊢; tauto) i,
        hgl k k' fun a ha i => hk a (by simp only [hsplit, hX, Finset.mem_union]; tauto) i]
  have hpinS : ∀ b, (D'.fix b).isSome → b ∈ π.surv.prot ∪ X := by
    intro b hb
    by_cases hchb : D'.fix b = π.fix b
    · exact Finset.mem_union_left _ (hπ.fix_prot b (by rw [← hchb]; exact hb))
    · exact Finset.mem_union_right _ (hchg b hchb)
  have hfixs : ∀ b, (D'.fix b).isSome → b ∈ split := fun b hb => by
    have := hpinS b hb
    simp only [hsplit, Finset.mem_union] at this ⊢; tauto
  have hc := hcoarse p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
    hπ.order_le D' split cθ hcθ hamp' (fun v => by rw [hlay]; exact hπ.layer_le v) hok hfixs π.ladders base roots
    hgeom
  have hconc : SubproConclusionsMKG π.Gsb D'.toSplicedKernelData π.Cs π.surv P.L P.γ P.η base roots := by
    rw [hD'd]
    exact ⟨hπ.structural, hπ.survivors, hπ.chainOrder, rfl, fun z he hg => hπ.support z he hg,
      hπ.hingeOutsideFirst, hπ.tripleDesignated, hπ.hingeNoLoop⟩
  have hfixlay : ∀ b t, D'.fix b = some t → (D'.layer b : ℝ) ≤ t ∧ t ≤ D'.layer b + 1 := by
    intro b t hbt
    rw [hlay]
    by_cases hchb : D'.fix b = π.fix b
    · exact hπ.fix_layer b t (by rw [← hchb]; exact hbt)
    · obtain ⟨t', ht', hb'⟩ := hbox b hchb
      rw [hbt] at ht'; cases ht'; exact hb'
  have hf := hfine p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
    hπ.order_le D' π.Cs π.surv E hamp' (fun v => by rw [hlay]; exact hπ.layer_le v)
    (fun a q hq u => by have hq' : π.filt a = some q := (hfilt' a q hq).symm.trans hq
                        exact (hπ.filt_ok a q hq').2.2.1 u)
    (fun k => by rw [hind]; have h1 := hπ.ind_ok k
                 exact ⟨mul_nonneg h1.1 (hg k).1,
                   (mul_le_mul h1.2 (hg k).2 (hg k).1 zero_le_one).trans_eq (one_mul 1)⟩)
    hpinS hfixlay (fun b hb => Finset.mem_union_left _ (hπ.lb_prot b (by rw [hlbeq] at hb; exact hb)))
    base roots hgeom hconc
  have hC1 : 0 < P.C₁ := by linarith [hs.c1_ge]
  have hC2 : 0 < P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  have hν0 : 0 ≤ P.ν := hs.nu_pos.le
  have hordL : (π.Gsb.order : ℝ) + 1 ≤ P.L :=
    le_trans (by have : (π.Gsb.order : ℝ) ≤ n := by exact_mod_cast hnsb
                 linarith) hnL
  set K0 : ℝ := ((π.surv.joints ∪ π.surv.prot).card : ℝ) with hK0
  set K : ℝ := (split.card : ℝ) with hK
  set ρ : ℝ := (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) with hρ
  set Ncard : ℕ := (5 * P.d + 4) * E.card with hNcard
  have hρ0 : 0 ≤ ρ := by positivity
  have hcard : (((D'.hinges ∪ split).card : ℕ) : ℝ) ≤ (π.Cs.hinges.card : ℝ) + K := by
    rw [hhin, hK]
    exact_mod_cast Finset.card_union_le π.Cs.hinges split
  have hc2 : ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (cθ * P.C₁ * Real.sqrt P.δ) ^ π.Gsb.order *
        P.L ^ (-P.η * (π.gsb : ℝ) + 80 * (P.d : ℝ) * ρ + 80 * (P.d : ℝ) * K) := by
    refine hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 ?_) (by positivity))
    have h80 := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 80 * (P.d : ℝ))
    have hg' : (π.ladders.totalIncoherency D'.layer : ℝ) = (π.gsb : ℝ) := by rw [hlay]; rfl
    rw [hg']
    nlinarith
  have hf2 : ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤
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
            simp only [hρ, hhin]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by have := hs.delta_pos; positivity)
  have hi := mk_interpolation (z := splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots)
    (C := P.C₁) (H := P.C₂) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν) (d := (P.d : ℝ)) (ρ := ρ)
    (g := (π.gsb : ℝ)) (R := (R : ℝ)) (cθ := cθ) (e1 := 80 * (P.d : ℝ) * K)
    (e2 := 2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) π.Gsb.order hC1 hC2 hs.c1_le_c2 hcθ
    hs.delta_pos hs.delta_le hL1 hν0 hs.nu_small hs.cost hρ0 (by exact_mod_cast hR) (by positivity)
    hc2 hf2
  have hK0le : K0 ≤ 2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ) := by
    have h1 : (π.surv.joints ∪ π.surv.prot).card ≤ π.surv.joints.card + π.surv.prot.card := Finset.card_union_le _ _
    have h2 := joints_card_leLow π.surv
    have h3 := hπ.prot_card
    have : (π.surv.joints ∪ π.surv.prot).card ≤ 2 * π.surv.m + 2 * π.nProt := by omega
    show (((π.surv.joints ∪ π.surv.prot).card : ℕ) : ℝ) ≤ _
    exact_mod_cast this
  have hKle : K ≤ K0 + 2 * (sel.card : ℝ) := by
    have h1 : split.card ≤ (π.surv.joints ∪ π.surv.prot).card + X.card := Finset.card_union_le _ _
    have : split.card ≤ (π.surv.joints ∪ π.surv.prot).card + 2 * sel.card := by omega
    have h4 : (split.card : ℝ) ≤ ((π.surv.joints ∪ π.surv.prot).card : ℝ) + 2 * (sel.card : ℝ) := by
      exact_mod_cast this
    exact h4
  have hEle : ((E.card : ℕ) : ℝ) ≤ ((π.surv.prot.card : ℕ) : ℝ) + 2 * (sel.card : ℝ) := by
    have h1 : E.card ≤ π.surv.prot.card + X.card := Finset.card_union_le _ _
    have : E.card ≤ π.surv.prot.card + 2 * sel.card := by omega
    exact_mod_cast this
  have hEp : ((π.surv.prot.card : ℕ) : ℝ) ≤ 2 * (π.nProt : ℝ) := by exact_mod_cast hπ.prot_card
  have hextra : 40 * P.ν * (80 * (P.d : ℝ) * K) + (2 * (π.surv.m : ℝ) + ((2 * Ncard : ℕ) : ℝ)) ≤
      (60 * (P.d : ℝ) + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) +
        (22 * (P.d : ℝ) + 16) * (sel.card : ℝ) := by
    have := extra_le_sel (d := (P.d : ℝ)) (ν := P.ν) (m := (π.surv.m : ℝ)) (np := (π.nProt : ℝ))
      (K := K0) (E := ((π.surv.prot.card : ℕ) : ℝ)) (a := (sel.card : ℝ)) (by exact_mod_cast hd) hν0
      hs.nu_small (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hK0le (Nat.cast_nonneg _) hEp
      (Nat.cast_nonneg _) K ((E.card : ℕ) : ℝ) hKle hEle
    have hN : ((2 * Ncard : ℕ) : ℝ) = 2 * (((5 * (P.d : ℝ) + 4)) * ((E.card : ℕ) : ℝ)) := by
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

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- C5a's pointwise kernel bound of a piece (the right side of `kernel_bound`). -/
def bsfLow (P : WTParams) (cθ : ℝ) {R : ℕ} (π : Stage1PieceMKG P R) : ℝ :=
  (P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
    (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
      ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L)) *
    (cθ ^ (40 * P.ν)) ^ π.Gsb.order *
    P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

theorem bsf_nonnegLow {P : WTParams} (hs : PieceSmall P) {cθ : ℝ} (hcθ : 1 ≤ cθ) {R : ℕ} (π : Stage1PieceMKG P R) :
    0 ≤ bsfLow P cθ π := by
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  unfold bsfLow
  have : 0 ≤ cθ ^ (40 * P.ν) := Real.rpow_nonneg (by linarith) _
  positivity

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- **A lower bound for `bsfLow`** (used only for tiny `δ`): `(δ^{10ν}/L)^{ord}`. -/
theorem bsf_lowerLow {P : WTParams} (hs : PieceSmall P) {cθ : ℝ} (hcθ : 1 ≤ cθ) {R : ℕ} (π : Stage1PieceMKG P R)
    (hgsb : (π.gsb : ℝ) ≤ π.Gsb.order) (hρ : (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) ≤ 2 * π.Gsb.order)
    (hR : (R : ℝ) ≤ 2 * π.Gsb.order) :
    (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order ≤ bsfLow P cθ π := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith
  have hδ0 := hs.delta_pos
  have hC1 : 1 ≤ P.C₁ := hs.c1_ge
  have hC2 : 1 ≤ P.C₂ := hC1.trans hs.c1_le_c2
  have hν0 := hs.nu_pos.le
  have hη0 := hs.eta_pos.le
  have hη1 := hs.eta_le
  set o : ℝ := (π.Gsb.order : ℝ) with ho
  have hlogL : 0 ≤ Real.log P.L := Real.log_nonneg hL1
  have hlogC : 0 ≤ Real.log P.C₁ := Real.log_nonneg hC1
  have hEL : -o ≤ -40 * P.ν * P.η * (π.gsb : ℝ) -
      P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 - ((R : ℝ) - 1) * (1 / 4 + 1 / 60) := by
    have h6 : P.η ^ 6 ≤ 1 / 4 := by
      calc P.η ^ 6 ≤ (1 / 4) ^ 6 := pow_le_pow_left₀ hη0 hη1 6
        _ ≤ 1 / 4 := by norm_num
    have hg0 : (0 : ℝ) ≤ π.gsb := Nat.cast_nonneg _
    have hρ0 : (0 : ℝ) ≤ (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) := by positivity
    have h1 : 40 * P.ν * P.η * (π.gsb : ℝ) ≤ o / 400 := by
      have : 40 * P.ν * P.η ≤ 1 / 400 := by nlinarith [hs.nu_small]
      nlinarith
    have h2 : P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 ≤ o / 4 := by nlinarith
    nlinarith
  have hexp : Real.exp (o * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
      (-40 * P.ν * P.η * (π.gsb : ℝ) - P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
        ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) ≥ (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order := by
    have e : (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order = Real.exp (o * (10 * P.ν * Real.log P.δ) + (-o) * Real.log P.L) := by
      rw [div_eq_mul_inv, mul_pow, Real.rpow_def_of_pos hδ0, ← Real.exp_nat_mul, ← Real.exp_log hL0,
        ← Real.exp_neg, ← Real.exp_nat_mul, Real.log_exp, ← Real.exp_add]
      congr 1; ring
    rw [e, ge_iff_le, Real.exp_le_exp]
    have : o * (Real.log P.C₁) ≥ 0 := mul_nonneg (Nat.cast_nonneg _) hlogC
    nlinarith
  have hc1 : 1 ≤ (cθ ^ (40 * P.ν)) ^ π.Gsb.order := one_le_pow₀ (Real.one_le_rpow hcθ (by linarith))
  have hL1' : 1 ≤ P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)) :=
    Real.one_le_rpow hL1 (by positivity)
  unfold bsfLow
  calc (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order ≤ 1 * Real.exp _ := by rw [one_mul]; exact hexp
    _ ≤ P.C₂ * Real.exp _ := mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
    _ ≤ P.C₂ * Real.exp _ * (cθ ^ (40 * P.ν)) ^ π.Gsb.order := le_mul_of_one_le_right (by positivity) hc1
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1'

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- **The selected pointwise bound with per-atom scales** (o73 Prop 20.1 at fixed `ξ`; finding F-C5b-1): the selected
atom `v` carries the filter `chiDN(Ω_v/M_v)` at its own scale `M_v ≥ L`. The regimes are split per atom: in the
normal regime only the atoms with `M_v > L^{18c}` are expanded (the others have `φ_v ≥ 1`); in the tiny regime only
the atoms with `μ M_v ≥ 2` are (the others have `κ φ_v ≥ 1`). This is the form for a piece without lower bounds
(ruling R187); `point_bound_atomLow` reduces the lower-bounded atoms to pins. -/
theorem point_bound_atom_nolbLow {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMKG P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMKG P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFullG π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Fama.Stage1PieceG.data π.toStage1PieceGD tt c e h f))
    (sel : Finset (GBranch π.Gsb.tree)) (M : GBranch π.Gsb.tree → ℝ) (hM : ∀ v ∈ sel, P.L ≤ M v)
    (hsel : ∀ v ∈ sel, π.fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M v, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    (hone : ∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') (hlb : π.lb = fun _ => none) :
    ‖splicedKernelMK π.Gsb (π.dataMK tt c e h f) P.L P.γ P.η P.δ base roots‖ ≤
      bsfLow P cθ π * ∏ v ∈ sel, (P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)) := by
  set D := π.dataMK tt c e h f with hDdef
  have hD : SplicedAmplitudeBounds π.Gsb D.toSplicedKernelData := hamp
  have hDlb : D.lb = fun _ => none := hlb
  have hL2 : 2 ≤ P.L := hs.L_ge
  have hL0 : 0 < P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have hM0 : ∀ v ∈ sel, 0 < M v := fun v hv => by linarith [hM v hv]
  have hδ0 := hs.delta_pos
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set φ : GBranch π.Gsb.tree → ℝ := fun v =>
    P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) with hφ
  have hΛ : 1 ≤ P.L ^ (71 * (P.d : ℝ) - 14) := Real.one_le_rpow hL1 (by linarith)
  have hw : ∀ v, 1 ≤ (1 + |f v|) ^ (1 / 18 : ℝ) := fun v =>
    Real.one_le_rpow (by linarith [abs_nonneg (f v)]) (by norm_num)
  have hMp : ∀ v ∈ sel, 0 ≤ M v ^ (-(1 / 18 : ℝ)) := fun v hv => Real.rpow_nonneg (hM0 v hv).le _
  have hφ0 : ∀ v ∈ sel, 0 ≤ φ v := fun v hv => by
    simp only [hφ]; have := hw v; have := hMp v hv; positivity
  have hφM : ∀ v ∈ sel, M v ^ (-(1 / 18 : ℝ)) ≤ φ v := fun v hv => by
    simp only [hφ]
    have := hMp v hv
    calc M v ^ (-(1 / 18 : ℝ)) = 1 * M v ^ (-(1 / 18 : ℝ)) * 1 := by ring
      _ ≤ _ := by gcongr; exact hw v
  have hb0 := bsf_nonnegLow hs hcθ π
  set cc : ℝ := 49 * (P.d : ℝ) - 35 with hcc
  -- an atom at a scale `M_v ≤ L^{18c}` needs no gain
  have hφ1 : ∀ v ∈ sel, M v ≤ P.L ^ (18 * cc) → 1 ≤ φ v := fun v hv hA => by
    have h1 : P.L ^ (-cc) ≤ M v ^ (-(1 / 18 : ℝ)) := by
      calc P.L ^ (-cc) = (P.L ^ (18 * cc)) ^ (-(1 / 18 : ℝ)) := by
            rw [← Real.rpow_mul hL0.le]; congr 1; ring
        _ ≤ M v ^ (-(1 / 18 : ℝ)) := Real.rpow_le_rpow_of_nonpos (hM0 v hv) hA (by norm_num)
    have h2 : 1 ≤ P.L ^ (71 * (P.d : ℝ) - 14) * P.L ^ (-cc) := by
      rw [← Real.rpow_add hL0]; exact Real.one_le_rpow hL1 (by rw [hcc]; linarith)
    have h3 : 0 ≤ P.L ^ (-cc) := Real.rpow_nonneg hL0.le _
    have := hM0 v hv
    simp only [hφ]
    calc (1 : ℝ) ≤ P.L ^ (71 * (P.d : ℝ) - 14) * P.L ^ (-cc) * 1 := by rw [mul_one]; exact h2
      _ ≤ _ := by gcongr; exact hw v
  -- common facts
  have hP := hπ.plain
  set μ : ℝ := P.δ * P.L ^ (2 * P.γ) with hμ
  have hsel' : ∀ v ∈ sel, D.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧
      ∀ u, ψ u = (chiDN u : ℂ) := hsel
  have hord : sel.card ≤ π.Gsb.order := by
    rw [← WaveTurbulence.Ladder.card_branch_eq π.Gsb]; exact Finset.card_le_univ _
  -- the patterns at a subset `S ⊆ sel` of the selected atoms
  have hpatS : ∀ S ⊆ sel, ∀ Bnd : ℝ, 0 ≤ Bnd →
      (∀ D', ModOK S D D' → ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤ Bnd) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ Q ⊆ S, (∀ v ∈ S \ Q, μ * M v / 4 ≤ |f v|) →
        (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * Bnd ≤ (1 / 2) ^ S.card * B) →
      ‖splicedKernelMK π.Gsb D P.L P.γ P.η P.δ base roots‖ ≤ B := by
    intro S hS Bnd hB0 hBnd B hB0' hQB
    have hSone : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b := fun a ha b hb => hone a (hS ha) b (hS hb)
    have hSsel : ∀ v ∈ S, D.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧
        ∀ u, ψ u = (chiDN u : ℂ) := fun v hv => hsel' v (hS hv)
    have hSM : ∀ v ∈ S, 0 < M v := fun v hv => hM0 v (hS hv)
    have hone_pat : ∀ Q ∈ S.powerset, ‖splicedKernelMK π.Gsb
        (modData D D.fix (patInd P.L P.γ P.δ D.frequency S Q)) P.L P.γ P.η P.δ base roots‖ ≤
        (1 / 2) ^ S.card * B := by
      intro Q hQ
      have hQs : Q ⊆ S := Finset.mem_powerset.1 hQ
      by_cases hz : ∃ v ∈ S \ Q, |D.frequency v| < P.δ * P.L ^ (2 * P.γ) * M v / 4
      · obtain ⟨v, hv, hsm⟩ := hz
        rw [pattern_zero hP D hD hDlb hL0 P.γ P.η P.δ hδ0.le base roots S Q M (fun v hv => (hSsel v hv).2) hv
          (hSM v (Finset.mem_sdiff.1 hv).1) hsm, norm_zero]
        exact mul_nonneg (by positivity) hB0'
      · push Not at hz
        exact (pattern_bound hP D hD hDlb hL0 P.γ P.η P.δ hδ0 base roots S Q hQs hSone M hSM hSsel Bnd hB0
          hBnd).trans (hQB Q hQs hz)
    rw [kernel_eq_sum_patterns hP D hD hDlb hL0 P.γ P.η P.δ base roots D.frequency S]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hone_pat).trans ?_)
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, ← mul_assoc]
    push_cast
    rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, one_mul]
  have hγb := gamma_bounds hs
  have hγ0 : 0 ≤ P.γ := le_trans hs.eta_pos.le hγb.1
  have hL2γ : 1 ≤ P.L ^ (2 * P.γ) := Real.one_le_rpow hL1 (by linarith)
  have hδμ : P.δ ≤ μ := by rw [hμ]; nlinarith
  have hp0 : 0 ≤ ∏ v ∈ sel, φ v := Finset.prod_nonneg hφ0
  have hx0 : ∀ v ∈ sel, 0 ≤ 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4) := fun v hv => by
    have := Real.rpow_pos_of_pos hL0 (2 * P.γ); have := hM0 v hv; positivity
  by_cases hB : 4 * P.L ^ (-(18 * cc)) ≤ μ
  · -- normal regime: the gates; only the atoms with `M_v > L^{18c}` are expanded
    set S := sel.filter (fun v => P.L ^ (18 * cc) < M v) with hSdef
    have hS : S ⊆ sel := Finset.filter_subset _ _
    set y : ℝ := P.L ^ (22 * (P.d : ℝ) + 16) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hL0.le _
    have hBnd : ∀ D', ModOK S D D' → ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤
        bsfLow P cθ π * y ^ S.card := by
      intro D' hD'
      have := kernel_bound_modLow hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt c e h f hamp S D'
        hD'
      refine this.trans (le_of_eq ?_)
      have e : P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) +
          (22 * P.d + 16) * (S.card : ℝ)) = P.L ^ ((60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) +
          2 * (π.surv.m : ℝ)) * y ^ S.card := by
        rw [Real.rpow_add hL0, hy, ← Real.rpow_mul_natCast hL0.le]
      unfold bsfLow
      rw [e]
      ring
    have hSφ : ∏ v ∈ S, φ v ≤ ∏ v ∈ sel, φ v :=
      prod_le_prod_of_subset_one_le hS φ (fun v hv => hφ0 v (hS hv)) fun v hv => by
        obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
        exact hφ1 v hv1 (not_lt.1 fun hlt => hv2 (Finset.mem_filter.2 ⟨hv1, hlt⟩))
    refine hpatS S hS _ (mul_nonneg hb0 (pow_nonneg hy0 _)) hBnd _ (mul_nonneg hb0 hp0) fun Q hQs hhigh => ?_
    have hprod := pattern_prod_le_atom S Q hQs (fun v => 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) y
      (fun v hv => hx0 v (hS (hQs hv))) hy0 φ (fun v hv => ?_) (fun v hv => ?_)
    · have hSp : 0 ≤ ∏ v ∈ S, φ v := Finset.prod_nonneg fun v hv => hφ0 v (hS hv)
      calc (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * (bsfLow P cθ π * y ^ S.card)
          = bsfLow P cθ π * ((∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * y ^ S.card) := by ring
        _ ≤ bsfLow P cθ π * ((1 / 2) ^ S.card * ∏ v ∈ S, φ v) := mul_le_mul_of_nonneg_left hprod hb0
        _ ≤ bsfLow P cθ π * ((1 / 2) ^ S.card * ∏ v ∈ sel, φ v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSφ (by positivity)) hb0
        _ = (1 / 2) ^ S.card * (bsfLow P cθ π * ∏ v ∈ sel, φ v) := by ring
    · have hvS := hQs hv
      have hvsel := hS hvS
      have hMv : P.L ^ (18 * cc) < M v := (Finset.mem_filter.1 hvS).2
      have := atom_low_normal hL2 hd' hB hMv
      have := hMp v hvsel
      calc 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * y
          ≤ P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) := by assumption
        _ ≤ φ v := by
          simp only [hφ]
          calc P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ))
              = P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr; exact hw v
    · exact atom_high_normal hL2 hd' hB (hM0 v (hS (Finset.mem_sdiff.1 hv).1)) (hhigh v hv)
  · -- tiny regime: the trivial bound; only the atoms with `μ M_v ≥ 2` are expanded
    push Not at hB
    have hδL : P.δ ≤ P.L ^ (-(12 * (P.d : ℝ) + 14)) := by
      have h1 : 4 * P.L ^ (-(18 * cc)) ≤ P.L ^ (-(12 * (P.d : ℝ) + 14)) := by
        have h2 : (4 : ℝ) ≤ P.L ^ (18 * cc - (12 * (P.d : ℝ) + 14)) := by
          calc (4 : ℝ) ≤ P.L ^ (2 : ℝ) := by
                rw [show (P.L ^ (2 : ℝ)) = P.L ^ (2 : ℕ) by norm_cast]; nlinarith
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hcc]; linarith)
        calc 4 * P.L ^ (-(18 * cc)) ≤ P.L ^ (18 * cc - (12 * (P.d : ℝ) + 14)) * P.L ^ (-(18 * cc)) := by
              gcongr
          _ = P.L ^ (-(12 * (P.d : ℝ) + 14)) := by rw [← Real.rpow_add hL0]; congr 1; ring
      linarith
    set κ : ℝ := 32 * P.δ ^ (-(1 / 18 : ℝ)) with hκ
    have hκ1 : 1 ≤ κ := by
      have : 1 ≤ P.δ ^ (-(1 / 18 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hs.delta_le (by norm_num)
      linarith
    set T : ℝ := ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) with hT
    have hT0 : 0 ≤ T := by positivity
    have hcore : T * κ ^ π.Gsb.order ≤ bsfLow P cθ π := by
      have hcoup : ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ = P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ)) := by
        unfold coupling
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hb : π.Gsb.molecule.bonds.card ≤ 2 * π.Gsb.order := by have := hπ.bond_count; omega
      have hRo : (R : ℝ) ≤ 2 * π.Gsb.order := by have := hπ.bond_count; exact_mod_cast (by omega : R ≤ 2 * π.Gsb.order)
      have hgsb : (π.gsb : ℝ) ≤ π.Gsb.order := by
        have := WaveTurbulence.Represents.totalIncoherency_le_atoms hπ.molecule π.ladders π.layer
        rw [hπ.atom_count] at this; exact_mod_cast this
      have hρ : (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ) ≤ 2 * π.Gsb.order := by
        have h1 := WaveTurbulence.Represents.rho_le_atoms hπ.molecule
        rw [hπ.atom_count] at h1
        have h2 : π.Cs.hinges.card ≤ π.Gsb.order := by
          rw [← WaveTurbulence.Ladder.card_branch_eq π.Gsb]; exact Finset.card_le_univ _
        have : π.Gsb.molecule.rho + π.Cs.hinges.card ≤ 2 * π.Gsb.order := by omega
        exact_mod_cast this
      have h1 := tiny_core (γ := P.γ) (n := π.Gsb.order) (b := π.Gsb.molecule.bonds.card) hL2 hd' hδ0 hδL
        hs.nu_pos.le
        hs.nu_small (by linarith [hγb.2, hs.eta_le]) hb P.d rfl
      have h2 := bsf_lowerLow hs hcθ π hgsb hρ hRo
      rw [hT, hcoup]
      calc (P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ))) ^ π.Gsb.order *
            (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) * κ ^ π.Gsb.order ≤
          (P.δ ^ (10 * P.ν) / P.L) ^ π.Gsb.order := h1
        _ ≤ _ := h2
    have hκord : κ ^ sel.card ≤ κ ^ π.Gsb.order := pow_le_pow_right₀ hκ1 hord
    have hTD : ∀ S : Finset (GBranch π.Gsb.tree), ∀ D', ModOK S D D' →
        ‖splicedKernelMK π.Gsb D' P.L P.γ P.η P.δ base roots‖ ≤ T := by
      intro S D' hD'
      have hdat : D'.toSplicedKernelData = D.toSplicedKernelData := hD'.data
      obtain ⟨g, hg, -, hi⟩ := hD'.ind
      refine norm_kernel_le_trivial hP D' (by rw [hdat]; exact hD) (fun a q hq u => ?_) (fun k => ?_) hL0
        P.γ P.η P.δ base roots
      · have hq' : π.filt a = some q := by
          have h2 := hD'.filt; rw [h2] at hq; exact hq
        exact (hπ.filt_ok a q hq').2.2.1 u
      · rw [hi k]; have h1 := hπ.ind_ok k
        exact ⟨mul_nonneg h1.1 (hg k).1, (mul_le_mul h1.2 (hg k).2 (hg k).1 zero_le_one).trans_eq (one_mul 1)⟩
    set S := sel.filter (fun v => 2 ≤ μ * M v) with hSdef
    have hS : S ⊆ sel := Finset.filter_subset _ _
    have hκφ0 : ∀ v ∈ sel, 0 ≤ κ * φ v := fun v hv => mul_nonneg (by linarith) (hφ0 v hv)
    have hκS : ∏ v ∈ S, κ * φ v ≤ κ ^ π.Gsb.order * ∏ v ∈ sel, φ v := by
      calc ∏ v ∈ S, κ * φ v ≤ ∏ v ∈ sel, κ * φ v :=
            prod_le_prod_of_subset_one_le hS (fun v => κ * φ v) (fun v hv => hκφ0 v (hS hv)) fun v hv => by
              obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
              have hC : μ * M v < 2 := not_le.1 fun hle => hv2 (Finset.mem_filter.2 ⟨hv1, hle⟩)
              have := atom_tiny_small hδ0 hδμ (hM0 v hv1) hC
              calc (1 : ℝ) ≤ M v ^ (-(1 / 18 : ℝ)) * κ := this
                _ ≤ κ * φ v := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hφM v hv1) (by linarith)
        _ = κ ^ sel.card * ∏ v ∈ sel, φ v := by rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ κ ^ π.Gsb.order * ∏ v ∈ sel, φ v := mul_le_mul_of_nonneg_right hκord hp0
    refine hpatS S hS T hT0 (hTD S) _ (mul_nonneg hb0 hp0) fun Q hQs hhigh => ?_
    have hprod := pattern_prod_le_atom S Q hQs (fun v => 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) 1
      (fun v hv => hx0 v (hS (hQs hv))) zero_le_one (fun v => κ * φ v) (fun v hv => ?_) (fun v hv => ?_)
    · rw [one_pow, mul_one] at hprod
      have hκ0 : 0 ≤ κ ^ π.Gsb.order := pow_nonneg (by linarith) _
      calc (∏ v ∈ Q, 12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * T
          ≤ ((1 / 2) ^ S.card * ∏ v ∈ S, κ * φ v) * T := mul_le_mul_of_nonneg_right hprod hT0
        _ ≤ ((1 / 2) ^ S.card * (κ ^ π.Gsb.order * ∏ v ∈ sel, φ v)) * T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκS (by positivity)) hT0
        _ = (1 / 2) ^ S.card * (T * κ ^ π.Gsb.order) * ∏ v ∈ sel, φ v := by ring
        _ ≤ (1 / 2) ^ S.card * bsfLow P cθ π * ∏ v ∈ sel, φ v :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore (by positivity)) hp0
        _ = (1 / 2) ^ S.card * (bsfLow P cθ π * ∏ v ∈ sel, φ v) := by ring
    · have hvS := hQs hv
      have hvsel := hS hvS
      have hC : 2 ≤ μ * M v := (Finset.mem_filter.1 hvS).2
      have := atom_low_tiny hδ0 hδμ hC
      calc 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) * 1
          = 2 * (12 / (Real.pi * (P.δ * P.L ^ (2 * P.γ) * M v) / 4)) := mul_one _
        _ ≤ M v ^ (-(1 / 18 : ℝ)) * κ := this
        _ ≤ κ * φ v := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hφM v hvsel) (by linarith)
    · have hvsel := hS (Finset.mem_sdiff.1 hv).1
      have := atom_high_tiny hδ0 hδμ (hM0 v hvsel) (hhigh v hv)
      have := hMp v hvsel
      calc 2 * (1 : ℝ) = 2 := mul_one _
        _ ≤ M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) * κ := by assumption
        _ ≤ κ * φ v := by
            rw [mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            simp only [hφ]
            calc M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)
                = 1 * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ) := by ring
              _ ≤ _ := by gcongr

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- Ruling R187: pinning the lower-bounded atoms of a sound piece inside their layer windows and dropping the lower
bounds keeps it sound (the pinned atoms are protected, `lb_prot`). -/
theorem soundMKFull_pinLBLow {P : WTParams} {R p : ℕ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {cθ : ℝ}
    {π : Stage1PieceMKG P R} (hπ : SoundMKFullG π p base roots cθ) (fix' : GBranch π.Gsb.tree → Option ℝ)
    (h1 : ∀ b, π.lb b = none → fix' b = π.fix b)
    (h2 : ∀ b, (π.lb b).isSome → fix' b = π.fix b ∨ ∃ r, fix' b = some r ∧ (π.layer b : ℝ) ≤ r ∧ r ≤ π.layer b + 1) :
    SoundMKFullG { π with fix := fix', lb := fun _ => none } p base roots cθ where
  plain := hπ.plain
  irreducible := hπ.irreducible
  balanced := hπ.balanced
  order_pos := hπ.order_pos
  order_le := hπ.order_le
  layer_le := hπ.layer_le
  survivors := hπ.survivors
  survivors_card := hπ.survivors_card
  prot_card := hπ.prot_card
  molecule := hπ.molecule
  connected := hπ.connected
  atom_count := hπ.atom_count
  bond_count := hπ.bond_count
  structural := hπ.structural
  support := hπ.support
  hingeOutsideFirst := hπ.hingeOutsideFirst
  tripleDesignated := hπ.tripleDesignated
  hingeNoLoop := hπ.hingeNoLoop
  chainOrder := hπ.chainOrder
  fix_prot := fun b hb => by
    have hb' : (fix' b).isSome := hb
    by_cases hl : π.lb b = none
    · rw [h1 b hl] at hb'; exact hπ.fix_prot b hb'
    · exact hπ.lb_prot b (Option.isSome_iff_ne_none.2 hl)
  fix_layer := fun b t ht => by
    have ht' : fix' b = some t := ht
    by_cases hl : π.lb b = none
    · rw [h1 b hl] at ht'; exact hπ.fix_layer b t ht'
    · rcases h2 b (Option.isSome_iff_ne_none.2 hl) with e | ⟨r, hr, hr1, hr2⟩
      · rw [e] at ht'; exact hπ.fix_layer b t ht'
      · rw [hr] at ht'; cases ht'; exact ⟨hr1, hr2⟩
  filt_ok := hπ.filt_ok
  ind_ok := hπ.ind_ok
  ind_local := hπ.ind_local
  lb_free := fun b hb => by simp at hb
  lb_prot := fun b hb => by simp at hb
  lb_layer := fun b x hb => by simp at hb

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece WaveTurbulence.Flower.FinalMKFine

/-- **The selected pointwise bound with per-atom scales** (`point_bound_atom_nolbLow` for every piece; ruling R187: the
selected atoms carry no lower bound, the other lower-bounded atoms are pinned inside their windows and integrated
over a window of length `≤ 1`, `FinalMKFine.norm_kernelMK_le_of_pinLB`). -/
theorem point_bound_atomLow {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMKG P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMKG P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFullG π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Fama.Stage1PieceG.data π.toStage1PieceGD tt c e h f))
    (sel : Finset (GBranch π.Gsb.tree)) (M : GBranch π.Gsb.tree → ℝ) (hM : ∀ v ∈ sel, P.L ≤ M v)
    (hsel : ∀ v ∈ sel, π.fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M v, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    (hone : ∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') (hlbsel : ∀ v ∈ sel, π.lb v = none) :
    ‖splicedKernelMK π.Gsb (π.dataMK tt c e h f) P.L P.γ P.η P.δ base roots‖ ≤
      bsfLow P cθ π * ∏ v ∈ sel, (P.L ^ (71 * (P.d : ℝ) - 14) * M v ^ (-(1 / 18 : ℝ)) * (1 + |f v|) ^ (1 / 18 : ℝ)) := by
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  refine FinalMKFine.norm_kernelMK_le_of_pinLB hπ.plain hL0 P.γ P.η P.δ base roots _ (π.dataMK tt c e h f) hamp
    fun fix' hpins => ?_
  have hπ' := soundMKFull_pinLBLow hπ fix' hpins.1 hpins.2
  exact point_bound_atom_nolbLow hs hd hcθ hcoarse hfine hp hR hRmax { π with fix := fix', lb := fun _ => none } base
    roots hπ' hnsb hnL tt c e h f hamp sel M hM
    (fun v hv => ⟨(hpins.1 v (hlbsel v hv)).trans (hsel v hv).1, (hsel v hv).2⟩) hone rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece

/-- **The selected piece bound with per-tree scales** (o73 Prop 20.1, finding F-C5b-1), for `1 ≤ d`. -/
theorem markedPieceBoundSelAtT_of_one_le_dLow {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (_hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMKG P) :
    MarkedPieceBoundSelAtTG cP cθ P := by
  intro p R n hp hR hRmax π sel Ms hM hsel hone hlbsel tt base roots hπ hnsb hnL val s hs0 hval
  obtain ⟨Ξ, _, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwbound, hD⟩ := hval
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hMs0 : 0 ≤ ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) :=
    Finset.prod_nonneg fun v hv => Real.rpow_nonneg (by linarith [hM v hv]) _
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  set a : ℝ := (sel.card : ℝ) with ha
  set M : ℝ := P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) with hMdef
  set cq : ℝ := cθ ^ (40 * P.ν) with hcq
  set Ek : ℝ := (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) with hEk
  set a0 : ℝ := cP * P.d * (π.nProt : ℝ) with ha0
  set Gsel : ℝ := P.L ^ ((71 * (P.d : ℝ) - 14) * a) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) with hGsel
  set Wf : Ξ → ℝ := fun ξ => ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) with hWf
  have hcq1 : 1 ≤ cq := Real.one_le_rpow hcθ (by have := hs.nu_pos; linarith)
  have hM0' : 0 ≤ M := by rw [hMdef]; exact mul_nonneg hC2 (Real.exp_pos _).le
  have hG0 : 0 ≤ Gsel := by positivity
  have hbsf : bsfLow P cθ π = M * cq ^ π.Gsb.order * P.L ^ Ek := rfl
  -- the pointwise bound
  have hKle : ∀ ξ, ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) * Wf ξ := by
    intro ξ
    have := point_bound_atomLow hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt (ctr ξ) (edge ξ)
      (hinge ξ) (freq ξ) (hD ξ) sel (fun v => Ms v.1.1) hM hsel hone hlbsel
    rw [prod_sel_factor_atom sel hL0] at this
    refine this.trans (le_of_eq ?_)
    rw [hbsf, hGsel, hWf]; ring
  have hMt0 : 0 ≤ M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel := by positivity
  have hpt : ∀ ξ, ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ ‖w ξ‖ * Wf ξ * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by
    intro ξ
    rw [norm_mul]
    calc ‖w ξ‖ * ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
          P.L P.γ P.η P.δ base roots‖ ≤ ‖w ξ‖ * ((M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) * Wf ξ) :=
          mul_le_mul_of_nonneg_left (hKle ξ) (norm_nonneg _)
      _ = ‖w ξ‖ * Wf ξ * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by ring
  have hnorm : ‖val‖ ≤ (∫ ξ, ‖w ξ‖ * Wf ξ ∂μ) * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by
    rw [hv]
    have h := norm_integral_le_of_norm_le (hwint.mul_const (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel))
      (Filter.Eventually.of_forall hpt)
    simpa only [integral_mul_const] using h
  set W : ℝ := ∫ ξ, ‖w ξ‖ * Wf ξ ∂μ with hW
  have hW0 : 0 ≤ W := integral_nonneg fun ξ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (by linarith [abs_nonneg (freq ξ v)]) _)
  set Ls : ℝ := P.L ^ (7 * (47 * P.d + 2) * a) with hLs
  have hLa : 0 < P.L ^ a0 := Real.rpow_pos_of_pos hL0 _
  have hLs0 : 0 < Ls := Real.rpow_pos_of_pos hL0 _
  have hden : 0 < s * P.L ^ a0 * Ls := by positivity
  set W' : ℝ := W / (s * P.L ^ a0 * Ls) with hW'
  have hW'0 : 0 ≤ W' := div_nonneg hW0 hden.le
  have hwb : W' ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    rw [hW', div_le_iff₀ hden]
    calc W ≤ _ := hwbound
      _ = _ := by ring
  have hcls := class_piece_bound (C := P.C₁) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν)
    (n := n) (nsb := π.Gsb.order) (R := R) (m := π.Gsb.order + 2 * R) (W := W') (X := M) (H := P.C₂)
    (gsk := (π.gsk : ℝ)) (bsk := (π.bsk : ℝ)) (qsk := (π.Cs.hinges.card : ℝ))
    (gsb := (π.gsb : ℝ)) (ρsb := (π.Gsb.molecule.rho : ℝ))
    hs.c1_ge hs.delta_pos hs.delta_le hL1 hs.nu_pos (by linarith [hs.nu_small]) hs.nu_eta
    hs.eta_pos hs.eta_le hnsb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC2 hW'0 hM0' hwb (by rw [hMdef])
  have hcqn : cq ^ π.Gsb.order ≤ cq ^ n := pow_le_pow_right₀ hcq1 hnsb
  have hWeq : W = W' * (s * P.L ^ a0 * Ls) := by rw [hW']; field_simp
  have hT0 : 0 ≤ P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    have := hs.c1_ge; have := hs.delta_pos; positivity
  have hmext : P.L ^ markedExtraG cP π = P.L ^ a0 * P.L ^ Ek := by
    rw [← Real.rpow_add hL0]; congr 1; unfold markedExtraG; simp only [ha0, hEk]; ring
  have hsel400 : Ls * Gsel = P.L ^ (400 * (P.d : ℝ) * a) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) := by
    rw [hLs, hGsel, ← mul_assoc, ← Real.rpow_add hL0]; congr 2; ring
  calc ‖val‖ ≤ W * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := hnorm
    _ = s * P.L ^ a0 * P.L ^ Ek * cq ^ π.Gsb.order * (W' * M) * (Ls * Gsel) := by rw [hWeq]; ring
    _ ≤ s * P.L ^ a0 * P.L ^ Ek * cq ^ n *
        (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) * (Ls * Gsel) := by
        gcongr
    _ = _ := by rw [hmext, hsel400, mul_pow, mul_pow, hcq]; ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKPiece

/-- **The selected class sum with per-tree scales** (finding F-C5b-1) from the per-tree selected piece bound: the
selected trees of every piece are `T`, so the per-piece factor `L^{400d·#T} ∏_{j∈T} Ms_j^{-1/18}` is uniform and is
divided out together with `s L^X`. -/
theorem markedSumBoundSelAtTLow {P : WTParams} (hs : PieceSmall P) {cP cθ : ℝ} (X : ℝ)
    (hcθ : 1 ≤ cθ) (hpb : MarkedPieceBoundSelAtTG cP cθ P) : MarkedSumBoundSelAtTG cP cθ X P := by
  intro p R n hp hR hRmax S sel T Ms tt base roots C₀ Cl hCl cls s hs0 hMT himg hsel hone hlbsel hsound hnsb hnL hrep
    hX hcnt hT2 hS2
  let _ := S.fin
  obtain ⟨hrb, hgb, hpc⟩ := hcnt
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hC1 : 0 < P.C₁ := by linarith [hs.c1_ge]
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  set Gs : ℝ := P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)) * ∏ j ∈ T, Ms j ^ (-(1 / 18 : ℝ)) with hGs
  have hGs0 : 0 < Gs := mul_pos (Real.rpow_pos_of_pos hL0 _)
    (Finset.prod_pos fun j hj => Real.rpow_pos_of_pos (by linarith [hMT j hj]) _)
  have hLX : 0 < P.L ^ X := Real.rpow_pos_of_pos hL0 _
  have hsX : 0 < s * P.L ^ X * Gs := mul_pos (mul_pos hs0 hLX) hGs0
  have hcq1 : 0 ≤ cθ ^ (40 * P.ν) := Real.rpow_nonneg (by linarith) _
  have hpiece : ∀ π, ‖S.val π / ((s * P.L ^ X * Gs : ℝ) : ℂ)‖ ≤ P.C₂ *
      (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
      (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    intro π
    have hinj : Set.InjOn (fun v : GBranch (S.piece π).Gsb.tree => v.1.1) (sel π) :=
      fun x hx y hy hxy => hone π x hx y hy hxy
    have hM : ∀ v ∈ sel π, P.L ≤ Ms v.1.1 := fun v hv =>
      hMT _ (by rw [← himg π]; exact Finset.mem_image_of_mem _ hv)
    have hcardT : (sel π).card = T.card := by rw [← himg π, Finset.card_image_of_injOn hinj]
    have hprodT : ∏ v ∈ sel π, Ms v.1.1 ^ (-(1 / 18 : ℝ)) = ∏ j ∈ T, Ms j ^ (-(1 / 18 : ℝ)) := by
      rw [← himg π, Finset.prod_image hinj]
    have h := hpb hp hR hRmax (S.piece π) (sel π) Ms hM (hsel π) (hone π) (hlbsel π) tt base roots (hsound π)
      (hnsb π) hnL
      (S.val π) s hs0 (hrep π)
    rw [hcardT, hprodT] at h
    have hme : P.L ^ markedExtraG cP (S.piece π) ≤ P.L ^ X :=
      Real.rpow_le_rpow_of_exponent_le hL1 (hX π)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsX.le, div_le_iff₀ hsX]
    have hRn : R ≤ 2 * n := by
      have h1 := (hsound π).bond_count
      have h2 := hnsb π
      omega
    have hCn : P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤ P.C₁ ^ (5 * n) :=
      pow_le_pow_right₀ hs.c1_ge (by have := hnsb π; omega)
    have hδp : (0 : ℝ) ≤ P.δ ^ (10 * P.ν) := Real.rpow_nonneg hs.delta_pos.le _
    have hcore : (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤
        (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by
      calc (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)
          ≤ (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (5 * n) :=
            mul_le_mul_of_nonneg_left hCn (by positivity)
        _ = (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by
            rw [pow_mul, ← mul_pow]; congr 1; ring
    have hrw : P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) =
        P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
      rw [← Real.rpow_mul_natCast hL0.le, ← Real.rpow_mul_natCast hL0.le]
      simp only [Fama.Stage1PieceGD.gbar, Fama.Stage1PieceGD.rbar, Nat.cast_add]
      ring_nf
    rw [hrw]
    have hL1' : 0 ≤ P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) :=
      Real.rpow_nonneg hL0.le _
    have hL2 : 0 ≤ P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
        (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) := Real.rpow_nonneg hL0.le _
    have hL3 : 0 ≤ P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := Real.rpow_nonneg hL0.le _
    have hmain : P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
        P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) ≤
        P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
      calc _ = P.C₂ * ((cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
              P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)) *
            (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
            P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
              (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
            P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by ring
        _ ≤ _ := by gcongr
    have hpos : 0 ≤ P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
        P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℝ))) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by positivity
    have key : ∀ T T' : ℝ, 0 ≤ T → T ≤ T' → ‖S.val π‖ ≤ s * P.L ^ markedExtraG cP (S.piece π) * T * Gs →
        ‖S.val π‖ ≤ T' * (s * P.L ^ X * Gs) := by
      intro T T' hT hTT' hh
      calc ‖S.val π‖ ≤ s * P.L ^ markedExtraG cP (S.piece π) * T * Gs := hh
        _ ≤ s * P.L ^ X * T * Gs := by gcongr
        _ ≤ s * P.L ^ X * T' * Gs := by gcongr
        _ = T' * (s * P.L ^ X * Gs) := by ring
    exact key _ _ hpos hmain (h.trans_eq (by rw [hGs]; ring))
  have hdelta : (0 : ℝ) ≤ cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν) :=
    mul_nonneg (mul_nonneg hcq1 (by positivity)) (Real.rpow_nonneg hs.delta_pos.le _)
  have hcls := class_sum_bound (fun π => S.val π / ((s * P.L ^ X * Gs : ℝ) : ℂ))
    (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R (6 * C₀)
    P.C₂ (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) (P.L ^ (-(P.ν * P.η))) (P.L ^ (-P.η ^ 6 / 4))
    (P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) P.C₂ hC2 hdelta (Real.rpow_nonneg hL0.le _)
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _) hC2 hpiece hrb hgb
    (piece_count_of_direct_count (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R C₀ P.C₂
      hC2 (by exact hpc)) hT2 hS2
  have hsum : ∑ π, S.val π / ((s * P.L ^ X * Gs : ℝ) : ℂ) = (∑ π, S.val π) / ((s * P.L ^ X * Gs : ℝ) : ℂ) := by
    rw [Finset.sum_div]
  rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hsX.le, div_le_iff₀ hsX] at hcls
  refine hcls.trans_eq ?_
  ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs

/-- The selected piece bound and class sum chained with per-tree scales (finding F-C5b-1), for `1 ≤ d`. -/
theorem markedSumBoundSelT_of_gatesLow {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hc : CoarseSplicedAtMK P) (hf : FineSplicedAtMKG P) (X : ℝ) :
    MarkedSumBoundSelAtTG cP cθ X P :=
  markedSumBoundSelAtTLow hs X hcθ (markedPieceBoundSelAtT_of_one_le_dLow hd hs hcP hcθ hc hf)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs

/-- **`SelSumTargetTG`** (C5b's D7 input, finding F-C5b-1): the per-tree selected class sum under `1 ≤ d`,
`PieceSmall` and the gates. -/
theorem selSumTargetTG : SelSumTargetTG :=
  fun _ _ hcP hcθ _ hd hs hc hf _ X => markedSumBoundSelT_of_gatesLow hd hs hcP hcθ hc hf X

end

end WaveTurbulence.GammaLow.Flower
