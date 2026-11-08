/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Expand
public import WaveTurbulence.Foundations.Flower.FinalMKPiece.Kernel

/-! # D7 SEL-RES / Gate: the crude and fine gates on the modified piece data

`kernel_bound_mod`: for a modification `ModOK sel (π.dataMK …) D'`, the θ = 40ν interpolation of
`CoarseSplicedAtMK` (split `joints ∪ prot ∪ sel ∪ Rc`) and `FineSplicedAtMK` (`E = prot ∪ sel ∪ Rc`), `#Rc ≤ #sel`,
is C5a's `kernel_bound` times `L^{(22d+16)·#sel}`. The proof is C5a's `kernel_bound` (world
`FinalMKPiece/Kernel.lean`) with the two sets enlarged (`extra_le_sel`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.FinalMKPiece

/-- The extra exponent with `2a` more split atoms and `2a` more exceptional atoms (`a = #sel`). -/
theorem extra_le_sel {d ν m np K E a : ℝ} (hd : 1 ≤ d) (hν0 : 0 ≤ ν) (hν : 40 * ν ≤ 1 / 100) (hm : 0 ≤ m)
    (hnp : 0 ≤ np) (hK0 : 0 ≤ K) (hK : K ≤ 2 * m + 2 * np) (hE0 : 0 ≤ E) (hE : E ≤ 2 * np) (ha : 0 ≤ a)
    (K' E' : ℝ) (hK' : K' ≤ K + 2 * a) (hE' : E' ≤ E + 2 * a) :
    40 * ν * (80 * d * K') + (2 * m + 2 * ((5 * d + 4) * E')) ≤
      (60 * d + 2) * (2 * m + 2 * np) + 2 * m + (22 * d + 16) * a := by
  have h0 := extra_le hd hν0 hν hm hnp hK0 hK hE0 hE
  have h1 : 40 * ν * (80 * d * K') ≤ 40 * ν * (80 * d * K) + 40 * ν * (80 * d * (2 * a)) := by
    have : 80 * d * K' ≤ 80 * d * K + 80 * d * (2 * a) := by nlinarith
    nlinarith
  have h2 : 40 * ν * (80 * d * (2 * a)) ≤ 2 * d * a := by
    have : 0 ≤ d * a := by nlinarith
    nlinarith
  have h3 : (5 * d + 4) * E' ≤ (5 * d + 4) * E + (5 * d + 4) * (2 * a) :=
    by nlinarith
  nlinarith

/-- **The gate bound for the modified piece data** (C5a's `kernel_bound` with split `joints ∪ prot ∪ sel ∪ Rc`
and `E = prot ∪ sel ∪ Rc`, `#Rc ≤ #sel`). -/
theorem kernel_bound_mod {P : WTParams} (hs : PieceSmall P) (hd : 1 ≤ P.d) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1PieceMK P.d R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : SoundMKFull π p base roots cθ) (hnsb : π.Gsb.order ≤ n) (hnL : ((n : ℝ) + 1) ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (c : GardenDart π.Gsb → Mom P.d) (e : GardenDart π.Gsb → Mom P.d → ℂ)
    (h : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (f : GBranch π.Gsb.tree → ℝ)
    (hamp : SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt c e h f))
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
  have hD'd : D'.toSplicedKernelData = Stage1Piece.data π.toStage1PieceD tt c e h f := hdata
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
  have hconc : SubproConclusionsMK π.Gsb D'.toSplicedKernelData π.Cs π.surv P.L P.γ P.η base roots := by
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
    have h2 := joints_card_le π.surv
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

end WaveTurbulence.Flower.SelRes
