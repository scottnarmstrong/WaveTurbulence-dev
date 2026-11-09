/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Statement
public import WaveTurbulence.Foundations.Flower.CompMK.Top

/-! # FLOWER-LOW (packet L8), item F: the non-regular part over `𝒱_γ`, `0 < γ ≤ 1/2`

Main's `Flower.CompMK.{Mono, Restrict, Numerics, Top, NonReg, Prefix}` carrier-dependent declarations, copied by
source (sha256 in `COPIED-SHA256SUMS`) onto the `𝒱_γ` marked carrier of `Carrier/` (`Stage1DataMKG`,
`Stage1ReductionAtMKSelG`, `SelSumTargetTG`, `FineSplicedAtMKG`, …), with `1 / 2 < P.γ` ↦ `P.γ ≤ 1 / 2`. The
family-free parts of CompMK (`Sum`, `Card`, the numerics `bracket_le`, `budget_le`, `budget_17999`, the prefix
helpers, `coarseSplicedAtMK_largeConstantMonotone`, `ladderFourierAtMKFace_largeConstantMonotone`) are main's, by
import, as are the C2 and C4a gates `FinalMKCrude.coarseSplicedGateMK`, `FinalMKPin.ladderFourierMKFace_prefix`.
One change beyond the carrier: main's proved γ > 1/2 fine gate `FinalMKFine.fineSplicedGateHalfMK` becomes the
hypothesis `hFine : FineSplicedGateLowMK` (PLAN-L8 item H).

**`nonregLowTarget_of`**: `NonregLowTarget` from item I's marked Stage-1′ gate, item G's `SelSumTargetTG` and
item H's `FineSplicedGateLowMK` (conditional helper). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem fineSplicedLowMK_largeConstantMonotone :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → FineSplicedAtMKG P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ p hp R hR hRmax G hplain hirr hbal hn hnmax D Cs S E hD hlayer hfilt hind
    hfixE hfixT hlbE base roots hgeom hconc
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h hγ p hp R hR hRmax G hplain hirr hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlbE base
    roots hgeom hconc
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hδ0 : 0 ≤ P.δ ^ (-10 * P.ν) := Real.rpow_nonneg hδ.le _
  have hrest : 0 ≤ P.L ^ (2 * (S.m : ℝ)) * (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
      P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
    positivity
  have hmono : P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order ≤ c₁ * (c₁ * P.δ ^ (-10 * P.ν)) ^ G.order :=
    mul_le_mul h₁ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
      (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)
  calc P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))
      = (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order) * (P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) := by
        ring
    _ ≤ (c₁ * (c₁ * P.δ ^ (-10 * P.ν)) ^ G.order) * (P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) :=
        mul_le_mul_of_nonneg_right hmono hrest
    _ = _ := by ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem representsIntMKSel_largeConstantsLow {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMKG P R) (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : RepresentsIntMKSelG π sel n cP tt base roots s val) :
    RepresentsIntMKSelG (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb.trans ?_, hD⟩
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  have hAC := mul_le_mul hpow hpow2 hC hB
  have hrest : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * P.L ^ (cP * P.d * (π.nProt : ℝ)) *
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s := by positivity
  calc (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s
      = ((P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R)) *
        (P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) := by ring
    _ ≤ ((c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * c₁ ^ (π.Gsb.order + 2 * R)) *
        (P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) :=
        mul_le_mul_of_nonneg_right hAC hrest
    _ = _ := by ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem soundMKFull_largeConstantsLow {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1PieceMKG P R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) (h : SoundMKFullG π p base roots cθ) :
    SoundMKFullG (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π p base roots cθ :=
  { plain := h.plain, irreducible := h.irreducible, balanced := h.balanced, order_pos := h.order_pos,
    order_le := by rw [N_largeConstants]; exact h.order_le, layer_le := h.layer_le, survivors := h.survivors,
    survivors_card := h.survivors_card, prot_card := h.prot_card,
    molecule := h.molecule, connected := h.connected, atom_count := h.atom_count, bond_count := h.bond_count,
    structural := h.structural, support := h.support, hingeOutsideFirst := h.hingeOutsideFirst,
    tripleDesignated := h.tripleDesignated, hingeNoLoop := h.hingeNoLoop, chainOrder := h.chainOrder,
    fix_prot := h.fix_prot, fix_layer := h.fix_layer, filt_ok := h.filt_ok, ind_ok := h.ind_ok,
    ind_local := h.ind_local, lb_free := h.lb_free, lb_prot := h.lb_prot, lb_layer := h.lb_layer }

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem stage1ReductionAtMKSel_largeConstantMonotoneLow (C₀ : ℕ) (cP cθ : ℝ) :
    LargeConstantMonotone (Stage1ReductionAtMKSelG C₀ cP cθ) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs
    hhigh
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hN
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcounts⟩ :=
    h p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A
      (fun LG hLG => ⟨mkCarries_largeConstants c₁ c₂ (hA LG hLG).1, (hA LG hLG).2⟩) hplain hTC roots hh b Rf σ Rs
      dag hb hhb hRf hRs hhigh
  refine ⟨⟨S.Pc, S.fin, S.piece, S.val⟩, Cl, hCl, cls, members, sel, selR, hpart, fun π => ?_,
    fun π => soundMKFull_largeConstantsLow c₁ c₂ (S.piece π) p 0 roots cθ (hsound π), hord, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpc π
    have hL0 : (0 : ℝ) ≤ P.L := by linarith
    refine ⟨h1, representsIntMKSel_largeConstantsLow c₁ c₂ h₁ (by linarith) hL0 (S.piece π) (selR π) N cP _ 0 roots
      _ (selMass_nonneg N (by linarith) (fun j => by linarith [hRs j]) kSel _) (S.val π) h2, h3, h4, h5, h6⟩
  · obtain ⟨hr, hg, hcnt⟩ := hcounts
    refine ⟨hr, hg, fun g r => (hcnt g r).trans ?_⟩
    have hC₂0 : 0 ≤ P.C₂ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC₂0 h₂ _) (by positivity)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- The pieces of `S` satisfying `q`. -/
def restrictDataLow {P : WTParams} {R : ℕ} (S : Stage1DataMKG P R) (q : S.Pc → Prop) : Stage1DataMKG P R where
  Pc := {π // q π}
  fin := @Subtype.fintype _ q (Classical.decPred q) S.fin
  piece := fun π => S.piece π.1
  val := fun π => S.val π.1

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem sum_restrictDataLow {P : WTParams} {R : ℕ} (S : Stage1DataMKG P R) (q : S.Pc → Prop) :
    @Finset.sum (restrictDataLow S q).Pc ℂ _ (@univ _ (restrictDataLow S q).fin) (restrictDataLow S q).val =
      @Finset.sum S.Pc ℂ _ (@Finset.filter S.Pc q (Classical.decPred q) (@univ S.Pc S.fin)) S.val := by
  letI := S.fin
  change ∑ π : {π // q π}, S.val π.1 = ∑ π ∈ univ.filter q, S.val π
  exact (Finset.sum_subtype (univ.filter q) (fun x => by simp) S.val).symm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- The class counts of a sub-family (same classes, `cls ∘ val`). -/
theorem stage1Counts_restrictLow {C₀ : ℕ} {P : WTParams} {R N : ℕ} (S : Stage1DataMKG P R) (q : S.Pc → Prop)
    {Cl : Type} (hCl : Fintype Cl) (cls : S.Pc → Cl) (h : Fama.Stage1CountsG C₀ P R N S.toData Cl hCl cls) :
    Fama.Stage1CountsG C₀ P R N (restrictDataLow S q).toData Cl hCl (fun π => cls π.1) := by
  letI := S.fin
  letI : Fintype S.toData.Pc := S.fin
  obtain ⟨hr, hg, hc⟩ := h
  refine ⟨fun π => hr π.1, fun π => hg π.1, fun g r => le_trans ?_ (hc g r)⟩
  have hinj : ((@univ (restrictDataLow S q).Pc (restrictDataLow S q).fin).filter fun π =>
      ((restrictDataLow S q).toData.piece π).gbar = g ∧ ((restrictDataLow S q).toData.piece π).rbar = r).card ≤
      ((@univ S.Pc S.fin).filter fun π => (S.toData.piece π).gbar = g ∧ (S.toData.piece π).rbar = r).card := by
    refine Finset.card_le_card_of_injOn (fun π => π.1) (fun π hπ => ?_) (fun π₁ _ π₂ _ he => Subtype.ext he)
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 (Finset.mem_coe.1 hπ)).2⟩)
  exact_mod_cast hinj

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

theorem markedExtra_leLow {P : WTParams} {R : ℕ} {cP : ℝ} (hcP : 0 ≤ cP) (π : Stage1PieceMKG P R) {p : ℕ}
    (hπ : SoundMKG π p) {K : ℕ} (hK : π.nProt ≤ K) :
    markedExtraG cP π ≤ (K : ℝ) * (cP * P.d + 840 * P.d + 40) := by
  unfold markedExtraG
  have hm : (π.surv.m : ℝ) ≤ 6 * (π.nProt : ℝ) := by exact_mod_cast hπ.survivors_card
  have hn : (π.nProt : ℝ) ≤ K := by exact_mod_cast hK
  have hd : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ π.nProt := Nat.cast_nonneg _
  have hc : 0 ≤ cP * P.d + 840 * P.d + 40 := by positivity
  have h1 : (60 * (P.d : ℝ) + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) ≤
      (60 * (P.d : ℝ) + 2) * (14 * (π.nProt : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)
      ≤ cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (14 * (π.nProt : ℝ)) + 12 * (π.nProt : ℝ) := by linarith
    _ = (π.nProt : ℝ) * (cP * P.d + 840 * P.d + 40) := by ring
    _ ≤ (K : ℝ) * (cP * P.d + 840 * P.d + 40) := mul_le_mul_of_nonneg_right hn hc

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.ProtWhole

/-- **B4's Full gate gives the gate this area consumes.** -/
theorem stage1ReductionAtMKSel_of_fullLow {C₀ : ℕ} {cP cθ : ℝ} {P : WTParams}
    (h : Stage1ReductionAtMKFullG C₀ cP cθ P) : Stage1ReductionAtMKSelG C₀ cP cθ P := by
  intro p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs
    hhigh
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcnt⟩ :=
    h p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
  exact ⟨S, Cl, hCl, cls, members, sel, selR, hpart,
    fun π => ⟨(hpc π).1, (hpc π).2.1, (hpc π).2.2.1, (hpc π).2.2.2.1, (hpc π).2.2.2.2.1, (hpc π).2.2.2.2.2.1⟩,
    hsound, hord, hcnt⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.ProtWhole

theorem wtPrefix_sel_of_fullLow {C₀ : ℕ} {cP cθ : ℝ}
    (h : WTPrefix fun P => P.γ ≤ 1 / 2 → Stage1ReductionAtMKFullG C₀ cP cθ P) :
    WTPrefix fun P => P.γ ≤ 1 / 2 → Stage1ReductionAtMKSelG C₀ cP cθ P :=
  FinalMKPin.wtPrefix_mono h fun _ h hγ => stage1ReductionAtMKSel_of_fullLow (h hγ)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- **The non-regular part of `MarkedComponentBoundAtI` at fixed parameters**, from B4's gate and D7's class sum
at `P`, under the numerical conditions that the prefix provides. -/
theorem nonreg_atLow {C₀ : ℕ} {cP cθ B : ℝ} (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) {Pm : ℕ} {P : WTParams}
    (hd : 1 ≤ P.d) (hs : PieceSmall P) (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L)
    (hθδ : cθ ^ (40 * P.ν) * P.δ ^ P.ν ≤ 1)
    (hNL : ∀ p, p < P.D → ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 1 ≤ P.L)
    (hRP : ∀ p, p < P.D → 2 * Pm ≤ 10 * P.R (p + 1))
    (hbud : 25 * (cP * P.d + 840 * P.d + 40) + 800 * P.d + 2 ≤ 2 * B * P.d)
    (hB4 : Stage1ReductionAtMKSelG C₀ cP cθ P) (hD7 : ∀ X : ℝ, MarkedSumBoundSelAtTG cP cθ X P) :
    NonregComponentBoundAtILow B Pm P := by
  intro _hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs' J roots hJ pat kSel A hA hplain hTC h b hb hh Rf σ Rs dag hRf hRs
    hhigh
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hδ0 := hs.delta_pos
  have hRmax : R ≤ 10 * P.R (p + 1) := by have := hRP p hp; omega
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcnt⟩ :=
    hB4 p hp R hR1 hRmax n hn1 hn2 J hJ pat kSel t ht s hs' A
      (fun LG hLG => ⟨(hA LG hLG).1, (hA LG hLG).2.2.2.2.2, (hA LG hLG).2.1, (hA LG hLG).2.2.1,
        (hA LG hLG).2.2.2.1, (hA LG hLG).2.2.2.2.1⟩) hplain hTC roots h b Rf σ Rs dag hb hh hRf hRs hhigh
  letI := S.fin
  letI := hCl
  -- 1. the component sum is the sum of the piece values
  have hsum : ∑ LG ∈ A, compValue P LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) t roots =
      ∑ π, S.val π :=
    sum_compValue_eq_sum_pieces P roots A members cls sel hpart t (fun LG => fixCap LG J pat t s)
      (fun LG => offCap LG J dag.isSome)
      (fun LG k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) S.val
      (fun π => (hpc π).1)
      (fun LG hLG => summable_kgTerm_capWt_gen P hL0 LG (hA LG hLG).1.1.1 (layer_le_of_mkCarries (hA LG hLG).1) J
        (hA LG hLG).2.2.1 roots _ _ _ kSel Rf σ Rs h dag b hb hh)
  rw [hsum]
  -- 2. grouping by residual selected trees
  set T : Finset (Fin (2 * R)) := univ.filter fun j => (kSel j).isSome with hT
  have hUT : ∀ π, ((selR π).image fun v => v.1.1) ⊆ T := by
    intro π j hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_filter.2 ⟨mem_univ _, ((hpc π).2.2.2.1 v hv).1⟩
  rw [sum_eq_sum_powerset S.val (fun π => (selR π).image fun v => v.1.1) T (fun π _ => hUT π)]
  -- the common bound of a group
  set Qp0 : ℝ := ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1) with hQp0
  have hRs0 : ∀ j, 0 < Rs j := fun j => lt_of_lt_of_le hL0 (hRs j)
  have hQp0nn : 0 ≤ Qp0 := Finset.prod_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (inv_nonneg.2 (hRs0 j).le) (Real.rpow_nonneg (hRs0 j).le _)
    · exact zero_le_one
  set X : ℝ := ((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40) with hX
  set Gb : ℝ := b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ))) * P.δ ^ (7 * P.ν * n) with hGb
  have hb0 : 0 ≤ b ^ n := pow_nonneg (by linarith) _
  have hGb0 : 0 ≤ Gb := by rw [hGb]; positivity
  have hgroup : ∀ V ∈ T.powerset,
      ‖∑ π ∈ univ.filter (fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V), S.val π‖ ≤ Gb := by
    intro V hV
    have hVT : V ⊆ T := Finset.mem_powerset.1 hV
    set q : S.Pc → Prop := fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V with hq
    have hres := sum_restrictDataLow S q
    by_cases hne : ∃ π, q π
    swap
    · push_neg at hne
      have : univ.filter q = ∅ := Finset.filter_eq_empty_iff.2 fun π _ => hne π
      change ‖∑ π ∈ univ.filter q, S.val π‖ ≤ Gb
      rw [this, Finset.sum_empty, norm_zero]
      exact hGb0
    obtain ⟨π₀, hπ₀⟩ := hne
    -- `R ≤ 2n` and `n ≤ (log L)^K`: the absorption conditions
    have hR2n : R ≤ 2 * n := by
      have h1 := (hsound π₀).bond_count
      have h2 := hord π₀
      omega
    have hnlog : (n : ℝ) ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
      have h1 : (n : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hn2
      exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
    obtain ⟨hT2, hS2, hLabs⟩ := habs.2 n R hR1 hR2n hnlog
    have hnL : (n : ℝ) + 1 ≤ P.L := by
      have h1 : (n : ℝ) ≤ ((P.N (p + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hn2
      linarith [hNL p hp]
    -- the uniform extra
    have hXπ : ∀ π, markedExtraG cP (S.piece π) ≤ X := by
      intro π
      obtain ⟨LG, hLG, hle⟩ := (hpc π).2.2.1
      have hLGA : LG ∈ A := (hpart.1 LG).2 ⟨cls π, hLG⟩
      have hc := card_protI_le LG J hJ (hA LG hLGA).2.2.1 pat t s kSel
      exact markedExtra_leLow hcP (S.piece π) (hsound π).toSoundMKG (le_trans hle hc)
    have hspos : 0 < selMass n b Rs kSel V := by
      unfold selMass
      refine mul_pos (pow_pos (by linarith) _) (Finset.prod_pos fun j _ => ?_)
      split_ifs <;> first
        | exact one_pos
        | exact mul_pos (inv_pos.2 (hRs0 j)) one_pos
        | exact mul_pos (inv_pos.2 (hRs0 j)) (Real.rpow_pos_of_pos (hRs0 j) _)
    have hD := hD7 X (p := p) (R := R) (n := n) hp hR1 hRmax (restrictDataLow S q) (fun π => selR π.1) V Rs
      (fun _ => t) 0 roots C₀ Cl hCl (fun π => cls π.1) (selMass n b Rs kSel V) hspos
      (fun j _ => hRs j) (fun π => π.2.2) (fun π v hv => ((hpc π.1).2.2.2.1 v hv).2)
      (fun π => (hpc π.1).2.2.2.2.1) (fun π => (hpc π.1).2.2.2.2.2) (fun π => hsound π.1) (fun π => hord π.1) hnL
      (fun π => by
        have h := (hpc π.1).2.1
        rw [π.2.2] at h
        exact h)
      (fun π => hXπ π.1) (stage1Counts_restrictLow S q hCl cls hcnt) hT2 hS2
    rw [hres] at hD
    have hfeq : (univ.filter fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V) =
        @Finset.filter _ q (Classical.decPred q) univ :=
      Finset.ext fun π => by simp only [Finset.mem_filter]; rfl
    rw [hfeq]
    refine hD.trans ?_
    -- the group bound is the common bound
    have hVsel : ∀ j ∈ V, (kSel j).isSome := fun j hj => (Finset.mem_filter.1 (hVT hj)).2
    have hmass := selMass_mul_prod n b Rs kSel V hVsel
    have hbr := bracket_le hs (cθ := cθ) (by linarith) hR1 habs.1 hθδ hLabs
    have hCV : P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ)) ≤ P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have : (V.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hVT
      have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      nlinarith
    set Br : ℝ := 4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * ((6 * C₀ : ℕ) : ℝ) ^ n *
        ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) with hBr
    have hBr0 : 0 ≤ Br := by
      have hC₂ : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
      have hC₁ : 0 ≤ P.C₁ := by linarith [hs.c1_ge]
      rw [hBr]; positivity
    have hLX : 0 ≤ P.L ^ X := Real.rpow_nonneg hL0.le _
    calc selMass n b Rs kSel V * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ)) *
          (∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ))) * Br
        = (selMass n b Rs kSel V * ∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ))) *
            (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ))) * Br := by ring
      _ = b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ))) * Br := by rw [hmass]
      _ ≤ b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ))) * P.δ ^ (7 * P.ν * n) := by
          apply mul_le_mul _ hbr hBr0 (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCV hLX) (mul_nonneg hb0 hQp0nn)
  -- 3. sum over the groups and the budget
  have hTc : T.card ≤ 2 * R := by
    calc T.card ≤ (univ : Finset (Fin (2 * R))).card := Finset.card_le_univ _
      _ = 2 * R := by simp
  have hsumV := norm_sum_le_of_le T.powerset hgroup
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul] at hsumV
  refine hsumV.trans ?_
  have hbudL := budget_le hs.L_ge (cP := cP) (B := B) (R := R) hTc hcP hbud
  have hδ7 : 0 ≤ P.δ ^ (7 * P.ν * n) := Real.rpow_nonneg hδ0.le _
  calc ((2 ^ T.card : ℕ) : ℝ) * Gb
      = ((2 : ℝ) ^ T.card * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)))) *
          (P.δ ^ (7 * P.ν * n) * b ^ n * Qp0) := by rw [hGb]; push_cast; ring
    _ ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp0) :=
        mul_le_mul_of_nonneg_right hbudL (by positivity)
    _ = _ := by rw [hQp0]; ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory Filter
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- **The non-regular part under the flower prefix.** -/
theorem nonregPrefixLow {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix fun P => P.γ ≤ 1 / 2 → Stage1ReductionAtMKSelG C₀ cP cθ P) (hD7 : SelSumTargetTG)
    (hFine : FineSplicedGateLowMK) :
    WTPrefixP (NonregComponentBoundAtILow 17999) := by
  have hm3 := ladderFourierAtMKFace_largeConstantMonotone
  have hm2 := fineSplicedLowMK_largeConstantMonotone
  have hm1 := coarseSplicedAtMK_largeConstantMonotone
  have hm0 : LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → Stage1ReductionAtMKSelG C₀ cP cθ P) :=
    fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
      stage1ReductionAtMKSel_largeConstantMonotoneLow C₀ cP cθ P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)
  have hQ0 := prefix_and hB4 (prefix_and FinalMKCrude.coarseSplicedGateMK
    (prefix_and hFine FinalMKPin.ladderFourierMKFace_prefix hm2 hm3) hm1 (hm2.and hm3))
    hm0 (hm1.and (hm2.and hm3))
  have hQ := prefix_with_stage1_small hQ0 (hm0.and (hm1.and (hm2.and hm3))) (6 * C₀) (by omega)
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨0, fun Pm _ => ?_⟩
  refine ⟨min δ₀ (cθ ^ 40)⁻¹, lt_min hδ₀ (by positivity), fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨Lk, hLk2, hLk⟩ := exists_log_pow_add_one_le (4 * (40 * d) ^ (2 * D + 2))
  refine ⟨C₂, hC₂, max L₀ (max Lk (Real.exp ((Pm : ℝ) + 1))), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLk' : Lk ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLe : Real.exp ((Pm : ℝ) + 1) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨⟨hS1, hcoarse, hfine, hface⟩, hs, -, hd3, habs⟩ := H L hLL₀
  intro hγh
  have hd1 : 1 ≤ d := by omega
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hLe
  have hlogPm : (Pm : ℝ) + 1 ≤ Real.log L := by
    rw [← Real.log_exp ((Pm : ℝ) + 1)]; exact Real.log_le_log (Real.exp_pos _) hLe
  have hlog : 1 ≤ Real.log L := by have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _; linarith
  refine nonreg_atLow (B := 17999) (Pm := Pm) hcP hcθ hd1 hs habs hlog
    (ctheta_delta_le hcθ hδ.1 (hδ.2.trans (min_le_right _ _)) hν.1.le) ?_ ?_ (budget_17999 hcP' hd1) (hS1 hγh)
    (fun X => hD7 cP cθ hcP hcθ _ hd1 hs hcoarse (hfine hγh) hface X) hγh
  · intro p _
    have h1 := N_quartic_le_log_pow ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ hd1 hlog (p + 1)
    have h2 := hLk L hLk'
    push_cast
    linarith
  · intro p _
    have := le_R_of_log ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ hd1 hlogPm (p + 1)
    omega

end

/-- **Item F** (conditional helper): the non-regular part for `0 < γ ≤ 1/2` from the marked Stage-1′ gate over
`𝒱_γ` (item I, at main's `cP = 452` and any `cθ ≥ 1`), the selected class sum (item G) and the marked fine gate
(item H), as main's `CompMK.markedComponentBoundAtI_18000` (non-regular half, `B = 17999`). -/
theorem nonregLowTarget_of {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hB4 : Stage1MKGateLow C₀ 452 cθ) (hD7 : SelSumTargetTG) (hFine : FineSplicedGateLowMK) :
    NonregLowTarget :=
  nonregPrefixLow hC₀ (by norm_num) (by norm_num) hcθ (wtPrefix_sel_of_fullLow hB4) hD7 hFine

end WaveTurbulence.GammaLow.Flower
