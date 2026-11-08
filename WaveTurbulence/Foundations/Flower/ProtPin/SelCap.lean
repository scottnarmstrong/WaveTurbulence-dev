/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCap
public import WaveTurbulence.Foundations.Flower.ProtPin.SelStar

/-! # D3 PROT-PIN (R181): the flagged cap multiplier on the paired tree

`starMult_capA`: `starMult_cap` (TermStarCap.lean) with a first-layer flag `ann`; the cut factor gains `chiDSup²`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin.Sel

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut TTree WaveTurbulence.Links WaveTurbulence.Reg

/-- **D3's flagged cap multiplier, on the paired tree, satisfies `StarMultA`** with `starCost S cω · chiDSup²`. -/
theorem starMult_capA {d : ℕ} {L : ℝ} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {X : RegChain}
    (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    StarMultA L LG1 X (Dc.capM fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ *
      filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (starCost S cω * FiltCoh.chiDSup ^ 2) := by
  intro Xp m Qr Qg inner LGp LGi LGr LGg C hX
  subst hX
  have hpres' : ∀ a ∈ (S.erase Dc.cap), Flower.IncTop.StarPresented (30 * d) (ω a) (cω a) :=
    fun a ha => hpres a (Finset.mem_of_mem_erase ha)
  set capc : ℝ := if Dc.cap ∈ S then max (cω Dc.cap) 0 else 1 with hcapc
  have hcapc0 : 0 ≤ capc := by rw [hcapc]; split_ifs <;> simp
  have EP := (embP C).comp (capEmb Dc)
  have EI := (embI C).comp (capEmb Dc)
  have ER := (embR C).comp (capEmb Dc)
  have EG := (embG C).comp (capEmb Dc)
  have h := CapData.multFactors_D3_cap' Dc C S ω F ann M Fu Mu ind hind
  have eP := funext fun K => pull_multA EP (S.erase Dc.cap) ω F ann M Fu Mu K
  have eI := funext fun K => pull_multA EI (S.erase Dc.cap) ω F ann M Fu Mu K
  have eR := funext fun K => pull_multA ER (S.erase Dc.cap) ω F ann M Fu Mu K
  have eG := funext fun K => pull_multA EG (S.erase Dc.cap) ω F ann M Fu Mu K
  rw [eP, eI, eR, eG] at h
  refine ⟨_, costB (S.erase Dc.cap) cω (Dc.βc C.aBr) * costB (S.erase Dc.cap) cω (Dc.βc C.bBr) * capc *
      FiltCoh.chiDSup ^ 2,
    pullS (fun z => capι Dc (C.ιP z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιP z)), fun z => cω (capι Dc (C.ιP z)),
      pullF (fun x => Dc.βc (C.βP x)) F, fun y => ann (Dc.βc (C.βP y)), fun y => M (Dc.βc (C.βP y)),
      pullF (fun x => Dc.βc (C.βP x)) Fu, fun y => Mu (Dc.βc (C.βP y)),
    pullS (fun z => capι Dc (C.ιI z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιI z)), fun z => cω (capι Dc (C.ιI z)),
      pullF (fun x => Dc.βc (C.βI x)) F, fun y => ann (Dc.βc (C.βI y)), fun y => M (Dc.βc (C.βI y)),
      pullF (fun x => Dc.βc (C.βI x)) Fu, fun y => Mu (Dc.βc (C.βI y)),
    pullS (fun z => capι Dc (C.ιR z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιR z)), fun z => cω (capι Dc (C.ιR z)),
      pullF (fun x => Dc.βc (C.βR x)) F, fun y => ann (Dc.βc (C.βR y)), fun y => M (Dc.βc (C.βR y)),
      pullF (fun x => Dc.βc (C.βR x)) Fu, fun y => Mu (Dc.βc (C.βR y)),
    pullS (fun z => capι Dc (C.ιG z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιG z)), fun z => cω (capι Dc (C.ιG z)),
      pullF (fun x => Dc.βc (C.βG x)) F, fun y => ann (Dc.βc (C.βG y)), fun y => M (Dc.βc (C.βG y)),
      pullF (fun x => Dc.βc (C.βG x)) Fu, fun y => Mu (Dc.βc (C.βG y)),
    h,
    ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩,
    ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩,
    mul_nonneg (mul_nonneg (mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)) hcapc0) (by positivity),
    fun A B => ?_, le_of_eq ?_⟩
  · -- the cut factor
    have hc : ‖(if Dc.cap ∈ S then ω Dc.cap (WithLp.toLp 2 fun _ => B (m.lone).succ) else 1)‖ ≤ capc := by
      rw [hcapc]
      split_ifs with hcap
      · exact FiltCoh.norm_star_le (hpres _ hcap) _
      · simp
    have hi : ‖((indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (Dc.ρ a)) B : ℝ) : ℂ)‖ ≤ 1 := by
      unfold indB
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind.1 _).1]
      exact (hind.1 _).2
    rw [norm_mul, norm_mul, norm_mul]
    have ha := norm_fD3'_leA (S.erase Dc.cap) ω cω hpres' F ann M Fu Mu (Dc.βc C.aBr) A
    have hb := norm_fD3'_leA (S.erase Dc.cap) ω cω hpres' F ann M Fu Mu (Dc.βc C.bBr) B
    have h1 := FiltCoh.one_le_chiDSup
    have hca := costB_nonneg (S.erase Dc.cap) cω (Dc.βc C.aBr)
    have hcb := costB_nonneg (S.erase Dc.cap) cω (Dc.βc C.bBr)
    calc _ ≤ (costB (S.erase Dc.cap) cω (Dc.βc C.aBr) * FiltCoh.chiDSup) *
          (costB (S.erase Dc.cap) cω (Dc.βc C.bBr) * FiltCoh.chiDSup) * (capc * 1) :=
          mul_le_mul (mul_le_mul ha hb (norm_nonneg _) (by positivity))
            (mul_le_mul hc hi (norm_nonneg _) hcapc0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (by positivity)
      _ = _ := by ring
  · -- the star cost
    obtain ⟨GZ, hs, hZ⟩ := C.exists_GZ
    have hXne := appendChain_ne_nil Xp m Qr Qg inner
    have hsplit : starCost S cω = capc * ∏ a ∈ (S.erase Dc.cap), max (cω a) 0 := by
      unfold starCost
      rw [hcapc]
      split_ifs with hcap
      · exact (Finset.mul_prod_erase S _ hcap).symm
      · rw [Finset.erase_eq_of_notMem hcap, one_mul]
    rw [hsplit, prod_cost_branch (S.erase Dc.cap) (Dc.hroot_erase hXne S) cω,
      ← Dc.βc.prod_comp (fun b => costB (S.erase Dc.cap) cω b), C.prod_branch_cut hZ hs (fun b => costB (S.erase Dc.cap) cω (Dc.βc b)),
      pull_cost EP, pull_cost EI, pull_cost ER, pull_cost EG]
    unfold starCost
    ring

end WaveTurbulence.Flower.ProtPin.Sel
