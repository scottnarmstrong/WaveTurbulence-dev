/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStar

/-! # D3 PROT-PIN: the multiplier of a cap couple at the cut of its paired tree, with stars and filters

D2c's `CapData.multFactors_D3_cap'` writes `capM` of D3's cap multiplier, at a terminal cut of the paired tree, with
the cap's star in the cut factor and the pieces' factors read at `βc ∘ β·`. The pieces are embedded in the cap couple
through the paired tree (`PieceEmb.comp`, `capEmb`), so the pull-back gives gate-form pieces (`starMult_cap`); the
star cost of `S` splits as `cap · 𝔫_a · 𝔫_b · pieces`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut TTree WaveTurbulence.Links WaveTurbulence.Reg

theorem PieceEmb.comp {w w' w'' : ℕ} {G : Garden w} {G' : Garden w'} {G'' : Garden w''}
    {ι₁ : GNode G''.tree → GNode G'.tree} {β₁ : GBranch G''.tree → GBranch G'.tree}
    {ι₂ : GNode G'.tree → GNode G.tree} {β₂ : GBranch G'.tree → GBranch G.tree}
    (E₁ : PieceEmb ι₁ β₁) (E₂ : PieceEmb ι₂ β₂) : PieceEmb (fun z => ι₂ (ι₁ z)) (fun x => β₂ (β₁ x)) :=
  ⟨fun x => by rw [E₂.node, E₁.node], fun x i => by rw [E₂.child, E₁.child]⟩

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1}

/-- The nodes of the paired tree of a cap couple, in the cap couple (tree `0`). -/
def capι (Dc : CapData X LG LG1) (z : GNode LG1.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 2), z.1.2), by
    have h := z.2
    rw [Dc.fin1 z.1.1, Dc.tree_eq] at h
    exact h⟩

theorem capEmb (Dc : CapData X LG LG1) : PieceEmb (capι Dc) Dc.βc :=
  ⟨fun _ => Subtype.ext rfl, fun _ _ => Subtype.ext rfl⟩

/-- **D3's cap multiplier, on the paired tree, satisfies `StarMult`** with the star cost of `S`. -/
theorem starMult_cap {d : ℕ} {L : ℝ} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {X : RegChain}
    (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    StarMult L LG1 X (Dc.capM fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
      filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (starCost S cω) := by
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
  have h := CapData.multFactors_D3_cap' Dc C S ω F (fun _ => false) M Fu Mu ind hind
  have eP := funext fun K => pull_mult EP (S.erase Dc.cap) ω F M Fu Mu K
  have eI := funext fun K => pull_mult EI (S.erase Dc.cap) ω F M Fu Mu K
  have eR := funext fun K => pull_mult ER (S.erase Dc.cap) ω F M Fu Mu K
  have eG := funext fun K => pull_mult EG (S.erase Dc.cap) ω F M Fu Mu K
  rw [eP, eI, eR, eG] at h
  refine ⟨_, costB (S.erase Dc.cap) cω (Dc.βc C.aBr) * costB (S.erase Dc.cap) cω (Dc.βc C.bBr) * capc,
    pullS (fun z => capι Dc (C.ιP z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιP z)), fun z => cω (capι Dc (C.ιP z)),
      pullF (fun x => Dc.βc (C.βP x)) F, fun y => M (Dc.βc (C.βP y)),
      pullF (fun x => Dc.βc (C.βP x)) Fu, fun y => Mu (Dc.βc (C.βP y)),
    pullS (fun z => capι Dc (C.ιI z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιI z)), fun z => cω (capι Dc (C.ιI z)),
      pullF (fun x => Dc.βc (C.βI x)) F, fun y => M (Dc.βc (C.βI y)),
      pullF (fun x => Dc.βc (C.βI x)) Fu, fun y => Mu (Dc.βc (C.βI y)),
    pullS (fun z => capι Dc (C.ιR z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιR z)), fun z => cω (capι Dc (C.ιR z)),
      pullF (fun x => Dc.βc (C.βR x)) F, fun y => M (Dc.βc (C.βR y)),
      pullF (fun x => Dc.βc (C.βR x)) Fu, fun y => Mu (Dc.βc (C.βR y)),
    pullS (fun z => capι Dc (C.ιG z)) (S.erase Dc.cap), fun z => ω (capι Dc (C.ιG z)), fun z => cω (capι Dc (C.ιG z)),
      pullF (fun x => Dc.βc (C.βG x)) F, fun y => M (Dc.βc (C.βG y)),
      pullF (fun x => Dc.βc (C.βG x)) Fu, fun y => Mu (Dc.βc (C.βG y)),
    h,
    ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩,
    ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩, ⟨pull_pres _ hpres', pull_scale _ hM, pull_scale _ hMu⟩,
    mul_nonneg (mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)) hcapc0, fun A B => ?_, le_of_eq ?_⟩
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
    have ha := norm_fD3'_le (S.erase Dc.cap) ω cω hpres' F M Fu Mu (Dc.βc C.aBr) A
    have hb := norm_fD3'_le (S.erase Dc.cap) ω cω hpres' F M Fu Mu (Dc.βc C.bBr) B
    calc _ ≤ costB (S.erase Dc.cap) cω (Dc.βc C.aBr) * costB (S.erase Dc.cap) cω (Dc.βc C.bBr) * (capc * 1) :=
          mul_le_mul (mul_le_mul ha hb (norm_nonneg _) (costB_nonneg _ _ _))
            (mul_le_mul hc hi (norm_nonneg _) hcapc0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _))
      _ = _ := by rw [mul_one]
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

end WaveTurbulence.Flower.ProtPin
