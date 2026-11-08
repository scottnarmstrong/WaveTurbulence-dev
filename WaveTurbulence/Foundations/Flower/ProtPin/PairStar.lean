/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCut

/-! # D3 PROT-PIN: D3's multiplier at a one-pair chain (`PairOnly`), with star weights and filters

The (P2)/(P1)-with-`rest = nil` analogue of `TermStarCut`: D2c's `PairOnly.multFactors_D3` writes D3's multiplier of
`pair m Qr Qg inner nil` as a cut factor (the branch factors of the root `𝔫_a` and of `𝔫_b`, and the dagger) times the
interior and the two side couples; the pull-back (`pull_mult`) makes each piece factor D3's multiplier of the piece
(`star_pair_mult`), the cut factor is bounded by the star costs of `𝔫_a`, `𝔫_b` (`star_pair_Mc_le`), and the star cost
of `S` splits (`star_pair_cost`). Groundwork for the root-pinned configurations (finding F-D3-4). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut TTree WaveTurbulence.Links WaveTurbulence.Reg

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)

theorem pairEmbI : PieceEmb D.hp.ιi D.hp.βi := ⟨D.hp.βi_toNode, D.hp.βi_child⟩
theorem pairEmbR : PieceEmb D.hp.ιr D.hp.βr := ⟨D.hp.βr_toNode, D.hp.βr_child⟩
theorem pairEmbG : PieceEmb D.hp.ιg D.hp.βg := ⟨D.hp.βg_toNode, D.hp.βg_child⟩

/-- **D3's multiplier at a one-pair chain, with gate-form pieces.** -/
theorem star_pair_mult {d : ℕ} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind) :
    D.MultFactors
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB A *
        fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB B * ((indB ind B : ℝ) : ℂ))
      (pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu) (pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu)
      (pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu) := by
  have h := D.multFactors_D3 S ω F (fun _ => false) M Fu Mu ind hind
  have eI : (fun K => ∏ x, fD3' S ω F (fun _ => false) M Fu Mu (D.hp.βi x) (bstar K x)) =
      pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu := funext fun K => pull_mult (pairEmbI D) S ω F M Fu Mu K
  have eR : (fun K => ∏ y, fD3' S ω F (fun _ => false) M Fu Mu (D.hp.βr y) (bstar K y)) =
      pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu := funext fun K => pull_mult (pairEmbR D) S ω F M Fu Mu K
  have eG : (fun K => ∏ y, fD3' S ω F (fun _ => false) M Fu Mu (D.hp.βg y) (bstar K y)) =
      pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu := funext fun K => pull_mult (pairEmbG D) S ω F M Fu Mu K
  rw [eI, eR, eG] at h
  exact h

/-- The cut factor at a one-pair chain is bounded by the star costs of the two linked nodes. -/
theorem star_pair_Mc_le {d : ℕ} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ) {J : ℕ}
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : ∀ κ, 0 ≤ ind κ ∧ ind κ ≤ 1) (A B : Fin 4 → Mom d) :
    ‖fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB A * fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB B *
        ((indB ind B : ℝ) : ℂ)‖ ≤ costB S cω D.hp.rootB * costB S cω D.hp.bB := by
  rw [norm_mul, norm_mul]
  have h3 : ‖((indB ind B : ℝ) : ℂ)‖ ≤ 1 := by
    unfold indB
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind _).1]
    exact (hind _).2
  calc ‖fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB A‖ * ‖fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB B‖ *
        ‖((indB ind B : ℝ) : ℂ)‖
      ≤ costB S cω D.hp.rootB * costB S cω D.hp.bB * 1 :=
        mul_le_mul (mul_le_mul (norm_fD3'_le S ω cω hpres F M Fu Mu _ _)
          (norm_fD3'_le S ω cω hpres F M Fu Mu _ _) (norm_nonneg _) (costB_nonneg _ _ _)) h3 (norm_nonneg _)
          (mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _))
    _ = _ := mul_one _

/-- **The star cost splits at a one-pair chain.** -/
theorem star_pair_cost (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    ∏ a ∈ S, max (cω a) 0 = costB S cω D.hp.rootB * costB S cω D.hp.bB *
      ((∏ a ∈ pullS D.hp.ιi S, max (cω (D.hp.ιi a)) 0) *
        ((∏ a ∈ pullS D.hp.ιr S, max (cω (D.hp.ιr a)) 0) * ∏ a ∈ pullS D.hp.ιg S, max (cω (D.hp.ιg a)) 0)) := by
  have hX : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  rw [prod_cost_branch S (hroot_tree hX D.dec S) cω, D.hp.prod_pairBranch, pull_cost (pairEmbI D),
    pull_cost (pairEmbR D), pull_cost (pairEmbG D)]

end WaveTurbulence.Flower.ProtPin
