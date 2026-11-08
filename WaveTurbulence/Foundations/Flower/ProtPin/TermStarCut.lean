/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.StarPull

/-! # D3 PROT-PIN: D3's multiplier at the terminal cut, with star weights and filters

At the terminal cut (D2c's `CutTermData`), D3's multiplier `starWeight S ω · filtWeight F 0 M · filtWeight Fu 0 Mu ·
ind` factors (`multFactors_D3'`) into the cut factor `Mc` (the branch factors of the partners `𝔫_a`, `𝔫_b` and the
dagger) and the four pieces; by the pull-back (`pull_mult`) each piece factor is D3's multiplier of the piece with the
pulled-back data (`star_cut_mult`). The cut factor is bounded by the star costs of `𝔫_a`, `𝔫_b`
(`star_cut_Mc_le`), and the star cost of the object splits accordingly (`star_cut_cost`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut TTree WaveTurbulence.Links WaveTurbulence.Reg

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)

/-! ### The four pieces are embedded -/

theorem embP : PieceEmb D.ιP D.βP := ⟨fun _ => Subtype.ext rfl, fun _ _ => Subtype.ext rfl⟩

theorem embI : PieceEmb D.ιI D.βI :=
  ⟨fun _ => Subtype.ext rfl, fun x i => Subtype.ext (Prod.ext rfl (by
    simp [CutTermData.βI, CutTermData.ιI, GBranch.child, GBranch.toNode]))⟩

theorem embR : PieceEmb D.ιR D.βR :=
  ⟨fun _ => Subtype.ext rfl, fun x i => Subtype.ext (Prod.ext rfl (by
    simp [CutTermData.βR, CutTermData.ιR, GBranch.child, GBranch.toNode]))⟩

theorem embG : PieceEmb D.ιG D.βG :=
  ⟨fun _ => Subtype.ext rfl, fun x i => Subtype.ext (Prod.ext rfl (by
    simp [CutTermData.βG, CutTermData.ιG, GBranch.child, GBranch.toNode]))⟩

/-! ### The factorization with gate-form pieces -/

/-- D3's multiplier of a piece, pulled back along `(ι, β)`. -/
def pullMult {w w' d : ℕ} {G : Garden w} {G' : Garden w'} (ι : GNode G'.tree → GNode G.tree)
    (β : GBranch G'.tree → GBranch G.tree) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (K : GNode G'.tree → Mom d) : ℂ :=
  Flower.IncTop.starWeight (pullS ι S) (fun z => ω (ι z)) K *
    filtWeight (pullF β F) (fun _ => false) (fun y => M (β y)) K *
    filtWeight (pullF β Fu) (fun _ => false) (fun y => Mu (β y)) K

/-- **D3's multiplier at the terminal cut, with gate-form pieces.** -/
theorem star_cut_mult {d : ℕ} (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    D.MultFactors
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F (fun _ => false) M Fu Mu D.aBr A * fD3' S ω F (fun _ => false) M Fu Mu D.bBr B *
        ((indB ind B : ℝ) : ℂ))
      (pullMult D.ιP D.βP S ω F M Fu Mu) (pullMult D.ιI D.βI S ω F M Fu Mu)
      (pullMult D.ιR D.βR S ω F M Fu Mu) (pullMult D.ιG D.βG S ω F M Fu Mu) := by
  have h := D.multFactors_D3' S ω F (fun _ => false) M Fu Mu ind hind
  have eP : (fun K => ∏ x, fD3' S ω F (fun _ => false) M Fu Mu (D.βP x) (bstar K x)) =
      pullMult D.ιP D.βP S ω F M Fu Mu := funext fun K => pull_mult (embP D) S ω F M Fu Mu K
  have eI : (fun K => ∏ x, fD3' S ω F (fun _ => false) M Fu Mu (D.βI x) (bstar K x)) =
      pullMult D.ιI D.βI S ω F M Fu Mu := funext fun K => pull_mult (embI D) S ω F M Fu Mu K
  have eR : (fun K => ∏ y, fD3' S ω F (fun _ => false) M Fu Mu (D.βR y) (bstar K y)) =
      pullMult D.ιR D.βR S ω F M Fu Mu := funext fun K => pull_mult (embR D) S ω F M Fu Mu K
  have eG : (fun K => ∏ y, fD3' S ω F (fun _ => false) M Fu Mu (D.βG y) (bstar K y)) =
      pullMult D.ιG D.βG S ω F M Fu Mu := funext fun K => pull_mult (embG D) S ω F M Fu Mu K
  rw [eP, eI, eR, eG] at h
  exact h

/-- The cut factor is bounded by the star costs of the two partners. -/
theorem star_cut_Mc_le {d : ℕ} (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ) {J : ℕ}
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : ∀ κ, 0 ≤ ind κ ∧ ind κ ≤ 1) (A B : Fin 4 → Mom d) :
    ‖fD3' S ω F (fun _ => false) M Fu Mu D.aBr A * fD3' S ω F (fun _ => false) M Fu Mu D.bBr B *
        ((indB ind B : ℝ) : ℂ)‖ ≤ costB S cω D.aBr * costB S cω D.bBr := by
  rw [norm_mul, norm_mul]
  have h3 : ‖((indB ind B : ℝ) : ℂ)‖ ≤ 1 := by
    unfold indB
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind _).1]
    exact (hind _).2
  calc ‖fD3' S ω F (fun _ => false) M Fu Mu D.aBr A‖ * ‖fD3' S ω F (fun _ => false) M Fu Mu D.bBr B‖ *
        ‖((indB ind B : ℝ) : ℂ)‖
      ≤ costB S cω D.aBr * costB S cω D.bBr * 1 :=
        mul_le_mul (mul_le_mul (norm_fD3'_le S ω cω hpres F M Fu Mu _ _)
          (norm_fD3'_le S ω cω hpres F M Fu Mu _ _) (norm_nonneg _) (costB_nonneg _ _ _)) h3 (norm_nonneg _)
          (mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _))
    _ = _ := mul_one _

/-- **The star cost splits at the cut.** -/
theorem star_cut_cost (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    ∏ a ∈ S, max (cω a) 0 = costB S cω D.aBr * costB S cω D.bBr *
      ((∏ a ∈ pullS D.ιP S, max (cω (D.ιP a)) 0) * ((∏ a ∈ pullS D.ιI S, max (cω (D.ιI a)) 0) *
        ((∏ a ∈ pullS D.ιR S, max (cω (D.ιR a)) 0) * ∏ a ∈ pullS D.ιG S, max (cω (D.ιG a)) 0))) := by
  obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
  rw [prod_cost_branch S (hroot_tree (appendChain_ne_nil Xp m Qr Qg inner) D.dec S) cω,
    D.prod_branch_cut hZ hs, pull_cost (embP D), pull_cost (embI D), pull_cost (embR D), pull_cost (embG D)]

/-- The pulled-back data inherit the presentations and the scales. -/
theorem pull_pres {w w' d J : ℕ} {G : Garden w} {G' : Garden w'} (ι : GNode G'.tree → GNode G.tree)
    {S : Finset (GNode G.tree)} {ω : GNode G.tree → Flower.IncTop.Star d → ℂ} {cω : GNode G.tree → ℝ}
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a)) :
    ∀ a ∈ pullS ι S, Flower.IncTop.StarPresented J (ω (ι a)) (cω (ι a)) :=
  fun a ha => hpres _ (Finset.mem_filter.mp ha).2.1

theorem pull_scale {w w' : ℕ} {G : Garden w} {G' : Garden w'} (β : GBranch G'.tree → GBranch G.tree)
    {F : Finset (GBranch G.tree)} {M : GBranch G.tree → ℝ} {L : ℝ} (hM : ∀ b ∈ F, L ≤ M b) :
    ∀ x ∈ pullF β F, L ≤ M (β x) :=
  fun x hx => hM _ ((mem_pullF β F x).mp hx)

end WaveTurbulence.Flower.ProtPin
