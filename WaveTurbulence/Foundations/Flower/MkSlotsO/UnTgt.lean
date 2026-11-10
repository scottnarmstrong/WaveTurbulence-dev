/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnGeo
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildConj
public import WaveTurbulence.Foundations.Flower.IncTop.TopWeight
public import WaveTurbulence.Foundations.Flower.MkSlots.CapTriv

/-! # B3s-HELPER8 / UNPIN (part 3): the slot targets from the D5 gates

Moment-carrying superpositions of the regular couple and tree kernels with INC-TOP star weights and two filter layers,
at the moment weights `θ = η` (no loss) and `θ = 1/4` (loss `L^{4d}` for incoherent objects, none for coherent
ones), from D5's `FiltIncoherentDecayAt` / `FiltCoherentBoundAt` (couples in both orientations through D3's
`ProtPin.tc_coh_any`), main's moment-carrying Fourier superpositions (`cenCplCM_spec`, `supTreeCM_spec`) and the
trivial producers (`couple_slot_trivM`, `tree_slot_nilM`, all `θ`):

* `d5_mass_le`, `d5_mass_coh_le`: the D5 mass against the B3 slot mass `(C√δ)^{2n} L^{-η⁸ g}`;
* **`unCpl_main`**, **`unTree_main`** (non-trivial objects); **`unCpl_triv`**, **`unTree_nil`** (trivial ones). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1WVine

namespace WaveTurbulence.Flower.MkSlotsO

/-- The D5 multiplier: star weights times two filter layers (no annular factor). -/
def d5M {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ)
    (κ : GNode G.tree → Mom d) : ℂ :=
  IncTop.starWeight S ω κ * ProtDefs.filtWeight F (fun _ => false) M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ

/-! ## Mass bookkeeping -/

/-- **The incoherent D5 mass against the slot mass.** -/
theorem d5_mass_le (P : WTParams) (C : ℝ) {ι : Type*} (S : Finset ι) (cω : ι → ℝ) (hcω : ∀ a ∈ S, 0 ≤ cω a)
    (c : ℝ) (n g : ℕ) (hn : 1 ≤ n) (hc1 : 1 ≤ P.C₁) (hCC : P.C₁ ≤ C) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (lf : ℝ) (hlf : 0 ≤ lf) :
    (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal lf ≤
      ENNReal.ofReal ((∏ a ∈ S, cω a) * P.L ^ c *
        ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ))) * lf) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  have hP0 : 0 ≤ ∏ a ∈ S, cω a := Finset.prod_nonneg hcω
  have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0.le _
  have hC0 : 0 ≤ P.C₁ := by linarith
  have hreg0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by positivity
  rw [← ENNReal.ofReal_prod_of_nonneg hcω, regBound_eq, ← ENNReal.ofReal_mul hP0,
    ← ENNReal.ofReal_mul (mul_nonneg hP0 hLc), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := regBound_le_target P C n g hn hc1 hCC hδ hL hκ
  gcongr

/-- The moment weights of the slots: `θ = η` (no loss) or `θ = 1/4` (incoherent loss `L^{4d}`). -/
def ThetaC (P : WTParams) (θ c : ℝ) : Prop := (θ = P.η ∧ c = 0) ∨ (θ = 1 / 4 ∧ c = 4 * P.d)

theorem ThetaC.nonneg {P : WTParams} {θ c : ℝ} (h : ThetaC P θ c) (hη0 : 0 ≤ P.η) : 0 ≤ θ := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hη0
  · norm_num

theorem ThetaC.le {P : WTParams} {θ c : ℝ} (h : ThetaC P θ c) (hη4 : P.η ≤ 1 / 4) : θ ≤ 1 / 4 := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hη4
  · exact le_rfl

theorem ThetaC.c_nonneg {P : WTParams} {θ c : ℝ} (h : ThetaC P θ c) : 0 ≤ c := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact le_rfl
  · positivity

/-! ## Non-trivial objects -/

section Main

variable {P : WTParams} (hI : ProtDefs.FiltIncoherentDecayAt P) (hC : ProtDefs.FiltCoherentBoundAt P)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη4 : P.η ≤ 1 / 4) (hc1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) {θ c : ℝ} (hθ : ThetaC P θ c) (C : ℝ) (hCC : P.C₁ ≤ C)

include hI hC hd hL hη0 hη4 hc1 hδ hκ hθ hCC in
/-- **The couple target** (non-trivial couple): `CenSupM θ` on `timeBox q q'`. -/
theorem unCpl_main {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (hwf : Q.wf = true)
    (hsz : Q.size = 2 * n) (hn1 : 1 ≤ n) (LG : LayeredGarden 2) (hdec : Q.Decodes LG.garden)
    (hlay : ∀ a, LG.layer a ≤ p) (q q' : ℕ) (hq : q ≤ p) (hq' : q' ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q) (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hcase : 1 ≤ LG.incoherency Q.links ∨ (LG.incoherency Q.links = 0 ∧ IsCoherentCoupleAt p q q' Q LG))
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hcω : ∀ a ∈ S, 0 ≤ cω a)
    (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hctrl : LeafwiseControlled LG H B)
    (Mb : ℝ) (hMb : ∀ κ, ‖d5M S ω F M Fu Mu κ‖ ≤ Mb) :
    CenSupM θ (30 * P.d) (timeBox (q : ℝ) q')
      (fun ts k => kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (d5M S ω F M Fu Mu))
      (ENNReal.ofReal ((cenCplCM P.d θ).toReal * ((∏ a ∈ S, cω a) * P.L ^ c *
        ((C * Real.sqrt P.δ) ^ Q.size * P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ))) *
        leafSizeProduct LG B))) := by
  have hθ0 := hθ.nonneg hη0
  have hθ1 := hθ.le hη4
  have hlf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hCne, hsup⟩ := cenCplCM_spec P.d θ hd hθ0
  set X := (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (LG.incoherency Q.links) *
    ENNReal.ofReal (leafSizeProduct LG B) with hX
  have hXt : X ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
      (regBound_ne_top _ _ _)) ENNReal.ofReal_ne_top
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hbound : XNormRestr θ (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ
      (fun ts k => kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (d5M S ω F M Fu Mu)) ≤ X := by
    rcases hcase with hi | ⟨hg0, hcoh⟩
    · exact (hI p hp n hn θ c hθ).1 Q hwf hsz LG hdec hlay q q' hq hq' hr0 hr1 hi S ω cω hpres F
        (fun _ => false) M hM Fu Mu hMu H B hctrl
    · refine (ProtPin.tc_coh_any hC hp hn hθ0 hθ1 Q LG hq hq' hsz hcoh S ω cω hpres F (fun _ => false) M hM Fu Mu
        hMu H B hctrl).trans ?_
      rw [hX, hg0]
      have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (P.L ^ c) :=
        ENNReal.one_le_ofReal.2 (Real.one_le_rpow hL hθ.c_nonneg)
      calc (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)
          = (∏ a ∈ S, ENNReal.ofReal (cω a)) * 1 * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B) := by
            rw [mul_one]
        _ ≤ _ := by gcongr
  have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ => kernelLeavesW P.L P.γ P.δ LG H
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 (d5M S ω F M Fu Mu) := by
    intro k
    have hplain : LG.garden.IsPlain := hdec.1.1
    have hc := continuous_kernelLeavesW_time P.L P.γ P.δ H LG k (fun _ => 0) 0 (d5M S ω F M Fu Mu) Mb hMb
      (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain)
      (hctrl.summable_coset hd hL k)
    let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
      fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
    have hu : Continuous u := by
      apply Continuous.prodMk _ continuous_const
      apply continuous_pi
      intro b
      by_cases h : b.1.1 = 0
      · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
      · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
    change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelLeavesW P.L P.γ P.δ LG H x.1 x.2 k (fun _ => 0) 0 (d5M S ω F M Fu Mu)) ∘ u)
    exact hc.comp hu
  refine (hsup q q' _ X hXt hcont hbound).mono ?_
  have hm := d5_mass_le P C S cω hcω c n (LG.incoherency Q.links) hn1 hc1 hCC hδ hL hκ _ hlf
  rw [← hsz] at hm
  refine (mul_le_mul_of_nonneg_left hm zero_le).trans (le_of_eq ?_)
  rw [enn_mul_ofReal hCne _ (by
    have : 0 ≤ ∏ a ∈ S, cω a := Finset.prod_nonneg hcω
    have : 0 ≤ P.L ^ c := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ (C * Real.sqrt P.δ) ^ Q.size := pow_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) _
    have : 0 ≤ P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity)]

include hI hC hd hL hη0 hη4 hc1 hδ hκ hθ hCC in
/-- **The tree target** (non-nil chain): `SupM θ` on the closure of `timeBoxGt q q'`. -/
theorem unTree_main {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (X : RegChain) (hwf : X.wf = true)
    (hsz : X.size = 2 * n) (hn1 : 1 ≤ n) (LG : LayeredGarden 1) (hdec : X.DecodesTree LG.garden)
    (hnf : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlo : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hlay : ∀ a, LG.layer a ≤ p) (q q' : ℕ) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hlone : ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q')
    (hcase : 1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) ∨
      (LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 ∧ IsCoherentTreeAt p q q' X LG))
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hcω : ∀ a ∈ S, 0 ≤ cω a)
    (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hctrl : LeafwiseControlled LG H B)
    (Mb : ℝ) (hMb : ∀ κ, ‖d5M S ω F M Fu Mu κ‖ ≤ Mb) :
    SupM θ (30 * P.d) (closure (timeBoxGt (q : ℝ) q'))
      (fun ts k => kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 (d5M S ω F M Fu Mu))
      (ENNReal.ofReal ((supTreeCM P.d θ).toReal * ((∏ a ∈ S, cω a) * P.L ^ c *
        ((C * Real.sqrt P.δ) ^ X.size * P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ))) *
        leafSizeProduct LG B))) := by
  have hθ0 := hθ.nonneg hη0
  have hθ1 := hθ.le hη4
  have hlf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hCne, hsup⟩ := supTreeCM_spec P.d θ hd hθ0
  set g := LG.incoherency (X.treeLinks (LG.garden.sig 0)) with hg
  set Y := (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n g *
    ENNReal.ofReal (leafSizeProduct LG B) with hY
  have hYt : Y ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
      (regBound_ne_top _ _ _)) ENNReal.ofReal_ne_top
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hbound : XNormRestr θ (30 * P.d) 0 (timeBoxGt (q : ℝ) q') Set.univ
      (fun ts k => kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (d5M S ω F M Fu Mu)) ≤ Y := by
    rcases hcase with hi | ⟨hg0, hcoh⟩
    · exact (hI p hp n hn θ c hθ).2 X hwf hsz LG hdec hlay q q' hqq' hqp hr0 hlone hi S ω cω hpres F
        (fun _ => false) M hM Fu Mu hMu H B hctrl
    · refine ((hC p hp n hn θ hθ0 hθ1).2 X LG q q' hqq' hqp hsz hcoh S ω cω hpres F (fun _ => false) M hM Fu Mu
        hMu H B hctrl).trans ?_
      rw [hY, hg0]
      have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (P.L ^ c) :=
        ENNReal.one_le_ofReal.2 (Real.one_le_rpow hL hθ.c_nonneg)
      calc (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)
          = (∏ a ∈ S, ENNReal.ofReal (cω a)) * 1 * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B) := by
            rw [mul_one]
        _ ≤ _ := by gcongr
  have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ => kernelLeavesW P.L P.γ P.δ LG H
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 (d5M S ω F M Fu Mu) := by
    intro k
    have hc := continuous_kernelLeavesW_time P.L P.γ P.δ H LG k (fun _ => 0) 0 (d5M S ω F M Fu Mu) Mb hMb
      hnf hlo (hctrl.summable_coset hd hL k)
    let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) := fun ts => ((fun _ => ts 0), ts 1)
    have hu : Continuous u := (continuous_pi fun _ => continuous_apply 0).prodMk (continuous_apply 1)
    change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelLeavesW P.L P.γ P.δ LG H x.1 x.2 k (fun _ => 0) 0 (d5M S ω F M Fu Mu)) ∘ u)
    exact hc.comp hu
  refine SupM.closure_of_continuous ((hsup q q' _ Y hYt hqq' hcont hbound).mono ?_) hcont
  have hm := d5_mass_le P C S cω hcω c n g hn1 hc1 hCC hδ hL hκ _ hlf
  rw [← hsz] at hm
  refine (mul_le_mul_of_nonneg_left hm zero_le).trans (le_of_eq ?_)
  rw [enn_mul_ofReal hCne _ (by
    have : 0 ≤ ∏ a ∈ S, cω a := Finset.prod_nonneg hcω
    have : 0 ≤ P.L ^ c := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ (C * Real.sqrt P.δ) ^ X.size := pow_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) _
    have : 0 ≤ P.L ^ (-(P.η ^ 8) * (g : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity)]

end Main

/-! ## Trivial objects -/

/-- **The trivial couple** (two paired leaves, every `θ`): two root multipliers. -/
theorem unCpl_triv {d : ℕ} {θ : ℝ} (hd : 1 ≤ d) (L γ δ : ℝ) (p : ℕ) (g : Fin 2 → Mom d → ℂ) (cψ : ℝ)
    (hc1 : 1 ≤ cψ) (hg : ∀ j, GPresented (32 * d) (g j) cψ) (a b : ℕ) (LG : LayeredGarden 2)
    (hdec : RegCpl.triv.Decodes LG.garden) (H : LeafProfiles 2 d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hctrl : LeafwiseControlled LG H B) (Bx : Set (Fin 2 → ℝ)) :
    CenSupM θ (30 * d) Bx (fun ts k => coupleLeavesTopR L γ δ p g a b LG H (ts 0) (ts 1) k)
      (ENNReal.ofReal ((multD d (30 * d) * cψ) ^ 2 * profCM d θ * leafSizeProduct LG B)) := by
  obtain ⟨Ct, hCt, hCte, htriv⟩ := couple_slot_trivM (d := d) (θ := θ) hd
  have h0 := htriv L γ δ Bx LG hdec H B hctrl
  set Cd := multD d (30 * d) with hCd
  have hCd1 : 1 ≤ Cd := one_le_multD _ _ hd
  have hmult : ∀ j, IsMult (30 * d) (g j) (Cd * cψ) := fun j => isMult_of_gPresented hd hc1 (hg j)
  have hCc : 1 ≤ Cd * cψ := by nlinarith
  have htree : ∀ j : Fin 2, LG.garden.tree j = TTree.leaf := by
    intro j; fin_cases j
    exacts [hdec.2.1, hdec.2.2.1]
  have hall := allRoot_of_leaf LG.garden.tree htree
  set f0 : Mom d → ℂ := fun x => topPsi p (g 0) (LG.layer (GNode.root LG.garden.tree 0)) a x with hf0
  set f1 : Mom d → ℂ := fun x => topPsi p (g 1) (LG.layer (GNode.root LG.garden.tree 1)) b x with hf1
  have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom d), coupleLeavesTopR L γ δ p g a b LG H (ts 0) (ts 1) k =
      f0 k * (f1 k * coupleLeaves L γ δ LG H (ts 0) (ts 1) k) := by
    intro ts k
    rw [← mul_assoc]
    unfold coupleLeavesTopR coupleLeaves
    refine kernelLeavesW_const _ _ _ LG H _ 0 k _ 0 _ _ fun κ => ?_
    unfold rowTopWeightR
    rw [prod_allRoot _ hall, Fin.prod_univ_two, rowParentLayer_root, rowParentLayer_root,
      CohTrunk.coset_root, CohTrunk.coset_root]
    rfl
  set K0 : ℝ := if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then Cd * cψ else 1 with hK0
  set K1 : ℝ := if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then Cd * cψ else 1 with hK1
  have hK01 : 0 < K0 := by rw [hK0]; split_ifs <;> linarith
  have hK11 : 0 < K1 := by rw [hK1]; split_ifs <;> linarith
  have hK0le : K0 ≤ Cd * cψ := by rw [hK0]; split_ifs <;> linarith
  have hK1le : K1 ≤ Cd * cψ := by rw [hK1]; split_ifs <;> linarith
  have h1 := CenSupM.mulM (CenSupM.mulM h0 hK11 (isMult_topPsi hCc (hmult 1) p _ b)) hK01
    (isMult_topPsi hCc (hmult 0) p _ a)
  refine (CenSupM.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
  rw [← ENNReal.ofReal_mul hK11.le, ← ENNReal.ofReal_mul hK01.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCt0 : 0 ≤ Ct := hCt.le
  rw [← hCte]
  calc K0 * (K1 * (Ct * leafSizeProduct LG B)) = (K0 * K1) * Ct * leafSizeProduct LG B := by ring
    _ ≤ ((Cd * cψ) * (Cd * cψ)) * Ct * leafSizeProduct LG B := by gcongr
    _ = (Cd * cψ) ^ 2 * Ct * leafSizeProduct LG B := by ring

/-- **The nil chain** (one leaf, every `θ`, any box): one root multiplier; the filter layers are empty. -/
theorem unTree_nil {d : ℕ} {θ : ℝ} (hd : 1 ≤ d) (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hc1 : 1 ≤ cψ)
    (hg : GPresented (32 * d) g cψ) (a : ℕ) (LG : LayeredGarden 1) (hdec : RegChain.nil.DecodesTree LG.garden)
    (H : LeafProfiles 1 d) (B : (Fin 1 × TTree.Path) → NNReal) (Bx : Set (Fin 2 → ℝ))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) :
    SupM θ (30 * d) Bx (fun ts k => kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun k' => rowTopWeightR p (fun _ => g) LG ![a] k' *
          (ProtDefs.filtWeight F (fun _ => false) M k' * ProtDefs.filtWeight Fu (fun _ => false) Mu k')))
      (ENNReal.ofReal (multD d (30 * d) * cψ * leafSizeProduct LG B)) := by
  have h0 := tree_slot_nilM (θ := θ) Bx L γ δ LG hdec H B
  set Cd := multD d (30 * d) with hCd
  have hCd1 : 1 ≤ Cd := one_le_multD _ _ hd
  have hmult : IsMult (30 * d) g (Cd * cψ) := isMult_of_gPresented hd hc1 hg
  have hCc : 1 ≤ Cd * cψ := by nlinarith
  have htree : ∀ j : Fin 1, LG.garden.tree j = TTree.leaf := by
    intro j; fin_cases j; exact hdec.1
  have hall := allRoot_of_leaf LG.garden.tree htree
  have hE := MkSlots.isEmpty_branch_of_leaves htree
  have hF0 : F = ∅ := Finset.eq_empty_of_isEmpty F
  have hFu0 : Fu = ∅ := Finset.eq_empty_of_isEmpty Fu
  set f : Mom d → ℂ := fun x => topPsi p g (LG.layer (GNode.root LG.garden.tree 0)) a x with hf
  have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom d), kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
      (fun k' => rowTopWeightR p (fun _ => g) LG ![a] k' *
        (ProtDefs.filtWeight F (fun _ => false) M k' * ProtDefs.filtWeight Fu (fun _ => false) Mu k')) =
      f k * treeLeaves L γ δ LG H (ts 0) (ts 1) k := by
    intro ts k
    unfold treeLeaves
    refine kernelLeavesW_const _ _ _ LG H _ _ k _ 0 _ _ fun κ => ?_
    rw [hF0, hFu0]
    unfold ProtDefs.filtWeight
    rw [Finset.prod_empty, Finset.prod_empty, mul_one, mul_one]
    unfold rowTopWeightR
    rw [prod_allRoot _ hall, Fin.prod_univ_one, rowParentLayer_root, CohTrunk.coset_root]
    rfl
  set K0 : ℝ := if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then Cd * cψ else 1 with hK0
  have hK00 : 0 < K0 := by rw [hK0]; split_ifs <;> linarith
  have hK0le : K0 ≤ Cd * cψ := by rw [hK0]; split_ifs <;> linarith
  have h1 := SupM.mulM h0 hK00 (isMult_topPsi hCc hmult p _ a)
  refine (SupM.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
  rw [← ENNReal.ofReal_mul hK00.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  exact mul_le_mul_of_nonneg_right hK0le hlf

end WaveTurbulence.Flower.MkSlotsO
