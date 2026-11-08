/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack

/-! # D3 PROT-PIN: cap couples reduced to their paired tree (multiplier, kernel, budget)

For a protected cap couple (D2c `CapData X LG LG1`), D3's multiplier read through `D.capM` is the cap's star factor
times D3's multiplier on the paired tree `LG1` with the pulled data `capcS S = pullS (capι D) (S.erase cap)`,
`pullF D.βc F`, … and the dagger `ind ∘ (· ∘ D.ρ)` (`capc_capM_eq`). On every coset decoration of `LG1` the lone leaf
carries the output `k` (`capc_lone_coset`), so the cap's star factor is the constant `capcStar S ω k` and the cap
kernel is `H(lone) k · capcStar S ω k · (paired-tree kernel)` (`capc_kernel_eq`). With the terminal pinned the port
time is irrelevant (`capc_port_irrel`). Budget bookkeeping: `capc_cost`, `capc_leaf`, the scaling of the per-output
budgets. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {d : ℕ}

/-- The pulled star set of the paired tree. -/
def capcS (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree)) : Finset (GNode LG1.garden.tree) :=
  pullS (capι Dc) (S.erase Dc.cap)

/-- The cap's star factor at output `k`. -/
def capcStar (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (k : Mom d) : ℂ :=
  if Dc.cap ∈ S then ω Dc.cap (WithLp.toLp 2 fun _ => k) else 1

/-- The cap's star cost. -/
def capcCost (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) : ℝ :=
  if Dc.cap ∈ S then max (cω Dc.cap) 0 else 1

theorem capcCost_nonneg (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    0 ≤ capcCost Dc S cω := by
  unfold capcCost; split_ifs <;> simp

theorem norm_capcStar_le (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (cω : GNode LG.garden.tree → ℝ) {J : ℕ}
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a)) (k : Mom d) :
    ‖capcStar Dc S ω k‖ ≤ capcCost Dc S cω := by
  unfold capcStar capcCost
  split_ifs with h
  · exact FiltCoh.norm_star_le (hpres _ h) _
  · simp

/-- D3's multiplier of the paired tree. -/
def capcMult (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) : (GNode LG1.garden.tree → Mom d) → ℂ :=
  fun κ => Flower.IncTop.starWeight (capcS Dc S) (fun z => ω (capι Dc z)) κ *
    filtWeight (pullF Dc.βc F) (fun _ => false) (fun y => M (Dc.βc y)) κ *
    filtWeight (pullF Dc.βc Fu) (fun _ => false) (fun y => Mu (Dc.βc y)) κ *
    (((fun K : GNode LG1.garden.tree → Mom d => ind fun a => K (Dc.ρ a)) κ : ℝ) : ℂ)

/-- **The cap multiplier on the paired tree.** -/
theorem capc_capM_eq (Dc : CapData X LG LG1) (hX : X ≠ .nil) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (K : GNode LG1.garden.tree → Mom d) :
    Dc.capM (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) K =
      capcStar Dc S ω (K Dc.lone1) * capcMult Dc S ω F M Fu Mu ind K := by
  unfold CapData.capM capcMult capcStar capcS
  simp only
  rw [Dc.starWeight_cap S ω, show ∀ a b c e g : ℂ, a * b * c * e * g = a * (b * c * e) * g from
    fun _ _ _ _ _ => by ring, starFilt_local' (S.erase Dc.cap) (Dc.hroot_erase hX S)]
  have e1 : (∏ b : GBranch LG.garden.tree, fD3' (S.erase Dc.cap) ω F (fun _ => false) M Fu Mu b
      (bstar (fun a => K (Dc.ρ a)) b)) =
      ∏ b : GBranch LG1.garden.tree, fD3' (S.erase Dc.cap) ω F (fun _ => false) M Fu Mu (Dc.βc b) (bstar K b) := by
    rw [← Dc.βc.prod_comp]
    simp only [Dc.bstar_cap]
  rw [e1, pull_mult (capEmb Dc), Dc.ρ_one Dc.cap (by simp [CapData.cap])]
  ring

/-- The lone leaf of the paired tree carries the output. -/
theorem capc_lone_coset (Dc : CapData X LG LG1) (L : ℝ) (k : Mom d)
    (κ : GenDecoration LG1.garden d (fun _ => 0) 0) : cosetDecoration LG1.garden L k κ.1 Dc.lone1 = k := by
  show k + latticePoint L (κ.1 Dc.lone1) = k
  rw [Dc.lone1_eq_root κ.2.1, κ.2.2.1 0, WaveTurbulence.Links.latticePoint_zero, add_zero]

/-- **The cap kernel**: the input of the cap pair, the cap's star factor, and the paired tree's kernel. -/
theorem capc_kernel_eq (Dc : CapData X LG LG1) (hX : X ≠ .nil) (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d) :
    kernelProt L γ δ LG H (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) up s fix k (fun _ => 0) 0 =
      (H ((0 : Fin 2), X.lonePath) k : ℂ) * capcStar Dc S ω k *
        kernelProt L γ δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun b => up (Dc.βc b)) 0
          (fun b => fix (Dc.βc b)) k (fun _ => 0) 0 := by
  rw [Dc.kernelProt_cap, mul_assoc]
  congr 1
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum]
  have hs : ∑' κ : GenDecoration LG1.garden d (fun _ => 0) 0, protSummand L γ δ LG1 (capH H)
        (Dc.capM (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))) (fun b => up (Dc.βc b)) 0 (fun b => fix (Dc.βc b)) k κ =
      capcStar Dc S ω k * ∑' κ : GenDecoration LG1.garden d (fun _ => 0) 0, protSummand L γ δ LG1 (capH H)
        (capcMult Dc S ω F M Fu Mu ind) (fun b => up (Dc.βc b)) 0 (fun b => fix (Dc.βc b)) k κ := by
    rw [← tsum_mul_left]
    refine tsum_congr fun κ => ?_
    unfold protSummand
    rw [capc_capM_eq Dc hX S ω F M Fu Mu ind, capc_lone_coset Dc L k κ]
    ring
  rw [hs]
  ring

/-- **The port time is irrelevant** when every lone parent is designated. -/
theorem capc_port_irrel {w : ℕ} (L γ δ : ℝ) (G : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode G.garden.tree → Mom d) → ℂ) (up : GBranch G.garden.tree → ℝ)
    (fix : GBranch G.garden.tree → Option ℝ) (k : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hfix : ∀ b, G.garden.IsLoneParent b → fix b ≠ none) (s₁ s₂ : ℝ) :
    kernelProt L γ δ G H m up s₁ fix k nroot nfl = kernelProt L γ δ G H m up s₂ fix k nroot nfl := by
  have hset : ∀ s' : ℝ, kDomainFix G up fix ∩
      {τ | ∀ b, G.garden.IsLoneParent b → fix b = none → s' < τ b} = kDomainFix G up fix := by
    intro s'
    exact Set.inter_eq_left.mpr fun τ _ b hb hf => absurd hf (hfix b hb)
  unfold kernelProt
  rw [hset s₁, hset s₂]

/-- The lone parent of a decoded chain sits at `X.lonePath.dropLast`. -/
theorem capc_loneParent_path {G : Garden 1} (hX : X.DecodesTree G) (b : GBranch G.tree) (hb : G.IsLoneParent b) :
    b.1.1 = 0 ∧ b.1.2 = X.lonePath.dropLast := by
  obtain ⟨ℓ, hℓ, -, i, hi⟩ := hb
  have hl : ℓ.1.2 = X.lonePath := (Reg.decodesTree_lone_iff hX ℓ).1 hℓ
  refine ⟨Subsingleton.elim _ _, ?_⟩
  rw [← hl, hi, List.dropLast_concat]

/-- `rootTerm`, `penTerm`, `termChild` designate the terminal node (the lone parent). -/
theorem capc_fix_pinned {G : Garden 1} (hX : X.DecodesTree G) (cfg : ProtCfg)
    (hcfg : cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i) (s t up : ℝ)
    (b : GBranch G.tree) (hb : G.IsLoneParent b) : cfg.fix X s t up b ≠ none := by
  obtain ⟨h0, hp⟩ := capc_loneParent_path hX b hb
  unfold ProtCfg.fix
  rw [if_pos (by rw [h0]; rfl), hp]
  rcases hcfg with rfl | rfl | ⟨i, rfl⟩
  · simp only [ProtCfg.pins, List.lookup]
    split <;> simp
  · simp only [ProtCfg.pins, List.lookup]
    split
    · simp
    · simp
  · simp only [ProtCfg.pins, List.lookup]
    simp

/-! ### Bookkeeping -/

theorem capc_cost (Dc : CapData X LG LG1) (hX : X ≠ .nil) (S : Finset (GNode LG.garden.tree))
    (cω : GNode LG.garden.tree → ℝ) :
    starCost S cω = capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z)) := by
  have hsplit : starCost S cω = capcCost Dc S cω * ∏ a ∈ (S.erase Dc.cap), max (cω a) 0 := by
    unfold starCost capcCost
    split_ifs with hcap
    · exact (Finset.mul_prod_erase S _ hcap).symm
    · rw [Finset.erase_eq_of_notMem hcap, one_mul]
  rw [hsplit, prod_cost_branch (S.erase Dc.cap) (Dc.hroot_erase hX S) cω,
    ← Dc.βc.prod_comp (fun b => costB (S.erase Dc.cap) cω b), pull_cost (capEmb Dc)]
  rfl

theorem capc_pres (Dc : CapData X LG LG1) {S : Finset (GNode LG.garden.tree)}
    {ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ} {cω : GNode LG.garden.tree → ℝ} {J : ℕ}
    (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (cω a)) :
    ∀ a ∈ capcS Dc S, Flower.IncTop.StarPresented J (ω (capι Dc a)) (cω (capι Dc a)) :=
  pull_pres (capι Dc) fun a ha => hpres a (Finset.mem_of_mem_erase ha)

/-- The leaf bounds of the paired tree. -/
def capcB (B : (Fin 2 × TTree.Path) → NNReal) : (Fin 1 × TTree.Path) → NNReal := fun z => B ((0 : Fin 2), z.2)

theorem capc_leafwise (Dc : CapData X LG LG1) {H : LeafProfiles 2 d} {B : (Fin 2 × TTree.Path) → NNReal}
    (hH : LeafwiseControlled LG H B) : LeafwiseControlled LG1 (capH H) (capcB B) := fun ℓ hℓ => by
  have hm : Dc.ιL ℓ ∈ inputLeaves LG.garden := by
    rw [Dc.inputLeaves_cap]; exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hℓ)
  exact hH _ hm

theorem capc_leaf (Dc : CapData X LG LG1) (B : (Fin 2 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = (B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B) := by
  unfold leafSizeProduct
  rw [Dc.inputLeaves_cap, Finset.prod_insert Dc.lone_not_input, Finset.prod_map]
  rfl

theorem capc_input_le (Dc : CapData X LG LG1) {H : LeafProfiles 2 d} {B : (Fin 2 × TTree.Path) → NNReal}
    (hH : LeafwiseControlled LG H B) (k : Mom d) :
    ‖(H ((0 : Fin 2), X.lonePath) k : ℂ)‖ ≤ (B Dc.ℓ0.1 : ℝ) := by
  have hℓ0 : Dc.ℓ0 ∈ inputLeaves LG.garden := by rw [Dc.inputLeaves_cap]; exact Finset.mem_insert_self _ _
  have hβ : 0 ≤ (B Dc.ℓ0.1 : ℝ) := NNReal.coe_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hp := SNormR_pointwise (H Dc.ℓ0.1) _ hβ (hH Dc.ℓ0 hℓ0) k
  refine hp.trans ?_
  calc (B Dc.ℓ0.1 : ℝ) * jbr k ^ (-((40 * d : ℕ) : ℝ)) ≤ (B Dc.ℓ0.1 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos (Induct.one_le_jbr k)
          (by simp)) hβ
    _ = _ := mul_one _

/-- **A constant factor in a restricted norm.** -/
theorem capc_rn_const_mul {r : ℕ} (θ : ℝ) (B : Set (Fin r → ℝ)) (c : ℂ) (f : (Fin r → ℝ) → ℂ) :
    rn θ B (fun x => c * f x) ≤ ‖c‖ₑ * rn θ B f := by
  unfold rn
  exact VineEstS3.Eng.XNorm00Restr_const_mul_le θ _ _ _ _

/-! ### The budgets scale with the leaf size and the star cost -/

theorem pairRb_scale (P : WTParams) (c' : ℝ) (n g : ℕ) (a b leaf CS : ℝ) :
    a * b * pairRb P c' n g leaf CS = pairRb P c' n g (a * leaf) (b * CS) := by
  unfold pairRb; ring

theorem termRb_scale (P : WTParams) (c' : ℝ) (n g : ℕ) (a b leaf CS : ℝ) :
    a * b * termRb P c' n g leaf CS = termRb P c' n g (a * leaf) (b * CS) := by
  unfold termRb; ring

theorem twoRb_scale (P : WTParams) (e : ℝ) (n g : ℕ) (a b leaf CS : ℝ) :
    a * b * twoRb P e n g leaf CS = twoRb P e n g (a * leaf) (b * CS) := by
  unfold twoRb; ring

/-- **The cap per-output bound from the paired tree's.** -/
theorem capc_perk {r : ℕ} {θ : ℝ} (Bx : Set (Fin r → ℝ)) (h c : ℂ) (f : (Fin r → ℝ) → ℂ) {β κc C R : ℝ}
    (hβ : 0 ≤ β) (hκc : 0 ≤ κc) (hC : 0 ≤ C) (hR : 0 ≤ R) (hh : ‖h‖ ≤ β) (hc : ‖c‖ ≤ κc)
    (hf : rn θ Bx f ≤ ENNReal.ofReal (C * R)) :
    rn θ Bx (fun x => h * c * f x) ≤ ENNReal.ofReal (C * (β * κc * R)) := by
  refine (capc_rn_const_mul θ Bx (h * c) f).trans ?_
  calc ‖h * c‖ₑ * rn θ Bx f ≤ ENNReal.ofReal (β * κc) * ENNReal.ofReal (C * R) := by
        refine mul_le_mul' ?_ hf
        rw [← ofReal_norm, norm_mul]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul hh hc (norm_nonneg _) hβ)
    _ = ENNReal.ofReal (C * (β * κc * R)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hβ hκc)]
        congr 1; ring

end WaveTurbulence.Flower.ProtPin
