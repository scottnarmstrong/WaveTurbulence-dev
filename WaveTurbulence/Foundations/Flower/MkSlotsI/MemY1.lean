/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.StemW2
public import WaveTurbulence.Foundations.Flower.MkSlotsI.MemW
public import WaveTurbulence.Foundations.Flower.MkSlotsI.MemRed
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb

/-! # B3s-HELPER7 MemY (part 1): the generic ingredients of the general member identity

Generic (reconstruction-level) ingredients of `MkSlotsI.member_skelValG` (`MemY2.lean`), the general twin of α's
`MkSlots.IntMember.member_skelVal`:

* **`genZa`**, **`genTw`**: the atom weight `Za` (selection test `selOK`, selection constant `∏_j [v_j] Rs_j⁻¹`, and
  the general stem node weight `genNW` at the cores of the non-hinge `G_sb` atoms, on the skeleton resonance factors)
  and the unit-top node weight `tw` (`genNW` at the core of a skeleton branch, read on the four momenta of
  `VineSpaceK.nodeWeight`), so that `topW blk ⟨F, genTw …⟩` is the unit-top part of WP4's `genCoreW` (`topW_genTw`);
* **`genWeight_factor_Za`**: the decoration multiplier `selOK · stemFilterCap · selWeightCap` of the frozen summand at
  the coset decoration of a reconstruction is `(Za · topW)(collapse κ) · ∏_s genΘs s (slotMom …) (κ|_s)` — under γ's
  stem retention `StemRet`, OR without it when the weight is not stem-dependent (`σ ≡ kSel ≡ none`: every factor is
  `1`, `genNW_none`, `genΘs_none`);
* the norm bounds `norm_genNW_le` (`≤ genM = max 1 chiDConst`), `exists_norm_genΘs_le`, `exists_norm_genZa_topW_le`;
* **`relaxPins_fixCap`**: β's `RelaxPins` for the pattern pins `fixCap LG J pat t s` (`p < s < t ≤ p + 1`, `CapGeo`,
  `CapPatValid`, every non-cap tree carries a capped flower);
* **`genKernel_reconstruction`**: β's relaxed kernel of a decoded garden at the selection `selAt` with MemW's weights is
  the one of the reconstruction (`subst`; α's `capKernel_reconstruction`); `kernelLeavesSelNWFMR_congr_m`: congruence
  in the momentum weight. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW topW)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-! ## The weight without stem dependence -/

/-- Without stem filters and selections the general stem node weight is `1`. -/
theorem genNW_none (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ)
    (z : GNode LG.garden.tree) (x : ℝ) :
    genNW LG J L (fun _ => none) (fun _ => none) Rs z x = 1 := by
  have hsel : ∀ b, b ∉ selSetCap LG J (fun _ => none) := fun b hb => by
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hb).2
    simp [selCap] at hj
  unfold genNW
  split_ifs with h1 h2 h3
  · exact absurd h3 (hsel _)
  · simp [MkSlotsG.radRaw, MkSlotsT.radSigma, MkSlotsG.shellRad, selCap, MkSlotsT.radProd]
  · rfl
  · rfl

/-- Without stem filters and selections the per-slot factor is `1`. -/
theorem genΘs_none {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ)
    (s : ReplacementSlot S) (k : Mom d) (ρ : NativeRelativeDecoration D hS d s) :
    genΘs D hS layer hLayer J L (fun _ => none) (fun _ => none) Rs s k ρ = 1 := by
  cases s with
  | inl p =>
    simp only [genΘs]
    refine Finset.prod_eq_one fun a _ => ?_
    split_ifs
    · rfl
    · exact genNW_none _ J L Rs _ _
  | inr b =>
    simp only [genΘs]
    refine Finset.prod_eq_one fun a _ => ?_
    split_ifs
    · rfl
    · exact genNW_none _ J L Rs _ _

/-! ## The atom weight and the unit-top weight -/

section Za

variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → CLBlock S}
  (Φ : SpliceShape blk Gsb) (hd : Disj blk) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
  (Rs : Fin w → ℝ)

/-- **The atom weight `Za`** at a skeleton decoration `κ'`: the selection test `selOK`, the selection constant
`∏_j [v_j] Rs_j⁻¹` and the general stem node weight `genNW` at the cores of the non-hinge `G_sb` atoms `Φ.br c`, at
the skeleton resonance factors of the coset decoration of `κ'` (WP4's `genCoreW` without its unit-top part). -/
def genZa (base : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ' : GenDecoration S d n nfl) : ℂ :=
  (selOK (layeredReconstruction D hS layer hLayer) J kSel : ℂ) *
    ((∏ j, (selCap (layeredReconstruction D hS layer hLayer) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
      ∏ c ∈ Finset.univ.filter (fun c => c ∉ Φ.hinges hd),
        genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS (Φ.br c)).toNode
          (omegaNode S (cosetDecoration S L base κ'.1) (Φ.br c)))

/-- **The unit-top node weight `tw`**: at a skeleton branch `b`, the general stem node weight at the core of `b`, at the
resonance factor of the four momenta `![k_b, k_{b0}, k_{b1}, k_{b2}]` (read by `VineSpaceK.nodeWeight`). -/
def genTw : GBranch S.tree → (Fin 4 → Mom d) → ℂ :=
  fun b q => genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS b).toNode
    (resFactor (q 1) (q 2) (q 3) (q 0))

/-- The units' top weights of `genTw` are `genNW` at the cores of the unit uppers, on the skeleton resonance factors. -/
theorem topW_genTw (F : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) :
    topW blk ⟨F, genTw D hS layer hLayer J L σ kSel Rs⟩ L base x =
      ∏ j : ι, genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS (blk j).upper).toNode
        (omegaNode S (cosetDecoration S L base x) (blk j).upper) := rfl

/-- `selOK` times WP4's core multiplier is the atom weight times the units' top weights. -/
theorem selOK_mul_genCoreW (F : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (base : Mom d)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ' : GenDecoration S d n nfl) :
    (selOK (layeredReconstruction D hS layer hLayer) J kSel : ℂ) *
        genCoreW D hS layer hLayer Φ hd J L σ kSel Rs base κ' =
      genZa D hS layer hLayer Φ hd J L σ kSel Rs base κ' *
        topW blk ⟨F, genTw D hS layer hLayer J L σ kSel Rs⟩ L base κ'.1 := by
  rw [topW_genTw]
  unfold genCoreW genZa
  ring

/-- **The decoration multiplier of the frozen summand on a reconstruction, factorized**: `selOK · stemFilterCap ·
selWeightCap` at the coset decoration of `κ` is `(Za · topW)(collapse κ) · ∏_s genΘs s (slotMom …) (κ|_s)`, under γ's
stem retention or when the weight is not stem-dependent (`σ ≡ kSel ≡ none`). -/
theorem genWeight_factor_Za
    (hR : MkSlotsT.StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J ∨
      ((σ = fun _ => none) ∧ kSel = fun _ => none))
    (F : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) (base : Mom d) :
    ((selOK (layeredReconstruction D hS layer hLayer) J kSel *
        (stemFilterCap (layeredReconstruction D hS layer hLayer) J L σ (cosetDecoration (D.garden hS) L base κ.1) *
          selWeightCap (layeredReconstruction D hS layer hLayer) J
            (selCap (layeredReconstruction D hS layer hLayer) J kSel) Rs
            (cosetDecoration (D.garden hS) L base κ.1)) : ℝ) : ℂ) =
      (genZa D hS layer hLayer Φ hd J L σ kSel Rs base (collapseGenDecoration D hS κ) *
          topW blk ⟨F, genTw D hS layer hLayer J L σ kSel Rs⟩ L base (collapseGenDecoration D hS κ).1) *
        ∏ s, genΘs D hS layer hLayer J L σ kSel Rs s
          (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 s) (restrictRelativeDecorations D hS κ s) := by
  rcases hR with hR | ⟨rfl, rfl⟩
  · rw [Complex.ofReal_mul, genWeight_factor_core D hS layer hLayer Φ hd J L σ kSel Rs hR κ base,
      ← selOK_mul_genCoreW D hS layer hLayer Φ hd J L _ _ Rs F base]
    ring
  · have e1 : stemFilterCap (layeredReconstruction D hS layer hLayer) J L (fun _ => none)
        (cosetDecoration (D.garden hS) L base κ.1) = 1 := MkSlots.IntWeight.stemFilterCap_none _ _ _ _
    have e2 : selWeightCap (layeredReconstruction D hS layer hLayer) J
        (selCap (layeredReconstruction D hS layer hLayer) J (fun _ => none)) Rs
        (cosetDecoration (D.garden hS) L base κ.1) = 1 := MkSlots.IntWeight.selWeightCap_none _ _ _ _
    have e3 := MkSlots.IntWeight.selOK_none (layeredReconstruction D hS layer hLayer) J
    simp only [e1, e2, e3, topW_genTw, genZa, genΘs_none]
    simp only [selCap, Option.bind_none, Option.elim_none, Finset.prod_const_one, mul_one, one_mul,
      Complex.ofReal_one]
    refine (one_mul 1).symm.trans (congrArg₂ _ ?_ ?_)
    · exact (Finset.prod_eq_one fun c _ => genNW_none _ J L Rs _ _).symm
    · exact (Finset.prod_eq_one fun j _ => genNW_none _ J L Rs _ _).symm

end Za

/-! ## Norm bounds -/

/-- The uniform bound of the general stem node weight: `max 1 chiDConst`. -/
def genM : ℝ := max 1 chiDConst

theorem one_le_genM : 1 ≤ genM := le_max_left _ _

/-- **The general stem node weight is bounded by `genM`** (`|radProd| ≤ 1`, `|chiD| ≤ chiDConst`). -/
theorem norm_genNW_le (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (z : GNode LG.garden.tree) (x : ℝ) : ‖genNW LG J L σ kSel Rs z x‖ ≤ genM := by
  have h1 := one_le_genM
  unfold genNW
  split_ifs with hb hs hv
  · have hr := MkSlotsT.radProd_mem_Icc (MkSlotsG.radRaw LG J L σ kSel Rs ⟨z.1, hb⟩) x
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr.1]
    calc _ ≤ 1 * genM := mul_le_mul hr.2 ((abs_chiD_le _).trans (le_max_right _ _)) (abs_nonneg _) zero_le_one
      _ = genM := one_mul _
  · have hr := MkSlotsT.radProd_mem_Icc (MkSlotsG.radRaw LG J L σ kSel Rs ⟨z.1, hb⟩) x
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2.trans h1
  · rw [norm_one]; exact h1
  · rw [norm_one]; exact h1

/-- A finite product of factors bounded by `genM` is bounded by `genM ^ N`, `N ≥ #factors`. -/
theorem norm_prod_le_genM {α : Type*} (s : Finset α) (f : α → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ genM) (N : ℕ)
    (hN : s.card ≤ N) : ‖∏ i ∈ s, f i‖ ≤ genM ^ N := by
  rw [norm_prod]
  calc ∏ i ∈ s, ‖f i‖ ≤ ∏ _i ∈ s, genM := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hf
    _ = genM ^ s.card := Finset.prod_const _
    _ ≤ genM ^ N := pow_le_pow_right₀ one_le_genM hN

section Bounds

variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → CLBlock S}
  (Φ : SpliceShape blk Gsb) (hd : Disj blk) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
  (Rs : Fin w → ℝ)

/-- **The per-slot factors are uniformly bounded.** -/
theorem exists_norm_genΘs_le :
    ∃ C : ℝ, ∀ (s : ReplacementSlot S) (k : Mom d) (ρ : NativeRelativeDecoration D hS d s),
      ‖genΘs D hS layer hLayer J L σ kSel Rs s k ρ‖ ≤ C := by
  have h : ∀ s : ReplacementSlot S, ∃ N : ℕ, ∀ (k : Mom d) (ρ : NativeRelativeDecoration D hS d s),
      ‖genΘs D hS layer hLayer J L σ kSel Rs s k ρ‖ ≤ genM ^ N := by
    intro s
    cases s with
    | inl p =>
      refine ⟨_, fun k ρ => norm_prod_le_genM Finset.univ _ (fun a _ => ?_) _ le_rfl⟩
      split_ifs
      · rw [norm_one]; exact one_le_genM
      · exact norm_genNW_le _ J L σ kSel Rs _ _
    | inr b =>
      refine ⟨_, fun k ρ => norm_prod_le_genM Finset.univ _ (fun a _ => ?_) _ le_rfl⟩
      split_ifs
      · rw [norm_one]; exact one_le_genM
      · exact norm_genNW_le _ J L σ kSel Rs _ _
  choose N hN using h
  exact ⟨genM ^ (∑ s, N s), fun s k ρ => (hN s k ρ).trans (pow_le_pow_right₀ one_le_genM
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)))⟩

/-- Norm bookkeeping for `exists_norm_genZa_topW_le`. -/
theorem norm_aux (A B C₁ C₂ : ℂ) (x y : ℝ) (h₁ : ‖C₁‖ ≤ x) (h₂ : ‖C₂‖ ≤ y) (hx : 0 ≤ x) :
    ‖A * (B * C₁) * C₂‖ ≤ ‖A * B‖ * (x * y) := by
  rw [show A * (B * C₁) * C₂ = (A * B) * (C₁ * C₂) by ring, norm_mul (A * B), norm_mul C₁ C₂]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (norm_nonneg _) hx) (norm_nonneg _)

/-- **The atom weight times the units' top weights is uniformly bounded** (a constant times finitely many factors
`genNW`). -/
theorem exists_norm_genZa_topW_le (F : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (base : Mom d)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    ∃ C : ℝ, ∀ κ' : GenDecoration S d n nfl,
      ‖genZa D hS layer hLayer Φ hd J L σ kSel Rs base κ' *
        topW blk ⟨F, genTw D hS layer hLayer J L σ kSel Rs⟩ L base κ'.1‖ ≤ C := by
  refine ⟨‖(selOK (layeredReconstruction D hS layer hLayer) J kSel : ℂ) *
      ∏ j, (selCap (layeredReconstruction D hS layer hLayer) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))‖ *
    (genM ^ Fintype.card (GBranch Gsb.tree) * genM ^ Fintype.card ι), fun κ' => ?_⟩
  rw [topW_genTw]
  unfold genZa
  refine norm_aux _ _ _ _ _ _ ?_ ?_ (pow_nonneg (zero_le_one.trans one_le_genM) _)
  · exact norm_prod_le_genM _ _ (fun c _ => norm_genNW_le _ J L σ kSel Rs _ _) _ (Finset.card_le_univ _)
  · exact norm_prod_le_genM _ _ (fun j _ => norm_genNW_le _ J L σ kSel Rs _ _) _ (by rw [Finset.card_univ])

end Bounds

/-! ## The pattern pins satisfy β's `RelaxPins` -/

/-- **`RelaxPins` for the pattern pins** (`p < s < t ≤ p + 1`): every pin is in layer `p` (β's `fixCap_layer`) with
value `s` or (at a root) `t`; along a strict descendant the lower pin is `s`. -/
theorem relaxPins_fixCap {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {pat : Fin w → FixPat} {t s : ℝ}
    (hG : CapGeo LG J p) (hpat : CapPatValid LG J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1) :
    MkSlotsB.RelaxPins LG.layer (fun _ => t) (fixCap LG J pat t s) where
  val b v hv := by
    rw [MkSlotsB.fixCap_layer hG hpat hroot hv]
    rcases MkSlotsB.fixCap_value hv with rfl | ⟨rfl, -, -⟩
    · exact ⟨hs.1, by linarith [hs.2], hs.2.le⟩
    · exact ⟨hs.1.trans hs.2, ht, le_rfl⟩
  mono x y v v' hx hy hxy := by
    have hnr : x.1.2 ≠ [] := by
      obtain ⟨-, l, hl, he⟩ := hxy
      rw [he]
      simp [hl]
    have hv : v = s := by
      rcases MkSlotsB.fixCap_value hx with h | ⟨-, h0, -⟩
      · exact h
      · exact absurd h0 hnr
    rcases MkSlotsB.fixCap_value hy with h | ⟨h, -, -⟩
    · rw [hv, h]
    · rw [hv, h]; exact hs.2.le

/-! ## The kernel of a decoded garden is the one of the reconstruction -/

/-- Congruence of β's kernel in the momentum weight. -/
theorem kernelLeavesSelNWFMR_congr_m (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m m' : (GNode LG.garden.tree → Mom d) → ℂ)
    (hm : ∀ k, m k = m' k) (Θg : GenDecoration LG.garden d nroot nfl → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    MkSlotsB.kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m Θg fix =
      MkSlotsB.kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m' Θg fix := by
  rw [show m = m' from funext hm]

/-- **The general kernel of a decoded garden at the selection `selAt` is the one of the reconstruction** (twin of α's
`capKernel_reconstruction` for β's relaxed kernel with MemW's weights). -/
theorem genKernel_reconstruction (P : WTParams) {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hprime : IsPrimeGarden S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden)
    (σg : VineA.NormalizedSplice.GroupPrescription S) (J : Finset (Fin w)) (p : ℕ) (pat : Fin w → FixPat)
    (kSel σ : Fin w → Option ℕ) (Rs : Fin w → ℝ) (t s : ℝ)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (roots : Fin w → (Fin P.d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom P.d)) :
    MkSlotsB.kernelLeavesSelNWFMR P.L P.γ P.δ LG (MkSlots.anchProfiles J LG h P.L roots) (fun _ => t) 0 roots 0
        (fun κ => Represents.selAt P 0 ⟨S, hprime, D, hd⟩ σg κ)
        (fun k => ∏ z, MkSlots.capNodeW P.L P.γ P.δ p s LG J Rf dag z (k z))
        (fun κ => ((selOK LG J kSel * (stemFilterCap LG J P.L σ (cosetDecoration LG.garden P.L 0 κ.1) *
          selWeightCap LG J (selCap LG J kSel) Rs (cosetDecoration LG.garden P.L 0 κ.1)) : ℝ) : ℂ))
        (fixCap LG J pat t s) =
      MkSlotsB.kernelLeavesSelNWFMR P.L P.γ P.δ (layeredReconstruction D hS layer hLayer)
        (MkSlots.anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots) (fun _ => t) 0 roots 0
        (fun κ => VineA.NormalizedSplice.selOf σg P.L P.γ P.η 0 (collapseGenDecoration D hS κ).1)
        (fun k => ∏ z, MkSlots.capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag z (k z))
        (fun κ => ((selOK (layeredReconstruction D hS layer hLayer) J kSel *
          (stemFilterCap (layeredReconstruction D hS layer hLayer) J P.L σ
              (cosetDecoration (D.garden hS) P.L 0 κ.1) *
            selWeightCap (layeredReconstruction D hS layer hLayer) J
              (selCap (layeredReconstruction D hS layer hLayer) J kSel) Rs
              (cosetDecoration (D.garden hS) P.L 0 κ.1)) : ℝ) : ℂ))
        (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) := by
  subst hspec
  rfl

end WaveTurbulence.Flower.MkSlotsI
