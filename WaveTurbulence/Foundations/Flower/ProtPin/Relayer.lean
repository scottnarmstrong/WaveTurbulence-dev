/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Statement
public import WaveTurbulence.Foundations.Flower.ProtKer.Bridge
public import WaveTurbulence.Foundations.Flower.ProtKer.Sanity
public import WaveTurbulence.Foundations.IncohInst.Enhanced.TreeIncoh1
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Mono

/-! # D3 PROT-PIN: leaf relayering and small kernel facts

Kernels (`kernelProt`, `kernelLeaves`, `kernelLeavesW`) and incoherency indices read the layers of branching
nodes only. `relayer LG f` keeps them and gives the leaves the layers `f`; it is used to put the lone leaf of a
protected paired tree in the layer `q'` of the box, and the leaves of a cap couple in layer `0`, as the gates
require. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

section Relayer

variable {w : ℕ}

/-- Branch layers kept, leaf layers (non-branching nodes) given by `f`. -/
def relayerFun (LG : LayeredGarden w) (f : GNode LG.garden.tree → ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 ∈ (LG.garden.tree a.1.1).branching then LG.layer a else f a

/-- The relayered garden (same garden). -/
def relayer (LG : LayeredGarden w) (f : GNode LG.garden.tree → ℕ)
    (hf : IsLayering LG.garden (relayerFun LG f)) : LayeredGarden w :=
  ⟨LG.garden, relayerFun LG f, hf⟩

variable (LG : LayeredGarden w) (f : GNode LG.garden.tree → ℕ) (hf : IsLayering LG.garden (relayerFun LG f))

theorem relayer_layer_branch (b : GBranch LG.garden.tree) :
    (relayer LG f hf).layer b.toNode = LG.layer b.toNode := by
  change relayerFun LG f b.toNode = _
  unfold relayerFun
  exact if_pos b.2

theorem relayer_layer_leaf (a : GNode LG.garden.tree) (ha : a.1.2 ∉ (LG.garden.tree a.1.1).branching) :
    (relayer LG f hf).layer a = f a := by
  change relayerFun LG f a = _
  unfold relayerFun
  exact if_neg ha

theorem kDomainFix_relayer (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kDomainFix (relayer LG f hf) up fix = kDomainFix LG up fix := by
  ext τ
  simp only [kDomainFix, Set.mem_setOf_eq]
  refine forall_congr' fun b => ?_
  rw [show (relayer LG f hf).layer b.toNode = LG.layer b.toNode from relayer_layer_branch LG f hf b]
  exact Iff.rfl

theorem kernelProt_relayer (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles w d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelProt L γ δ (relayer LG f hf) H m up s fix k₀ nroot nfl = kernelProt L γ δ LG H m up s fix k₀ nroot nfl := by
  unfold kernelProt
  rw [kDomainFix_relayer]
  rfl

theorem incoherency_relayer (links : List ((Fin w × TTree.Path) × (Fin w × TTree.Path))) :
    (relayer LG f hf).incoherency links = LG.incoherency links := by
  unfold LayeredGarden.incoherency
  congr 1
  refine Finset.filter_congr fun bb _ => ?_
  rw [show (relayer LG f hf).layer bb.1.toNode = LG.layer bb.1.toNode from relayer_layer_branch LG f hf bb.1,
    show (relayer LG f hf).layer bb.2.toNode = LG.layer bb.2.toNode from relayer_layer_branch LG f hf bb.2]
  exact Iff.rfl

end Relayer

/-! ### Garden facts -/

theorem not_loneParent_of_isPlain {w : ℕ} {G : Garden w} (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsLoneParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  unfold Garden.IsLone at hℓ
  rw [hG ℓ] at hℓ
  simp at hℓ

theorem not_flowerParent_of_isPlain {w : ℕ} {G : Garden w} (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  unfold Garden.IsFlower at hℓ
  rw [hG ℓ] at hℓ
  simp at hℓ

theorem not_flowerParent_of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  unfold Garden.IsFlower at hℓ
  rw [hX.2.1 ℓ] at hℓ
  split_ifs at hℓ
  all_goals simp at hℓ

theorem not_mem_branching_of_leaf {w : ℕ} {T : Fin w → TTree} (ℓ : GLeaf T) :
    ℓ.toNode.1.2 ∉ (T ℓ.toNode.1.1).branching :=
  fun h => TTree.not_mem_branching_of_mem_leaves _ ℓ.2 h

/-- With the multiplier `1`, the weighted leafwise kernel is the leafwise kernel. -/
theorem kernelLeavesW_one {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (hm : ∀ k, m k = 1) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold Flower.Stage1W.kernelLeavesW kernelLeaves
  simp only [hm, one_mul]

/-- Without lone parents the port time `s` is irrelevant. -/
theorem kernelProt_s_irrel {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s s' : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hl : ∀ b, ¬ LG.garden.IsLoneParent b) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl = kernelProt L γ δ LG H m up s' fix k₀ nroot nfl := by
  unfold kernelProt
  rw [loneConstraint_vacuous LG up s fix hl, loneConstraint_vacuous LG up s' fix hl]

/-- The empty-multiplier product with a dagger equal to `1` is `1`. -/
theorem alphaMult_eq_one {w d : ℕ} {G : Garden w} (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (M Mu : GBranch G.tree → ℝ) (ind : (GNode G.tree → Mom d) → ℝ) (hind : ∀ κ, ind κ = 1)
    (κ : GNode G.tree → Mom d) :
    Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ * filtWeight ∅ (fun _ => false) Mu κ *
      (ind κ : ℂ) = 1 := by
  simp [Flower.IncTop.starWeight, filtWeight, hind κ]

/-- The gate multiplier with empty layers is `1`. -/
theorem gateMult_eq_one {w d : ℕ} {G : Garden w} (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ ann M κ * filtWeight ∅ (fun _ => false) Mu κ = 1 := by
  simp [Flower.IncTop.starWeight, filtWeight]

/-- `XNormRestr` is antitone in the agreement sets. -/
theorem XNormRestr_mono_set {r d : ℕ} {θ : ℝ} {Λ₁ Λ₂ : ℕ} {B B' : Set (Fin r → ℝ)} {K K' : Set (Mom d)}
    (hB : B' ⊆ B) (hK : K' ⊆ K) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B' K' F ≤ XNormRestr θ Λ₁ Λ₂ B K F :=
  le_iInf₂ fun G hG => iInf₂_le G fun t ht k hk => hG t (hB ht) k (hK hk)

/-- `XNormRestr` only sees the function on the agreement set. -/
theorem XNormRestr_congr {r d : ℕ} {θ : ℝ} {Λ₁ Λ₂ : ℕ} {B : Set (Fin r → ℝ)} {K : Set (Mom d)}
    {F F' : (Fin r → ℝ) → Mom d → ℂ} (h : ∀ t ∈ B, ∀ k ∈ K, F t k = F' t k) :
    XNormRestr θ Λ₁ Λ₂ B K F = XNormRestr θ Λ₁ Λ₂ B K F' := by
  unfold XNormRestr
  refine iInf_congr fun G => ?_
  refine iInf_congr_Prop ⟨fun hG t ht k hk => (hG t ht k hk).trans (h t ht k hk),
    fun hG t ht k hk => (hG t ht k hk).trans (h t ht k hk).symm⟩ fun _ => rfl

/-- `regBound` is monotone in `C₁`. -/
theorem regBound_mono_C₁ (P : WTParams) {C C' : ℝ} (h0 : 0 ≤ C) (h : C ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L)
    (n g : ℕ) : regBound { P with C₁ := C, C₂ := C' } n g ≤ regBound P n g := by
  unfold regBound
  refine ENNReal.ofReal_le_ofReal ?_
  have hL' : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g) := Real.rpow_nonneg hL _
  change C * (C * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g) ≤
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)
  have hC1 : 0 ≤ P.C₁ := h0.trans h
  gcongr

end WaveTurbulence.Flower.ProtPin
