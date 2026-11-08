/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp
public import WaveTurbulence.Foundations.Flower.MkSlots.PVBModes

/-! # B3s MK-SLOTS (integration): cap slots in the pinned skeleton value and the combined outer slot family

**Cap swap.** A cap pair slot `.inl q` (`IsCapPair`) is evaluated by the pinned skeleton value `skelValF` at ONE
momentum only: the slot momentum is the label of the first leaf, which equals the label of the cap root (paired leaves
carry equal labels, a cap tree is a single leaf whose root label is prescribed), `capPair_label`. So the slot family may
be changed on cap slots away from that momentum (`capSwap`, `skelValF_capSwap`). Cap pairs are never regional pairs of a
unit (a regional pair has both leaves off the roots, `capPair_not_regional`), so the unit kernels and the regional
bounds do not see the change (`starProdG_capSwap`, `unitKernelMG_capSwap`, `RegBound.capSwap`).

**Combined family.** `combineFam fam₀ isCap pc`: the outer slot family that is B3's family `fam₀` on the slots with
`¬ isCap s` and the single-slot superposition `pc s` (`SlotPiece`, e.g. from `CapSlotObligation`) on the slots with
`isCap s`; its modes are `fam₀.Λ s ⊕ (pc s).Λ` with the weights of the unused side set to `0`
(`hasSum_combineFam_of_not`, `hasSum_combineFam_of_cap`, `mass_combineFam_le`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.Stage1WVine WaveTurbulence.VineB WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-! ## The cap swap on the skeleton -/

section CapSwap
variable {S : Garden w} (hS : S.IsPlain) (J : Finset (Fin w))

/-- The slot family `Fs` with the cap pair slots replaced by `Fcap`. -/
def capSwap (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl q => if IsCapPair S hS J q then Fcap q else Fs (.inl q)
  | .inr b => Fs (.inr b)

/-- A leaf of a single-leaf tree is its root. -/
theorem leaf_path_nil_of_tree_leaf {ℓ : GLeaf S.tree} (h : S.tree ℓ.1.1 = TTree.leaf) : ℓ.1.2 = [] := by
  have hl := ℓ.2
  rw [h] at hl
  simpa [TTree.leaves] using hl

/-- One leaf of a cap pair has the empty path (it is the cap root). -/
theorem capPair_path_nil (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf) {q : SourcePair S} (hq : IsCapPair S hS J q) :
    (q.firstLeaf hS).1.2 = [] ∨ (q.secondLeaf hS).1.2 = [] := by
  rcases hq with h | h
  · exact Or.inl (leaf_path_nil_of_tree_leaf (hcapS _ h))
  · exact Or.inr (leaf_path_nil_of_tree_leaf (hcapS _ h))

/-- **Cap pairs are never regional pairs** of a unit (a regional pair has both leaves off the roots). -/
theorem capPair_not_regional (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf) {q : SourcePair S}
    (hq : IsCapPair S hS J q) (U : Finset (GBranch S.tree)) : q ∉ clRegionalPairs hS U := by
  intro hmem
  have hint := (Finset.mem_filter.mp hmem).2
  obtain ⟨_, hn, hp, _⟩ := hint
  have hpair : S.pair (q.firstLeaf hS) = q.secondLeaf hS := VineEstS4.pair_first_eq_second hS q
  rcases capPair_path_nil hS J hcapS hq with h | h
  · exact hn h
  · exact hp (by rw [hpair]; exact h)

theorem starProdG_capSwap (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) (U : Finset (GBranch S.tree)) (a : GBranch S.tree) (top : ℝ)
    (x : GNode S.tree → (Fin d → ℤ)) (u : GBranch S.tree → ℝ) :
    starProdG hS (capSwap hS J Fs Fcap) L base U a top x u = starProdG hS Fs L base U a top x u := by
  unfold starProdG
  congr 1
  refine Finset.prod_congr rfl fun q hq => ?_
  show (if IsCapPair S hS J q then Fcap q else Fs (.inl q)) _ _ = _
  rw [if_neg (fun h => capPair_not_regional hS J hcapS h U hq)]

theorem regMeas_capSwap (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) (U : Finset (GBranch S.tree)) (a : GBranch S.tree) (h : RegMeas hS Fs L base U a) :
    RegMeas hS (capSwap hS J Fs Fcap) L base U a := by
  refine ⟨fun q hq n => ?_, fun v hv n => h.2 v hv n⟩
  have he : capSwap hS J Fs Fcap (.inl q) = Fs (.inl q) := by
    show (if IsCapPair S hS J q then Fcap q else Fs (.inl q)) = _
    rw [if_neg (fun h' => capPair_not_regional hS J hcapS h' U hq)]
  rw [he]
  exact h.1 q hq n

variable {J' : Type} [Fintype J'] [DecidableEq J'] {blk : J' → CLBlock S}

/-- A regional bound survives the cap swap. -/
def RegBound.capSwap (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf)
    {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ)
    {L : ℝ} {base : Mom d} (RB : RegBound blk hS Fs L base) :
    RegBound blk hS (MkSlots.capSwap hS J Fs Fcap) L base where
  lb := RB.lb
  lbC := RB.lbC
  nonneg := RB.nonneg
  norm_le := fun j x top u => by
    rw [starProdG_capSwap hS J hcapS]
    exact RB.norm_le j x top u
  summable := RB.summable
  tsum_le := RB.tsum_le
  meas := fun j => regMeas_capSwap hS J hcapS Fs Fcap L base _ _ (RB.meas j)

theorem unitKernelMG_capSwap (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf) (D : ReconstructionData S)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ)
    (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (base : Mom d) :
    unitKernelMG blk D hS (capSwap hS J Fs Fcap) L γ δ layer base = unitKernelMG blk D hS Fs L γ δ layer base := by
  unfold unitKernelMG clLocalSummandG clLocalStarProductG
  simp only [starProdG_capSwap hS J hcapS]

/-- **The label of a cap slot** is the label of its cap root. -/
theorem capPair_label (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf) {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration S d roots 0) {q : SourcePair S} (hq : IsCapPair S hS J q) :
    κ.1 (slotNode hS (.inl q)) = roots (capTreeOf S hS J q) := by
  have hpair : S.pair (q.firstLeaf hS) = q.secondLeaf hS := VineEstS4.pair_first_eq_second hS q
  show κ.1 (q.firstLeaf hS).toNode = _
  unfold capTreeOf
  by_cases h1 : (q.firstLeaf hS).1.1 ∈ J
  · rw [if_pos h1]
    have hp := leaf_path_nil_of_tree_leaf (hcapS _ h1)
    have hroot : (q.firstLeaf hS).toNode = GNode.root S.tree (q.firstLeaf hS).1.1 :=
      Subtype.ext (Prod.ext rfl hp)
    rw [hroot]
    exact κ.2.2.1 _
  · rw [if_neg h1]
    have h2 : (q.secondLeaf hS).1.1 ∈ J := hq.resolve_left h1
    have hp := leaf_path_nil_of_tree_leaf (hcapS _ h2)
    have hroot : (q.secondLeaf hS).toNode = GNode.root S.tree (q.secondLeaf hS).1.1 :=
      Subtype.ext (Prod.ext rfl hp)
    rw [κ.2.1.2 (q.firstLeaf hS), hpair, hroot]
    exact κ.2.2.1 _

/-- **Congruence of the pinned skeleton value** in the slot family: only the values at the slot times of the core
domain and at the slot momenta of selected decorations matter. -/
theorem skelValF_congr (D : ReconstructionData S) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs Fs' : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (fixS : GBranch S.tree → Option ℝ)
    (h : ∀ κ : GenDecoration S d roots 0, selSk κ →
      ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s,
        Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s))) =
          Fs' s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) :
    skelValF D hS L γ δ base roots tt layer selSk Fs fixS = skelValF D hS L γ δ base roots tt layer selSk Fs' fixS := by
  unfold skelValF
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    by_cases hτ : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
    · simp only [Set.indicator_of_mem hτ]
      congr 1
      exact Finset.prod_congr rfl fun s _ => h κ hκ τ hτ s
    · simp only [Set.indicator_of_notMem hτ]
  · simp only [hκ, ite_false]

/-- **The cap swap does not change the pinned skeleton value**, provided the swapped cap functions agree with the old
ones at the cap momentum on the slot boxes, and the slot times of the core domain lie in the boxes. -/
theorem skelValF_capSwap (hcapS : ∀ j ∈ J, S.tree j = TTree.leaf) (D : ReconstructionData S) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ) (fixS : GBranch S.tree → Option ℝ)
    (Box : ReplacementSlot S → Set (Fin 2 → ℝ))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s, slotTs hS tt τ s ∈ Box s)
    (hcap : ∀ q, IsCapPair S hS J q → ∀ ts ∈ Box (.inl q),
      Fcap q ts (base + latticePoint L (roots (capTreeOf S hS J q))) =
        Fs (.inl q) ts (base + latticePoint L (roots (capTreeOf S hS J q)))) :
    skelValF D hS L γ δ base roots tt layer selSk Fs fixS =
      skelValF D hS L γ δ base roots tt layer selSk (capSwap hS J Fs Fcap) fixS := by
  refine skelValF_congr hS D L γ δ base roots tt layer selSk _ _ fixS fun κ _ τ hτ s => ?_
  rcases s with q | b
  · show _ = (if IsCapPair S hS J q then Fcap q else Fs (.inl q)) _ _
    by_cases hq : IsCapPair S hS J q
    · rw [if_pos hq, capPair_label hS J hcapS κ hq]
      exact (hcap q hq _ (hbox τ hτ (.inl q))).symm
    · rw [if_neg hq]
  · rfl

end CapSwap

/-! ## The combined outer slot family -/

/-- A superposition on one slot: countable modes, nonnegative summable weights, amplitudes bounded by `1` with
`SNorm (30 d) 0 ≤ 1`, centred within distance `1` of a lattice point (`SlotFam`'s per-slot axioms). -/
structure SlotPiece (d : ℕ) where
  Λ : Type
  cnt : Countable Λ
  w : Λ → ℝ
  m : Λ → Fin 2 → ℤ
  n : Λ → Fin d → ℤ
  a : Λ → Mom d → ℂ
  w_nn : ∀ l, 0 ≤ w l
  w_sum : Summable w
  a_one : ∀ l k, ‖a l k‖ ≤ 1
  a_snorm : ∀ l, SNorm (30 * d) 0 (a l) ≤ 1
  a_supp : ∀ l k, a l k ≠ 0 → ‖k - latPt d (n l)‖ ≤ 1

/-- The empty superposition. -/
def SlotPiece.empty (d : ℕ) : SlotPiece d where
  Λ := Empty
  cnt := inferInstance
  w := Empty.elim
  m := Empty.elim
  n := Empty.elim
  a := Empty.elim
  w_nn := fun l => l.elim
  w_sum := summable_empty
  a_one := fun l => l.elim
  a_snorm := fun l => l.elim
  a_supp := fun l => l.elim

/-- The value of a superposition. -/
def SlotPiece.val (pc : SlotPiece d) (ts : Fin 2 → ℝ) (x : Mom d) : ℂ :=
  ∑' l, (pc.w l : ℂ) * pc.a l x * fsPhase (pc.m l) ts

theorem SlotPiece.norm_term_le (pc : SlotPiece d) (ts : Fin 2 → ℝ) (x : Mom d) (l : pc.Λ) :
    ‖(pc.w l : ℂ) * pc.a l x * fsPhase (pc.m l) ts‖ ≤ pc.w l := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pc.w_nn l)]
  have h1 := pc.a_one l x
  have h2 : ‖fsPhase (pc.m l) ts‖ = 1 := by
    unfold fsPhase
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h2, mul_one]
  exact mul_le_of_le_one_right (pc.w_nn l) h1

theorem SlotPiece.hasSum (pc : SlotPiece d) (ts : Fin 2 → ℝ) (x : Mom d) :
    HasSum (fun l => (pc.w l : ℂ) * pc.a l x * fsPhase (pc.m l) ts) (pc.val ts x) :=
  (Summable.of_norm_bounded pc.w_sum (pc.norm_term_le ts x)).hasSum

variable {G : Garden w}

/-- **The combined outer slot family.** -/
def combineFam (fam₀ : SlotFam G d) (isCap : ReplacementSlot G → Prop) (pc : ReplacementSlot G → SlotPiece d) :
    SlotFam G d where
  Λ s := fam₀.Λ s ⊕ (pc s).Λ
  cnt s := by
    haveI := fam₀.cnt s
    haveI := (pc s).cnt
    infer_instance
  w s := Sum.elim (fun l => if isCap s then 0 else fam₀.w s l) (fun l => if isCap s then (pc s).w l else 0)
  m s := Sum.elim (fam₀.m s) (pc s).m
  n s := Sum.elim (fam₀.n s) (pc s).n
  a s := Sum.elim (fam₀.a s) (pc s).a
  w_nn s l := by
    rcases l with l | l
    · show 0 ≤ (if isCap s then 0 else fam₀.w s l)
      split_ifs
      · exact le_rfl
      · exact fam₀.w_nn s l
    · show 0 ≤ (if isCap s then (pc s).w l else 0)
      split_ifs
      · exact (pc s).w_nn l
      · exact le_rfl
  w_sum s := by
    refine Summable.sum _ ?_ ?_
    · by_cases h : isCap s
      · simp only [Function.comp_def, Sum.elim_inl, h, ite_true]
        exact summable_zero
      · simp only [Function.comp_def, Sum.elim_inl, h, ite_false]
        exact fam₀.w_sum s
    · by_cases h : isCap s
      · simp only [Function.comp_def, Sum.elim_inr, h, ite_true]
        exact (pc s).w_sum
      · simp only [Function.comp_def, Sum.elim_inr, h, ite_false]
        exact summable_zero
  a_one s l k := by
    rcases l with l | l
    · exact fam₀.a_one s l k
    · exact (pc s).a_one l k
  a_snorm s l := by
    rcases l with l | l
    · exact fam₀.a_snorm s l
    · exact (pc s).a_snorm l
  a_supp q l k hk := by
    rcases l with l | l
    · exact fam₀.a_supp q l k hk
    · exact (pc (Sum.inl q)).a_supp l k hk

section Combine
variable (fam₀ : SlotFam G d) (isCap : ReplacementSlot G → Prop) (pc : ReplacementSlot G → SlotPiece d)
  (s : ReplacementSlot G)

theorem combineFam_w_inl (l : fam₀.Λ s) :
    (combineFam fam₀ isCap pc).w s (Sum.inl l) = if isCap s then 0 else fam₀.w s l := rfl
theorem combineFam_w_inr (l : (pc s).Λ) :
    (combineFam fam₀ isCap pc).w s (Sum.inr l) = if isCap s then (pc s).w l else 0 := rfl
theorem combineFam_a_inl (l : fam₀.Λ s) : (combineFam fam₀ isCap pc).a s (Sum.inl l) = fam₀.a s l := rfl
theorem combineFam_a_inr (l : (pc s).Λ) : (combineFam fam₀ isCap pc).a s (Sum.inr l) = (pc s).a l := rfl
theorem combineFam_m_inl (l : fam₀.Λ s) : (combineFam fam₀ isCap pc).m s (Sum.inl l) = fam₀.m s l := rfl
theorem combineFam_m_inr (l : (pc s).Λ) : (combineFam fam₀ isCap pc).m s (Sum.inr l) = (pc s).m l := rfl

/-- The combined term at a mode. -/
def combTerm (ts : Fin 2 → ℝ) (x : Mom d) (l : fam₀.Λ s ⊕ (pc s).Λ) : ℂ :=
  ((combineFam fam₀ isCap pc).w s l : ℂ) * (combineFam fam₀ isCap pc).a s l x *
    fsPhase ((combineFam fam₀ isCap pc).m s l) ts

theorem combTerm_inl (ts : Fin 2 → ℝ) (x : Mom d) (l : fam₀.Λ s) :
    combTerm fam₀ isCap pc s ts x (Sum.inl l) =
      ((if isCap s then 0 else fam₀.w s l : ℝ) : ℂ) * fam₀.a s l x * fsPhase (fam₀.m s l) ts := rfl

theorem combTerm_inr (ts : Fin 2 → ℝ) (x : Mom d) (l : (pc s).Λ) :
    combTerm fam₀ isCap pc s ts x (Sum.inr l) =
      ((if isCap s then (pc s).w l else 0 : ℝ) : ℂ) * (pc s).a l x * fsPhase ((pc s).m l) ts := rfl

theorem hasSum_combineFam_of_not (hs : ¬ isCap s) (ts : Fin 2 → ℝ) (x : Mom d)
    {v : ℂ} (h : HasSum (fun l => (fam₀.w s l : ℂ) * fam₀.a s l x * fsPhase (fam₀.m s l) ts) v) :
    HasSum (combTerm fam₀ isCap pc s ts x) v := by
  have h1 : HasSum (combTerm fam₀ isCap pc s ts x ∘ Sum.inl) v := by
    refine h.congr_fun fun l => ?_
    simp only [Function.comp_apply, combTerm_inl, hs, ite_false]
  have h0 : HasSum (combTerm fam₀ isCap pc s ts x ∘ Sum.inr) 0 := by
    have : combTerm fam₀ isCap pc s ts x ∘ Sum.inr = fun _ => 0 := by
      funext l
      simp only [Function.comp_apply, combTerm_inr, hs, ite_false, Complex.ofReal_zero, zero_mul]
    rw [this]
    exact hasSum_zero
  simpa using HasSum.sum h1 h0

theorem hasSum_combineFam_of_cap (hs : isCap s) (ts : Fin 2 → ℝ) (x : Mom d) :
    HasSum (combTerm fam₀ isCap pc s ts x) ((pc s).val ts x) := by
  have h0 : HasSum (combTerm fam₀ isCap pc s ts x ∘ Sum.inl) 0 := by
    have : combTerm fam₀ isCap pc s ts x ∘ Sum.inl = fun _ => 0 := by
      funext l
      simp only [Function.comp_apply, combTerm_inl, hs, ite_true, Complex.ofReal_zero, zero_mul]
    rw [this]
    exact hasSum_zero
  have h1 : HasSum (combTerm fam₀ isCap pc s ts x ∘ Sum.inr) ((pc s).val ts x) := by
    refine ((pc s).hasSum ts x).congr_fun fun l => ?_
    simp only [Function.comp_apply, combTerm_inr, hs, ite_true]
  simpa using HasSum.sum h0 h1

/-- The combined mode mass at a mode. -/
def combMass (θ : ℝ) (l : fam₀.Λ s ⊕ (pc s).Λ) : ℝ≥0∞ :=
  maxBracketPow θ (half ((combineFam fam₀ isCap pc).m s l)) * ENNReal.ofReal ((combineFam fam₀ isCap pc).w s l)

/-- **The mode mass of the combined family**: B3's on the ordinary slots, the piece's on the cap slots. -/
theorem mass_combineFam (θ : ℝ) :
    ∑' l, combMass fam₀ isCap pc s θ l =
      if isCap s then ∑' l, maxBracketPow θ (half ((pc s).m l)) * ENNReal.ofReal ((pc s).w l)
      else ∑' l, maxBracketPow θ (half (fam₀.m s l)) * ENNReal.ofReal (fam₀.w s l) := by
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  by_cases hs : isCap s
  · rw [if_pos hs]
    have h0 : ∀ l : fam₀.Λ s, combMass fam₀ isCap pc s θ (Sum.inl l) = 0 := fun l => by
      simp only [combMass, combineFam_w_inl, hs, ite_true, ENNReal.ofReal_zero, mul_zero]
    simp only [h0, tsum_zero, zero_add]
    refine tsum_congr fun l => ?_
    simp only [combMass, combineFam_w_inr, combineFam_m_inr, hs, ite_true]
  · rw [if_neg hs]
    have h0 : ∀ l : (pc s).Λ, combMass fam₀ isCap pc s θ (Sum.inr l) = 0 := fun l => by
      simp only [combMass, combineFam_w_inr, hs, ite_false, ENNReal.ofReal_zero, mul_zero]
    simp only [h0, tsum_zero, add_zero]
    refine tsum_congr fun l => ?_
    simp only [combMass, combineFam_w_inl, combineFam_m_inl, hs, ite_false]

end Combine

end WaveTurbulence.Flower.MkSlots
