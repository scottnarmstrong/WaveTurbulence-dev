/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBZ2
public import WaveTurbulence.Foundations.Flower.MkSlotsI.CentreForm

/-! # B3s-HELPER7 (WP10): the centre-indexed relaxed pinned VINE-B♯ — the outer slot swap at a centre assignment

Setting of `hasSum_skelValWZRL_outerValMμD` (VBZ2), but the outer slot superpositions are only given on the slot
momenta the skeleton value consumes: `fam₀` on the non-centred slots (at the consumed momenta, `hcons`, `hexp₀`) and the
centre-indexed chain pieces `famC c y` on the centred slots (on the node ball of `y`, `hexpC`). For a centre assignment
`X` the skeleton weight `Zs · chiX X ∘ resDec` localizes the centred slot momenta in the node balls of `X`, so the outer
slot kernels may be swapped for the superposition values of `famX fam₀ famC X` (α's `MkSlots.capSwap` pattern):

* `famVal`, `hasSum_famVal`: the value of a slot superposition;
* **`swapFs Φ hS hSb Fs fam`**: `famVal fam s'` on the outer slots `Φ.iota s'`, `Fs` elsewhere; it leaves the regional
  products, the regional bound (`swapRB`) and the unit kernels (`unitKernelMGW_swapFs`) unchanged (the unit regions
  contain no outer slot, `SpliceShape.iota_mem_outer`);
* `hasSum_famX_of_not`, `hasSum_famX_centred`: the superposition of `famX` is `fam₀`'s off the centred slots and the
  centre-`X c` piece on the centred slot of `c`;
* `chiXR` (the real node partition, `chiX = chiXR`), `hasSum_chiXR`, `chiXR_le_one`,
  `norm_sub_le_one_of_chiX_ne_zero`;
* **`skelValWZRL_swapFsX`**: at the weight `Zs · chiX X ∘ resDec` the swap does not change the relaxed pinned skeleton
  value;
* **`hasSum_modes_centred`**: the per-`X` mode form (VBZ2 for `swapFs … (famX fam₀ famC X)`, weight `Zw · chiX X`),
  with the ORIGINAL unit kernels `unitKernelMGW … Fs …`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsI
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW RegMeasW starProdGW unitKernelMGW clLocalSummandGW
  clLocalStarProductGW topW)
open WaveTurbulence.Flower.MkSlotsB

variable {w d : ℕ}

/-! ## The value of a slot superposition -/

section FamVal
variable {G : Garden w}

/-- The value of the superposition of the slot family `fam` at the slot `s`. -/
def famVal (fam : SlotFam G d) (s : ReplacementSlot G) (ts : Fin 2 → ℝ) (x : Mom d) : ℂ :=
  ∑' l, (fam.w s l : ℂ) * fam.a s l x * fsPhase (fam.m s l) ts

theorem norm_famTerm_le (fam : SlotFam G d) (s : ReplacementSlot G) (ts : Fin 2 → ℝ) (x : Mom d) (l : fam.Λ s) :
    ‖(fam.w s l : ℂ) * fam.a s l x * fsPhase (fam.m s l) ts‖ ≤ fam.w s l := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (fam.w_nn s l), fsPhase_norm, mul_one]
  exact mul_le_of_le_one_right (fam.w_nn s l) (fam.a_one s l x)

/-- The superposition converges (absolutely) to its value. -/
theorem hasSum_famVal (fam : SlotFam G d) (s : ReplacementSlot G) (ts : Fin 2 → ℝ) (x : Mom d) :
    HasSum (fun l => (fam.w s l : ℂ) * fam.a s l x * fsPhase (fam.m s l) ts) (famVal fam s ts x) :=
  (Summable.of_norm_bounded (fam.w_sum s) (norm_famTerm_le fam s ts x)).hasSum

end FamVal

/-! ## The swapped slot family -/

section Swap
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)

open scoped Classical in
/-- **The swapped slot family**: the superposition value `famVal fam s'` on the outer slot `Φ.iota s'`, the slot
family `Fs` on the other (unit-internal) slots; the top weights are those of `Fs`. -/
def swapFs (Fs : SlotFamW S d) (fam : SlotFam Gsb d) : SlotFamW S d :=
  ⟨fun sl => if h : ∃ s', Φ.iota hS hSb s' = sl then famVal fam (Classical.choose h) else Fs.fs sl, Fs.tw⟩

theorem swapFs_tw (Fs : SlotFamW S d) (fam : SlotFam Gsb d) : (swapFs Φ hS hSb Fs fam).tw = Fs.tw := by
  unfold swapFs
  rfl

theorem swapFs_iota (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (s' : ReplacementSlot Gsb) :
    (swapFs Φ hS hSb Fs fam).fs (Φ.iota hS hSb s') = famVal fam s' := by
  classical
  unfold swapFs
  dsimp only
  have h : ∃ s'', Φ.iota hS hSb s'' = Φ.iota hS hSb s' := ⟨s', rfl⟩
  rw [dite_eq_left h, Φ.iota_inj hS hSb (Classical.choose_spec h)]

theorem swapFs_not_iota (Fs : SlotFamW S d) (fam : SlotFam Gsb d) {sl : ReplacementSlot S}
    (hs : ¬ ∃ s', Φ.iota hS hSb s' = sl) : (swapFs Φ hS hSb Fs fam).fs sl = Fs.fs sl := by
  classical
  unfold swapFs
  dsimp only
  rw [dite_eq_right hs]

theorem swapFs_reg (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (j : J) {sl : ReplacementSlot S}
    (hs : sl ∈ regSlots blk hS j) : (swapFs Φ hS hSb Fs fam).fs sl = Fs.fs sl := by
  classical
  refine swapFs_not_iota Φ hS hSb Fs fam ?_
  rintro ⟨s', hs'⟩
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j hs

theorem swapFs_pair (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (j : J) {p : SourcePair S}
    (hp : p ∈ clRegionalPairs hS (blk j).atoms) : (swapFs Φ hS hSb Fs fam).fs (.inl p) = Fs.fs (.inl p) := by
  refine swapFs_reg Φ hS hSb Fs fam j ((mem_regSlots_inl hS j p).mpr ?_)
  classical
  exact (Finset.mem_filter.mp hp).2

theorem swapFs_erase (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (j : J) {v : GBranch S.tree}
    (hv : v ∈ (blk j).atoms.erase (blk j).upper) : (swapFs Φ hS hSb Fs fam).fs (.inr v) = Fs.fs (.inr v) :=
  swapFs_reg Φ hS hSb Fs fam j ((mem_regSlots_inr hS j v).mpr
    (VineB.mem_inter.mpr ⟨(Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1⟩))

/-- The regional star products of the units do not see the swap. -/
theorem starProdGW_swapFs (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (L : ℝ) (base : Mom d) (j : J) (top : ℝ)
    (x : GNode S.tree → (Fin d → ℤ)) (u : GBranch S.tree → ℝ) :
    starProdGW hS (swapFs Φ hS hSb Fs fam) L base (blk j).atoms (blk j).upper top x u =
      starProdGW hS Fs L base (blk j).atoms (blk j).upper top x u := by
  unfold starProdGW
  rw [swapFs_tw]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_)
    (Finset.prod_congr rfl fun v hv => ?_)) rfl
  · rw [swapFs_pair Φ hS hSb Fs fam j hp]
  · rw [swapFs_erase Φ hS hSb Fs fam j hv]

theorem regMeasW_swapFs (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (L : ℝ) (base : Mom d) (j : J)
    (h : RegMeasW hS Fs L base (blk j).atoms (blk j).upper) :
    RegMeasW hS (swapFs Φ hS hSb Fs fam) L base (blk j).atoms (blk j).upper :=
  ⟨fun p hp n => by rw [swapFs_pair Φ hS hSb Fs fam j hp]; exact h.1 p hp n,
    fun v hv n => by rw [swapFs_erase Φ hS hSb Fs fam j hv]; exact h.2 v hv n⟩

/-- **The regional bound survives the swap** (same `lb`, `lbC`; α's `MkSlots.RegBound.capSwap` pattern). -/
def swapRB {Fs : SlotFamW S d} (fam : SlotFam Gsb d) {L : ℝ} {base : Mom d} (RB : RegBoundW blk hS Fs L base) :
    RegBoundW blk hS (swapFs Φ hS hSb Fs fam) L base where
  lb := RB.lb
  lbC := RB.lbC
  nonneg := RB.nonneg
  norm_le := fun j x top u => by
    rw [starProdGW_swapFs Φ hS hSb Fs fam L base j top x u]
    exact RB.norm_le j x top u
  summable := RB.summable
  tsum_le := RB.tsum_le
  meas := fun j => regMeasW_swapFs Φ hS hSb Fs fam L base j (RB.meas j)

theorem swapRB_lb {Fs : SlotFamW S d} (fam : SlotFam Gsb d) {L : ℝ} {base : Mom d}
    (RB : RegBoundW blk hS Fs L base) : (swapRB Φ hS hSb fam RB).lb = RB.lb := by
  unfold swapRB
  rfl

/-- **The unit kernels do not see the swap.** -/
theorem unitKernelMGW_swapFs (D : ReconstructionData S) (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (L γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) (base : Mom d) :
    unitKernelMGW blk D hS (swapFs Φ hS hSb Fs fam) L γ δ layer base = unitKernelMGW blk D hS Fs L γ δ layer base := by
  unfold unitKernelMGW clLocalSummandGW clLocalStarProductGW
  simp only [starProdGW_swapFs]

theorem topW_swapFs (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (L : ℝ) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) : topW blk (swapFs Φ hS hSb Fs fam) L base x = topW blk Fs L base x := by
  unfold topW
  rw [swapFs_tw]

/-- **Congruence of the weighted skeleton summand under the swap**: only the slot values at pinned times of the core
domain, at decorations of non-zero weight, matter. -/
theorem skelTermWZ_swapFs (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (A : Set (GBranch S.tree → ℝ))
    (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0)
    (h : Zs κ ≠ 0 → ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s',
      famVal fam s' (slotTs hS tt τ (Φ.iota hS hSb s')) (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))) =
        Fs.fs (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s'))
          (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s'))))) :
    skelTermWZ blk hS L γ δ base roots tt Zs (swapFs Φ hS hSb Fs fam) A fixS κ =
      skelTermWZ blk hS L γ δ base roots tt Zs Fs A fixS κ := by
  unfold skelTermWZ
  by_cases hz : Zs κ = 0
  · rw [hz, zero_mul, zero_mul]
  refine congrArg (fun I => Zs κ * ((epsDec S κ.1 : ℂ) * I))
    (integral_congr_ae ((ae_pinnedAt fixS).mono fun τ hτ => ?_))
  by_cases hA : τ ∈ A
  · simp only [Set.indicator_of_mem hA]
    have hprod : ∏ s, (swapFs Φ hS hSb Fs fam).fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s))) =
        ∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s))) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      by_cases hs : ∃ s', Φ.iota hS hSb s' = s
      · obtain ⟨s', rfl⟩ := hs
        rw [swapFs_iota]
        exact h hz τ hτ hA s'
      · rw [swapFs_not_iota Φ hS hSb Fs fam hs]
    rw [hprod, topW_swapFs]
  · simp only [Set.indicator_of_notMem hA]

end Swap

/-! ## The centre-indexed family -/

section FamX
variable {G : Garden w} (fam₀ : SlotFam G d) (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d)
  (X : CentredSlot G → (Fin d → ℤ))

open scoped Classical in
theorem famX_w_inl (s : ReplacementSlot G) (l : fam₀.Λ s) :
    (famX fam₀ famC X).w s (Sum.inl l) = if IsCentred s then 0 else fam₀.w s l := rfl

theorem famX_a_inl (s : ReplacementSlot G) (l : fam₀.Λ s) :
    (famX fam₀ famC X).a s (Sum.inl l) = fam₀.a s l := rfl

theorem famX_m_inl (s : ReplacementSlot G) (l : fam₀.Λ s) :
    (famX fam₀ famC X).m s (Sum.inl l) = fam₀.m s l := rfl

/-- Off the centred slots the piece is empty. -/
theorem isEmpty_pieceAtX {s : ReplacementSlot G} (hs : ¬ IsCentred s) : IsEmpty (pieceAtX famC X s).Λ := by
  rcases s with q | c
  · exact inferInstanceAs (IsEmpty Empty)
  · have hc : ¬ c.1.2 ≠ [] := hs
    rw [pieceAtX, dite_eq_right hc]
    exact inferInstanceAs (IsEmpty Empty)

/-- On the centred slot of `c` the piece is the centre-`X c` chain piece. -/
theorem pieceAtX_centred (c : CentredSlot G) : pieceAtX famC X (.inr c.1) = famC c (X c) := by
  rw [pieceAtX, dite_eq_left c.2]

/-- Off the centred slots the superposition of `famX` is that of `fam₀`. -/
theorem hasSum_famX_of_not {s : ReplacementSlot G} (hs : ¬ IsCentred s) (ts : Fin 2 → ℝ) (x : Mom d) {v : ℂ}
    (h : HasSum (fun l => (fam₀.w s l : ℂ) * fam₀.a s l x * fsPhase (fam₀.m s l) ts) v) :
    HasSum (fun l => ((famX fam₀ famC X).w s l : ℂ) * (famX fam₀ famC X).a s l x *
      fsPhase ((famX fam₀ famC X).m s l) ts) v := by
  have := isEmpty_pieceAtX famC X hs
  let f : fam₀.Λ s ⊕ (pieceAtX famC X s).Λ → ℂ := fun l => ((famX fam₀ famC X).w s l : ℂ) *
    (famX fam₀ famC X).a s l x * fsPhase ((famX fam₀ famC X).m s l) ts
  have h1 : HasSum (f ∘ Sum.inl) v := by
    refine h.congr_fun fun l => ?_
    simp only [f, Function.comp_apply, famX_w_inl, famX_a_inl, famX_m_inl, hs, ↓reduceIte]
  have h0 : HasSum (f ∘ Sum.inr) 0 := hasSum_empty
  have := h1.sum h0
  rw [add_zero] at this
  exact this

/-- On the centred slot of `c` the superposition of `famX` is that of the centre-`X c` chain piece. -/
theorem hasSum_famX_centred (c : CentredSlot G) (ts : Fin 2 → ℝ) (x : Mom d) {v : ℂ}
    (h : HasSum (fun l => ((famC c (X c)).w l : ℂ) * (famC c (X c)).a l x * fsPhase ((famC c (X c)).m l) ts) v) :
    HasSum (fun l => ((famX fam₀ famC X).w (.inr c.1) l : ℂ) * (famX fam₀ famC X).a (.inr c.1) l x *
      fsPhase ((famX fam₀ famC X).m (.inr c.1) l) ts) v := by
  have hc : IsCentred (Sum.inr c.1 : ReplacementSlot G) := c.2
  let f : fam₀.Λ (.inr c.1) ⊕ (pieceAtX famC X (.inr c.1)).Λ → ℂ := fun l =>
    ((famX fam₀ famC X).w (.inr c.1) l : ℂ) * (famX fam₀ famC X).a (.inr c.1) l x *
      fsPhase ((famX fam₀ famC X).m (.inr c.1) l) ts
  have h0 : HasSum (f ∘ Sum.inl) 0 := by
    have e : f ∘ Sum.inl = fun _ => 0 := by
      funext l
      simp only [f, Function.comp_apply, famX_w_inl, hc, ↓reduceIte, Complex.ofReal_zero, zero_mul]
    rw [e]
    exact hasSum_zero
  have key : ∀ P : ChainPiece d, P = famC c (X c) →
      HasSum (fun l : P.Λ => (P.w l : ℂ) * P.a l x * fsPhase (P.m l) ts) v := by
    rintro P rfl
    exact h
  have h1 : HasSum (f ∘ Sum.inr) v := key _ (pieceAtX_centred famC X c)
  have := h0.sum h1
  rw [zero_add] at this
  exact this

end FamX

/-! ## The real node partition -/

section Chi
variable {G : Garden w}

/-- **The real node partition** at the centred slots (`chiX = (chiXR : ℂ)`, `chiX_eq`). -/
def chiXR (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : ℝ :=
  ∏ c : CentredSlot G, chi d (X c) (base + latticePoint L (z.1 c.1.toNode))

theorem chiX_eq (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : chiX L base X z = (chiXR L base X z : ℂ) := by
  unfold chiX chiXR chiC
  rw [Complex.ofReal_prod]

theorem chiXR_nonneg (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : 0 ≤ chiXR L base X z :=
  Finset.prod_nonneg fun _ _ => chi_nonneg d _ _

/-- The real partition of unity over the centre assignments. -/
theorem hasSum_chiXR (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0) :
    HasSum (fun X : CentredSlot G → (Fin d → ℤ) => chiXR L base X z) 1 := by
  have h := hasSum_chiX L base z
  simp only [chiX_eq] at h
  rw [← Complex.ofReal_one] at h
  exact Complex.hasSum_ofReal.mp h

theorem chiXR_le_one (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : chiXR L base X z ≤ 1 :=
  le_hasSum (hasSum_chiXR L base z) X fun Y _ => chiXR_nonneg L base Y z

theorem norm_chiX (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : ‖chiX L base X z‖ = chiXR L base X z := by
  rw [chiX_eq, Complex.norm_real, Real.norm_of_nonneg (chiXR_nonneg L base X z)]

/-- A complex weight of norm `≤ 1` times the node partition has norm `≤ 1`. -/
theorem norm_mul_chiX_le_one (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ))
    {roots : Fin w → (Fin d → ℤ)} (Zw : GenDecoration G d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (z : GenDecoration G d roots 0) : ‖Zw z * chiX L base X z‖ ≤ 1 := by
  rw [norm_mul, norm_chiX]
  calc ‖Zw z‖ * chiXR L base X z ≤ 1 * 1 :=
        mul_le_mul (hZw z) (chiXR_le_one L base X z) (chiXR_nonneg L base X z) zero_le_one
    _ = 1 := one_mul 1

/-- Where the node partition does not vanish, every centred slot momentum lies in the node ball of its centre. -/
theorem norm_sub_le_one_of_chiX_ne_zero {L : ℝ} {base : Mom d} {X : CentredSlot G → (Fin d → ℤ)}
    {roots : Fin w → (Fin d → ℤ)} {z : GenDecoration G d roots 0} (h : chiX L base X z ≠ 0) (c : CentredSlot G) :
    ‖base + latticePoint L (z.1 c.1.toNode) - latPt d (X c)‖ ≤ 1 := by
  rw [chiX_eq, Complex.ofReal_ne_zero] at h
  exact norm_sub_le_one_of_chi_ne_zero (Finset.prod_ne_zero_iff.mp h c (Finset.mem_univ c))

end Chi

/-! ## The agreement on the consumed momenta -/

section Agree
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- **The agreement hypothesis at the centre assignment `X`**: at every consumed slot momentum of a decoration of
non-zero weight `chiX X`, on the slot boxes, the superposition of `famX fam₀ famC X` is the outer slot kernel (all that
the swap uses; it follows from `hcons`, `hexp₀`, `hexpC`, `centreAgree_of`). -/
def CentreAgree (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (hd : Disj blk) (L : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (Fs : SlotFamW S d) (fam₀ : SlotFam Gsb d)
    (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (X : CentredSlot Gsb → (Fin d → ℤ)) : Prop :=
  ∀ κ : GenDecoration S d roots 0, chiX L base X (Φ.resDec hS hd κ) ≠ 0 → ∀ (s' : ReplacementSlot Gsb),
    ∀ ts ∈ Box s', famVal (famX fam₀ famC X) s' ts (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))) =
      Fs.fs (Φ.iota hS hSb s') ts (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s'))))

end Agree

/-! ## The swap at a centre assignment -/

section SwapX
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- The swap at the centre assignment `X` under the agreement hypothesis (summand). -/
theorem skelTermWZ_swapFsX_agree (hd : Disj blk) (hSb : Gsb.IsPlain) (γ δ : ℝ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (Zs : GenDecoration S d roots 0 → ℂ)
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (X : CentredSlot Gsb → (Fin d → ℤ)) (hA : CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X)
    (κ : GenDecoration S d roots 0) :
    skelTermWZ blk hS L γ δ base roots tt (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ))
        (swapFs Φ hS hSb Fs (famX fam₀ famC X)) A fixS κ =
      skelTermWZ blk hS L γ δ base roots tt (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs A fixS κ :=
  skelTermWZ_swapFs Φ hS hSb L γ δ base tt _ Fs _ A fixS κ fun hz τ hτ hA' s' =>
    hA κ (right_ne_zero_of_mul hz) s' _ (hbox τ hτ hA' s')

/-- The swap at the centre assignment `X` under the agreement hypothesis (relaxed pinned skeleton value). -/
theorem skelValWZRL_swapFsX_agree (hd : Disj blk) (hSb : Gsb.IsPlain) (γ δ : ℝ) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ)
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (fixS lbS : GBranch S.tree → Option ℝ)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (X : CentredSlot Gsb → (Fin d → ℤ)) (hA : CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X) :
    skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ))
        (swapFs Φ hS hSb Fs (famX fam₀ famC X)) fixS lbS =
      skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs
        fixS lbS := by
  unfold skelValWZRL skelValWZ
  rw [tsum_congr fun κ => skelTermWZ_swapFsX_agree Φ hd hSb γ δ tt Zs fam₀ famC Box _ fixS hbox X hA κ]

/-- The per-centre mode form under the agreement hypothesis. -/
theorem hasSum_modes_centred_agree (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (X : CentredSlot Gsb → (Fin d → ℤ)) (hA : CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X) :
    HasSum (fun ξ : ∀ s, (famX fam₀ famC X).Λ s => ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs
        fixS lbS) := by
  have h := hasSum_skelValWZRL_outerValMμD Φ (swapRB Φ hS hSb (famX fam₀ famC X) RB) hd hSb hL0 γ δ D layer tt
    (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) (fun z => Zw z * chiX L base X z)
    (norm_mul_chiX_le_one L base X Zw hZw) (fun κ => by simp only [hZ κ]) (famX fam₀ famC X) Box
    (fun s' ts _ x => by rw [swapFs_iota]; exact hasSum_famVal _ s' ts x) fixS lbS hU hlbU hP hbox
  rw [unitKernelMGW_swapFs, skelValWZRL_swapFsX_agree Φ hd hSb γ δ D layer tt Zs fam₀ famC Box fixS lbS hbox X
    hA] at h
  exact h

end SwapX

end WaveTurbulence.Flower.MkSlotsI
