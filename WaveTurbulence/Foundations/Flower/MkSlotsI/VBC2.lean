/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBC1

/-! # B3s-HELPER7 (WP10): the centre-indexed relaxed pinned VINE-B♯ — the majorant and the decoration bound

The partition `Σ_X chiX X = 1` of the skeleton weight needs the decoration sum of the skeleton terms to be absolutely
summable. The slot family `Fs` is only known on the consumed momenta through the centre-indexed superpositions, so the
bound goes through the modes: at a decoration `κ = glue (z, κs)` pick a centre assignment `X₀` with `chiX X₀ z ≠ 0`;
the term at the weight `Zs · chiX X₀` is the mode sum of `famX fam₀ famC X₀` (VBZ2 per term, after the swap), whence
`chiX X₀ z · |term κ| ≤ chiX X₀ z · Σ_ξ modeWt · ampBound · ∏ lb ≤ chiX X₀ z · ampBound ampQ z · ∏ lb`, where the
**majorant amplitude** `ampQ fam₀ M` is, on a non-centred slot, `Σ_l w₀ |a₀|` and, on a centred slot, the uniform mass
bound `M ≥ Σ_l (famC c y).w l` of the chain pieces (hypothesis `hM`; it is NOT implied by the other data: a
centre-indexed family with unbounded masses allows slot kernels of arbitrary growth at the centred slots, and then the
decoration sum need not converge absolutely).

* `tsum_ampBound_le_of_loc` (main's `Represents.tsum_ampBound_mode_le` for a localized amplitude, copied);
* `wQ`, `aQ`, `bndQ`, `ampQ`, **`summable_ampBound_ampQ`**;
* `hasSum_modeWt_ampBound_famX`, **`prod_famX_le_ampQ`** (`Σ_ξ modeWt · ampBound ≤ ampBound ampQ`, every `X`);
* `norm_skelTerm_glueGWZ_le_wt` (VBZ1's glue bound keeping the weight), `exists_chiXR_ne_zero`;
* **`norm_skelTermWZ_glue_le_centred`**, **`summable_norm_skelTermWZ_centred`**. -/

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
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW modalFnGW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (kBoundGW summable_kBoundGW resDec_glueDecGW)
open WaveTurbulence.Flower.MkSlotsB

variable {w d : ℕ}

/-! ## Decoration count for a localized amplitude -/

open scoped Classical in
/-- **The decoration sum of a localized amplitude bound** (main's `Represents.tsum_ampBound_mode_le` with an arbitrary
amplitude of norm `≤ 1` whose pair-slot values are supported in unit balls). -/
theorem tsum_ampBound_le_of_loc {G : Garden w} (hG : G.IsPlain) (L : ℝ) (hL : 0 < L) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (amp : ReplacementSlot G → Mom d → ℂ) (h1 : ∀ s k, ‖amp s k‖ ≤ 1)
    (c : SourcePair G → Mom d) (hloc : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - c p‖ ≤ 1) :
    Summable (fun z : GenDecoration G d roots 0 => ampBound hG L base amp z) ∧
      ∑' z : GenDecoration G d roots 0, ampBound hG L base amp z ≤
        (((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair G) : ℕ) := by
  obtain ⟨hF, hC⟩ := decoration_count_pairs hG L hL base roots c
  set K := {κ : GenDecoration G d roots 0 |
    ∀ p, hasBond hG (Sum.inl p) → ‖base + latticePoint L (κ.1 (slotNode hG (Sum.inl p))) - c p‖ ≤ 1} with hK
  have hle : ∀ z : GenDecoration G d roots 0,
      ampBound hG L base amp z ≤ if z ∈ hF.toFinset then 1 else 0 := by
    intro z
    by_cases hz : z ∈ hF.toFinset
    · simp only [hz, ite_true]
      unfold ampBound
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => h1 s _
    · simp only [hz, ite_false]
      have hz' : z ∉ K := by simpa [Set.Finite.mem_toFinset] using hz
      simp only [hK, Set.mem_ofPred_eq, not_forall] at hz'
      obtain ⟨p, _, hp⟩ := hz'
      have h0 : amp (Sum.inl p) (base + latticePoint L (z.1 (slotNode hG (Sum.inl p)))) = 0 := by
        by_contra hne
        exact hp (hloc p _ hne)
      unfold ampBound
      rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl p)) (by simp [h0])]
  have hnn : ∀ z : GenDecoration G d roots 0, 0 ≤ ampBound hG L base amp z := fun z => ampBound_nonneg _ _ _ _ _
  have hs : Summable (fun z : GenDecoration G d roots 0 => if z ∈ hF.toFinset then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := hF.toFinset) (fun x hx => by simp [hx])
  refine ⟨Summable.of_nonneg_of_le hnn hle hs, ?_⟩
  calc ∑' z : GenDecoration G d roots 0, ampBound hG L base amp z
      ≤ ∑' z : GenDecoration G d roots 0, (if z ∈ hF.toFinset then (1 : ℝ) else 0) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hs) hs
    _ = (hF.toFinset.card : ℝ) := by
        rw [tsum_eq_sum (s := hF.toFinset) (fun x hx => by simp [hx]), Finset.sum_ite_of_true (fun x hx => hx),
          Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
        have : hF.toFinset.card ≤ ((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair G) := by
          rw [← Set.ncard_eq_toFinset_card _ hF]; exact hC
        exact_mod_cast this

/-! ## The majorant amplitude -/

section Maj
variable {G : Garden w} (fam₀ : SlotFam G d) (M : ℝ)

open scoped Classical in
/-- The majorant weights: `fam₀`'s off the centred slots, one mode of weight `M` on them. -/
def wQ (s : ReplacementSlot G) : fam₀.Λ s ⊕ Unit → ℝ :=
  Sum.elim (fun l => if IsCentred s then 0 else fam₀.w s l) (fun _ => if IsCentred s then M else 0)

open scoped Classical in
/-- The majorant amplitudes: `fam₀`'s, and the constant `1` for the extra mode on the centred slots. -/
def aQ (s : ReplacementSlot G) : fam₀.Λ s ⊕ Unit → Mom d → ℂ :=
  Sum.elim (fam₀.a s) (fun _ _ => if IsCentred s then 1 else 0)

/-- The majorant slot bound `Σ_l wQ · |aQ|`. -/
def bndQ (s : ReplacementSlot G) (k : Mom d) : ℝ := ∑' l, wQ fam₀ M s l * ‖aQ fam₀ s l k‖

/-- **The majorant amplitude** (complex, for `ampBound`). -/
def ampQ (s : ReplacementSlot G) (k : Mom d) : ℂ := (bndQ fam₀ M s k : ℂ)

variable {M}

theorem wQ_nonneg (hM0 : 0 ≤ M) (s : ReplacementSlot G) (l : fam₀.Λ s ⊕ Unit) : 0 ≤ wQ fam₀ M s l := by
  classical
  rcases l with l | u
  · show 0 ≤ (if IsCentred s then 0 else fam₀.w s l)
    split_ifs
    · exact le_rfl
    · exact fam₀.w_nn s l
  · show 0 ≤ (if IsCentred s then M else 0)
    split_ifs
    · exact hM0
    · exact le_rfl

theorem summable_wQ (s : ReplacementSlot G) : Summable (wQ fam₀ M s) := by
  classical
  refine Summable.sum _ ?_ ?_
  · by_cases h : IsCentred s
    · have e : wQ fam₀ M s ∘ Sum.inl = fun _ => 0 := by
        funext l
        simp only [wQ, Function.comp_apply, Sum.elim_inl, h, ↓reduceIte]
      rw [e]
      exact summable_zero
    · have e : wQ fam₀ M s ∘ Sum.inl = fam₀.w s := by
        funext l
        simp only [wQ, Function.comp_apply, Sum.elim_inl, h, ↓reduceIte]
      rw [e]
      exact fam₀.w_sum s
  · exact (hasSum_fintype _).summable

theorem norm_aQ_le (s : ReplacementSlot G) (l : fam₀.Λ s ⊕ Unit) (k : Mom d) : ‖aQ fam₀ s l k‖ ≤ 1 := by
  classical
  rcases l with l | u
  · exact fam₀.a_one s l k
  · show ‖(if IsCentred s then (1 : ℂ) else 0)‖ ≤ 1
    split_ifs <;> simp

theorem summable_bndQ_term (hM0 : 0 ≤ M) (s : ReplacementSlot G) (k : Mom d) :
    Summable fun l => wQ fam₀ M s l * ‖aQ fam₀ s l k‖ :=
  Summable.of_nonneg_of_le (fun l => mul_nonneg (wQ_nonneg fam₀ hM0 s l) (norm_nonneg _))
    (fun l => mul_le_of_le_one_right (wQ_nonneg fam₀ hM0 s l) (norm_aQ_le fam₀ s l k)) (summable_wQ fam₀ s)

theorem bndQ_nonneg (hM0 : 0 ≤ M) (s : ReplacementSlot G) (k : Mom d) : 0 ≤ bndQ fam₀ M s k :=
  tsum_nonneg fun l => mul_nonneg (wQ_nonneg fam₀ hM0 s l) (norm_nonneg _)

/-- The pair-slot amplitudes of a majorant mode are localized (at the `fam₀` centre of its `fam₀` part). -/
theorem aQ_loc (ξ' : ∀ s, fam₀.Λ s ⊕ Unit) (p : SourcePair G) (k : Mom d)
    (h : aQ fam₀ (Sum.inl p) (ξ' (Sum.inl p)) k ≠ 0) :
    ‖k - Sum.elim (fun l => latPt d (fam₀.n (Sum.inl p) l)) (fun _ => 0) (ξ' (Sum.inl p))‖ ≤ 1 := by
  classical
  generalize ξ' (Sum.inl p) = l at h ⊢
  rcases l with l | u
  · exact fam₀.a_supp p l k h
  · exact absurd (show (if IsCentred (Sum.inl p : ReplacementSlot G) then (1 : ℂ) else 0) = 0 from
      ite_eq_right (fun h' => h')) h

/-- **The majorant amplitude bound is summable over the decorations.** -/
theorem summable_ampBound_ampQ (hG : G.IsPlain) {L : ℝ} (hL : 0 < L) (base : Mom d) (roots : Fin w → Fin d → ℤ)
    (hM0 : 0 ≤ M) :
    Summable (fun z : GenDecoration G d roots 0 => ampBound hG L base (ampQ fam₀ M) z) := by
  set C₀ : ℝ := ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair G) : ℕ) : ℝ)
  let F : (∀ s, fam₀.Λ s ⊕ Unit) × GenDecoration G d roots 0 → ℝ := fun p =>
    (∏ s, wQ fam₀ M s (p.1 s)) * ampBound hG L base (fun s => aQ fam₀ s (p.1 s)) p.2
  have hW0 : ∀ ξ' : ∀ s, fam₀.Λ s ⊕ Unit, 0 ≤ ∏ s, wQ fam₀ M s (ξ' s) :=
    fun ξ' => Finset.prod_nonneg fun s _ => wQ_nonneg fam₀ hM0 s _
  have hF0 : 0 ≤ F := fun p => mul_nonneg (hW0 p.1) (ampBound_nonneg _ _ _ _ _)
  have hloc := fun ξ' : ∀ s, fam₀.Λ s ⊕ Unit => tsum_ampBound_le_of_loc hG L hL base roots
    (fun s => aQ fam₀ s (ξ' s)) (fun s k => norm_aQ_le fam₀ s _ k)
    (fun p => Sum.elim (fun l => latPt d (fam₀.n (Sum.inl p) l)) (fun _ => 0) (ξ' (Sum.inl p)))
    (fun p k h => aQ_loc fam₀ ξ' p k h)
  have hW : HasSum (fun ξ' : ∀ s, fam₀.Λ s ⊕ Unit => ∏ s, wQ fam₀ M s (ξ' s)) (∏ s, ∑' l, wQ fam₀ M s l) :=
    hasSum_prod_real _ (wQ_nonneg fam₀ hM0) (summable_wQ fam₀)
  have hFs : Summable F := by
    refine (summable_prod_of_nonneg hF0).2 ⟨fun ξ' => ?_, ?_⟩
    · show Summable fun z => (∏ s, wQ fam₀ M s (ξ' s)) * ampBound hG L base (fun s => aQ fam₀ s (ξ' s)) z
      exact (hloc ξ').1.mul_left _
    · refine Summable.of_nonneg_of_le (fun ξ' => tsum_nonneg fun z => hF0 (ξ', z)) (fun ξ' => ?_)
        (hW.summable.mul_right C₀)
      show ∑' z, (∏ s, wQ fam₀ M s (ξ' s)) * ampBound hG L base (fun s => aQ fam₀ s (ξ' s)) z ≤
        (∏ s, wQ fam₀ M s (ξ' s)) * C₀
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hloc ξ').2 (hW0 ξ')
  have hFs' : Summable (F ∘ Equiv.prodComm _ _) := (Equiv.summable_iff _).mpr hFs
  have h2 := ((summable_prod_of_nonneg (f := F ∘ Equiv.prodComm _ _) fun p => hF0 _).1 hFs').2
  refine h2.congr fun z => ?_
  show ∑' ξ', F (ξ', z) = _
  have hz : HasSum (fun ξ' : ∀ s, fam₀.Λ s ⊕ Unit =>
      ∏ s, wQ fam₀ M s (ξ' s) * ‖aQ fam₀ s (ξ' s) (base + latticePoint L (z.1 (slotNode hG s)))‖)
      (∏ s, bndQ fam₀ M s (base + latticePoint L (z.1 (slotNode hG s)))) :=
    hasSum_prod_real (fun s l => wQ fam₀ M s l * ‖aQ fam₀ s l (base + latticePoint L (z.1 (slotNode hG s)))‖)
      (fun s l => mul_nonneg (wQ_nonneg fam₀ hM0 s l) (norm_nonneg _))
      (fun s => summable_bndQ_term fam₀ hM0 s _)
  have e1 : ampBound hG L base (ampQ fam₀ M) z = ∏ s, bndQ fam₀ M s (base + latticePoint L (z.1 (slotNode hG s))) := by
    unfold ampBound ampQ
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (bndQ_nonneg fam₀ hM0 s _)]
  rw [e1, ← hz.tsum_eq]
  refine tsum_congr fun ξ' => ?_
  show (∏ s, wQ fam₀ M s (ξ' s)) * ampBound hG L base (fun s => aQ fam₀ s (ξ' s)) z = _
  unfold ampBound
  rw [Finset.prod_mul_distrib]

end Maj

/-! ## The mode sum of the amplitude bounds -/

section ModeBound
variable {G : Garden w} (fam₀ : SlotFam G d) (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d)
  (X : CentredSlot G → (Fin d → ℤ))

theorem summable_famX_term (s : ReplacementSlot G) (k : Mom d) :
    Summable fun l => (famX fam₀ famC X).w s l * ‖(famX fam₀ famC X).a s l k‖ :=
  Summable.of_nonneg_of_le (fun l => mul_nonneg ((famX fam₀ famC X).w_nn s l) (norm_nonneg _))
    (fun l => mul_le_of_le_one_right ((famX fam₀ famC X).w_nn s l) ((famX fam₀ famC X).a_one s l k))
    ((famX fam₀ famC X).w_sum s)

/-- The mode sum of `modeWt · ampBound` is the product of the slot sums `Σ_l w |a|`. -/
theorem hasSum_modeWt_ampBound_famX (hG : G.IsPlain) (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) :
    HasSum (fun ξ : ∀ s, (famX fam₀ famC X).Λ s => modeWt (famX fam₀ famC X) ξ *
        ampBound hG L base (fun s x => (famX fam₀ famC X).a s (ξ s) x) z)
      (∏ s, ∑' l, (famX fam₀ famC X).w s l *
        ‖(famX fam₀ famC X).a s l (base + latticePoint L (z.1 (slotNode hG s)))‖) := by
  have h := hasSum_prod_real (fun s l => (famX fam₀ famC X).w s l *
      ‖(famX fam₀ famC X).a s l (base + latticePoint L (z.1 (slotNode hG s)))‖)
    (fun s l => mul_nonneg ((famX fam₀ famC X).w_nn s l) (norm_nonneg _))
    (fun s => summable_famX_term fam₀ famC X s _)
  refine h.congr_fun fun ξ => ?_
  unfold modeWt ampBound
  rw [Finset.prod_mul_distrib]

theorem tsum_chainPiece_le (P : ChainPiece d) (k : Mom d) : ∑' l, P.w l * ‖P.a l k‖ ≤ ∑' l, P.w l :=
  Summable.tsum_le_tsum (fun l => mul_le_of_le_one_right (P.w_nn l) (P.a_one l k))
    (Summable.of_nonneg_of_le (fun l => mul_nonneg (P.w_nn l) (norm_nonneg _))
      (fun l => mul_le_of_le_one_right (P.w_nn l) (P.a_one l k)) P.w_sum) P.w_sum

/-- **The slot sums of `famX X` are bounded by the majorant**, uniformly in `X`. -/
theorem tsum_famX_term_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c y, ∑' l, (famC c y).w l ≤ M) (s : ReplacementSlot G)
    (k : Mom d) :
    ∑' l, (famX fam₀ famC X).w s l * ‖(famX fam₀ famC X).a s l k‖ ≤ bndQ fam₀ M s k := by
  classical
  have hX := summable_famX_term fam₀ famC X s k
  have hQ := summable_bndQ_term fam₀ hM0 s k
  have hsX : ∑' l : (famX fam₀ famC X).Λ s, (famX fam₀ famC X).w s l * ‖(famX fam₀ famC X).a s l k‖ =
      ∑' l : fam₀.Λ s, (famX fam₀ famC X).w s (Sum.inl l) * ‖(famX fam₀ famC X).a s (Sum.inl l) k‖ +
      ∑' l : (pieceAtX famC X s).Λ, (famX fam₀ famC X).w s (Sum.inr l) * ‖(famX fam₀ famC X).a s (Sum.inr l) k‖ :=
    Summable.tsum_sum (hX.comp_injective Sum.inl_injective) (hX.comp_injective Sum.inr_injective)
  unfold bndQ
  rw [hsX, Summable.tsum_sum (hQ.comp_injective Sum.inl_injective) (hQ.comp_injective Sum.inr_injective)]
  by_cases hs : IsCentred s
  · have e1 : ∀ l : fam₀.Λ s, (famX fam₀ famC X).w s (Sum.inl l) * ‖(famX fam₀ famC X).a s (Sum.inl l) k‖ = 0 :=
      fun l => by simp only [famX_w_inl, hs, ↓reduceIte, zero_mul]
    have e2 : ∀ l : fam₀.Λ s, wQ fam₀ M s (Sum.inl l) * ‖aQ fam₀ s (Sum.inl l) k‖ = 0 :=
      fun l => by simp only [wQ, Sum.elim_inl, hs, ↓reduceIte, zero_mul]
    have e3 : ∀ u : Unit, wQ fam₀ M s (Sum.inr u) * ‖aQ fam₀ s (Sum.inr u) k‖ = M :=
      fun u => by simp only [wQ, aQ, Sum.elim_inr, hs, ↓reduceIte, norm_one, mul_one]
    simp only [e1, e2, e3, tsum_zero, zero_add]
    rw [show ∑' _ : Unit, M = M from (tsum_fintype _).trans (by simp)]
    rcases s with q | c
    · exact hs.elim
    · have key : ∀ P : ChainPiece d, P = famC ⟨c, hs⟩ (X ⟨c, hs⟩) → ∑' l, P.w l * ‖P.a l k‖ ≤ M := by
        rintro P rfl
        exact (tsum_chainPiece_le _ k).trans (hM _ _)
      exact key _ (pieceAtX_centred famC X ⟨c, hs⟩)
  · have e1 : ∀ l : fam₀.Λ s, (famX fam₀ famC X).w s (Sum.inl l) * ‖(famX fam₀ famC X).a s (Sum.inl l) k‖ =
        wQ fam₀ M s (Sum.inl l) * ‖aQ fam₀ s (Sum.inl l) k‖ :=
      fun l => by simp only [famX_w_inl, famX_a_inl, wQ, aQ, Sum.elim_inl, hs, ↓reduceIte]
    have e3 : ∀ u : Unit, wQ fam₀ M s (Sum.inr u) * ‖aQ fam₀ s (Sum.inr u) k‖ = 0 :=
      fun u => by simp only [wQ, Sum.elim_inr, hs, ↓reduceIte, zero_mul]
    have := isEmpty_pieceAtX famC X hs
    simp only [e1, e3, tsum_zero, tsum_empty, le_refl]

/-- **The mode sum of the amplitude bounds of `famX X` is bounded by the majorant amplitude bound**, uniformly in the
centre assignment `X`. -/
theorem prod_famX_le_ampQ (hG : G.IsPlain) (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c y, ∑' l, (famC c y).w l ≤ M) (z : GenDecoration G d roots 0) :
    ∏ s, ∑' l, (famX fam₀ famC X).w s l *
        ‖(famX fam₀ famC X).a s l (base + latticePoint L (z.1 (slotNode hG s)))‖ ≤
      ampBound hG L base (ampQ fam₀ M) z := by
  unfold ampBound ampQ
  refine Finset.prod_le_prod₀ (fun s _ => tsum_nonneg fun l =>
    mul_nonneg ((famX fam₀ famC X).w_nn s l) (norm_nonneg _)) fun s _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (bndQ_nonneg fam₀ hM0 s _)]
  exact tsum_famX_term_le fam₀ famC X hM0 hM s _

/-- Some centre assignment carries a non-zero node partition. -/
theorem exists_chiXR_ne_zero (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0) :
    ∃ X : CentredSlot G → (Fin d → ℤ), chiXR L base X z ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hasSum_chiXR L base z
  have h0 : (fun X => chiXR L base X z) = fun _ => 0 := funext hcon
  rw [h0] at h1
  exact one_ne_zero (h1.unique hasSum_zero)

end ModeBound

/-! ## The decoration bound -/

section Bound
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- The glued term keeps its weight in the bound (VBZ1's `norm_skelTerm_glueGWZ_le_fix` without `‖Zw‖ ≤ 1`). -/
theorem norm_skelTerm_glueGWZ_le_wt (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        (Φ.glueDec hS hd hL base z κs)‖ ≤
      ‖Zw z‖ * (ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) := by
  rw [skelTerm_glueGWZ_fix Φ hd hSb hL γ δ D layer tt amp frq Zs Zw hZ fixS hU hG z κs, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_psiIntGWD_le_fix Φ RB hd D hSb γ δ layer tt amp frq z κs
    (fun c => fixS (Φ.br c)) hG.meas hG.mass) (norm_nonneg _)

/-- The decoration bound under the agreement hypothesis (at every centre assignment). -/
theorem norm_skelTermWZ_glue_le_centred_agree (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c y, ∑' l, (famC c y).w l ≤ M)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (hA : ∀ X, CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermWZ blk hS L γ δ base roots tt Zs Fs
        (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS
        (Φ.glueDec hS hd hL0.ne' base z κs)‖ ≤ kBoundGW Φ RB hSb (ampQ fam₀ M) ⟨z, κs⟩ := by
  obtain ⟨X₀, hX₀⟩ := exists_chiXR_ne_zero L base z
  have hG := GlueDomR.relaxedLB Φ hd D hS layer tt fixS lbS hU hlbU hP
  set P : ℝ := ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) with hPdef
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => RB.nonneg j _
  have hchi0 := chiXR_nonneg L base X₀ z
  have hmodes := hasSum_skelTerm_modesGWZ_fix Φ (swapRB Φ hS hSb (famX fam₀ famC X₀) RB) hd hSb hL0.ne' γ δ D layer
    tt (fun κ => Zs κ * chiX L base X₀ (Φ.resDec hS hd κ)) (famX fam₀ famC X₀) Box
    (fun s' ts _ x => by rw [swapFs_iota]; exact hasSum_famVal _ s' ts x) fixS hU hG hbox z κs
  have hS' := (hasSum_modeWt_ampBound_famX fam₀ famC X₀ hSb L base z).mul_left (chiXR L base X₀ z * P)
  have hle := hmodes.norm_le_of_bounded hS' fun ξ => by
    have h1 := norm_skelTerm_glueGWZ_le_wt Φ (swapRB Φ hS hSb (famX fam₀ famC X₀) RB) hd hSb hL0.ne' γ δ D layer tt
      (fun s' x => (famX fam₀ famC X₀).a s' (ξ s') x) (fun s' => (famX fam₀ famC X₀).m s' (ξ s'))
      (fun κ => Zs κ * chiX L base X₀ (Φ.resDec hS hd κ)) (fun z => Zw z * chiX L base X₀ z)
      (fun κ => by simp only [hZ κ]) fixS hU hG z κs
    rw [swapRB_lb] at h1
    have h2 : ‖Zw z * chiX L base X₀ z‖ ≤ chiXR L base X₀ z := by
      rw [norm_mul, norm_chiX]
      exact mul_le_of_le_one_left hchi0 (hZw z)
    have hw0 := modeWt_nonneg (famX fam₀ famC X₀) ξ
    have ha0 := ampBound_nonneg hSb L base (fun s' x => (famX fam₀ famC X₀).a s' (ξ s') x) z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    calc _ ≤ modeWt (famX fam₀ famC X₀) ξ * (chiXR L base X₀ z *
          (ampBound hSb L base (fun s' x => (famX fam₀ famC X₀).a s' (ξ s') x) z * P)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 (mul_nonneg ha0 hP0))) hw0
      _ = _ := by ring
  rw [skelTermWZ_swapFsX_agree Φ hd hSb γ δ tt Zs fam₀ famC Box _ fixS hbox X₀ (hA X₀)] at hle
  have e : skelTermWZ blk hS L γ δ base roots tt (fun κ => Zs κ * chiX L base X₀ (Φ.resDec hS hd κ)) Fs
      (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS
      (Φ.glueDec hS hd hL0.ne' base z κs) = (chiXR L base X₀ z : ℂ) * skelTermWZ blk hS L γ δ base roots tt Zs Fs
      (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS
      (Φ.glueDec hS hd hL0.ne' base z κs) := by
    simp only [skelTermWZ, resDec_glueDecGW Φ hd hL0.ne' base z κs, chiX_eq]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hchi0] at hle
  have hpos : 0 < chiXR L base X₀ z := lt_of_le_of_ne hchi0 (Ne.symm hX₀)
  have hPi := prod_famX_le_ampQ fam₀ famC X₀ hSb L base hM0 hM z
  show _ ≤ ampBound hSb L base (ampQ fam₀ M) z * P
  refine le_of_mul_le_mul_left (hle.trans ?_) hpos
  rw [mul_assoc, mul_comm (ampBound hSb L base (ampQ fam₀ M) z) P]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPi hP0) hchi0

/-- The absolute decoration summability under the agreement hypothesis. -/
theorem summable_norm_skelTermWZ_centred_agree (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c y, ∑' l, (famC c y).w l ≤ M)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (hA : ∀ X, CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X) :
    Summable fun κ : GenDecoration S d roots 0 => ‖skelTermWZ blk hS L γ δ base roots tt Zs Fs
      (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS κ‖ := by
  have hk := summable_kBoundGW Φ RB hSb (roots := roots) (ampQ fam₀ M)
    (summable_ampBound_ampQ fam₀ hSb hL0 base roots hM0)
  have hk' := (Φ.decSplit hS hd hL0.ne' base roots).summable_iff.mpr hk
  refine Summable.of_nonneg_of_le (fun κ => norm_nonneg _) (fun κ => ?_) hk'
  have h := norm_skelTermWZ_glue_le_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box hM0 hM
    fixS lbS hU hlbU hP hbox hA ((Φ.decSplit hS hd hL0.ne' base roots) κ).1
    ((Φ.decSplit hS hd hL0.ne' base roots) κ).2
  have hκ : Φ.glueDec hS hd hL0.ne' base ((Φ.decSplit hS hd hL0.ne' base roots) κ).1
      ((Φ.decSplit hS hd hL0.ne' base roots) κ).2 = κ := (Φ.decSplit hS hd hL0.ne' base roots).symm_apply_apply κ
  rw [hκ] at h
  exact h

end Bound

end WaveTurbulence.Flower.MkSlotsI
