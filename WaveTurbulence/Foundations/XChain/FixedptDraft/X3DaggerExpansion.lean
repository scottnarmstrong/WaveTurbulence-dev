/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DyadicReduction
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3FinitElem

/-!
# X3 DaggerExpansion: removing the phase at `𝔣^pr` (T L2326–L2327)

**Statement** (`hasSum_randFlowerKernel_dagger`). Let `d ≥ 1`, `L ≠ 0`, and let `a(p)` be summable. Then for any
kind, pattern, cutoffs, `ζ`, `t`, `s`, `k`, `k'`:

`HasSum (x ↦ e^{i θ_x(k') s} · 𝒦[† := c_x](t, s, k, k')) 𝒦[† := none](t, s, k, k')`.

The index `x = (i, w)` runs over `i : Fin 3` and `w : Fin 3 → ℤ^d` with `w_i = 0`. Here:
* `c_x = dagLabel L x` has the sentinel `v₀ ∉ ℤ^d/L` in slot `i` and `w_m/L` in the slots `m ≠ i`;
* `θ_x(k') = π ζ (−1)^{[i=1]} δ L^{2γ} Ω(ch)` (`dagTheta`), where `ch_i = k'` and `ch_m = w_m` for `m ≠ i`.

Why it holds:
- The sentinel cannot be a sibling label, so `𝒦[† := c_x]` keeps exactly the trees whose flower is the
  `i`-th child of `𝔣^pr`.
- On those trees, `ζ_{𝔣^pr} = ζ(−1)^{[i=1]}` and `Ω_{𝔣^pr} = Ω(ch)` for the decorations with siblings `w`.
- Hence `e^{iθ_x s}` is the phase removed at `𝔣^pr` (whose time is `s`).
- Each decoration matches exactly one index `x`.

**Support** (`flowerKernelGen_dagger_eq_zero`). With `cut1 = j₁`, the term of `x` vanishes unless
`|w_m/L| < ℓ_max 2^{j₁} L` for `m ≠ i`. The proof is the sum rule at the sibling `m`, whose leaves are
non-flower leaves.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree

variable {d : ℕ}

/-! ## The labels and phases -/

/-- The sentinel `v₀ = (1/(2L), …, 1/(2L))`; it is not in `ℤ^d/L` for `d ≥ 1`. -/
noncomputable def sentinel (L : ℝ) : Mom d := WithLp.toLp 2 fun _ => 1 / (2 * L)

theorem latticePoint_ne_sentinel (hd : 0 < d) {L : ℝ} (hL : L ≠ 0) (k : Fin d → ℤ) :
    latticePoint L k ≠ sentinel L := by
  intro h
  have h0 := congrArg (fun v : Mom d => v ⟨0, hd⟩) h
  simp only [latticePoint, sentinel] at h0
  have h1 : (2 * (k ⟨0, hd⟩) : ℝ) = 1 := by
    field_simp at h0
    linarith
  have h2 : 2 * k ⟨0, hd⟩ = 1 := by exact_mod_cast h1
  omega

/-- The index of the expansion: `(i, w)` with `w_i = 0`. -/
abbrev DagIdx (d : ℕ) : Type := Σ _i : Fin 3, {w : Fin 3 → (Fin d → ℤ) // w _i = 0}

/-- The `†` label of `x = (i, w)`: the sentinel in slot `i`, `w_m/L` elsewhere. -/
noncomputable def dagLabel (L : ℝ) (x : DagIdx d) : Fin 3 → Mom d :=
  fun m => if m = x.1 then sentinel L else latticePoint L (x.2.1 m)

/-- The children momenta at `𝔣^pr`: `k'` in slot `i`, `w_m` elsewhere. -/
def dagChildren (x : DagIdx d) (k' : Fin d → ℤ) : Fin 3 → (Fin d → ℤ) :=
  fun m => if m = x.1 then k' else x.2.1 m

/-- `θ_x(k') = π ζ (−1)^{[i=1]} δ L^{2γ} Ω(ch)`. -/
noncomputable def dagTheta (L γ δ : ℝ) (ζ : ℤˣ) (x : DagIdx d) (k' : Fin d → ℤ) : ℝ :=
  Real.pi * (((ζ * (if x.1 = 1 then -1 else 1) : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
    resFactor (latticePoint L (dagChildren x k' 0)) (latticePoint L (dagChildren x k' 1))
      (latticePoint L (dagChildren x k' 2))
      (latticePoint L (dagChildren x k' 0 - dagChildren x k' 1 + dagChildren x k' 2))

/-- The phase `e^{i θ_x(k') s}`. -/
noncomputable def dagPhase (L γ δ : ℝ) (ζ : ℤˣ) (x : DagIdx d) (k' : Fin d → ℤ) (s : ℝ) : ℂ :=
  Complex.exp ((dagTheta L γ δ ζ x k' * s : ℝ) * Complex.I)

theorem norm_dagPhase (L γ δ : ℝ) (ζ : ℤˣ) (x : DagIdx d) (k' : Fin d → ℤ) (s : ℝ) :
    ‖dagPhase L γ δ ζ x k' s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

instance : Countable (DagIdx d) := inferInstance

/-! ## The flower slot -/

section Slot

variable {F : FTree} (hF : F ≠ flower)

/-- The slot of the flower among the children of `𝔣^pr`. -/
def flowerSlot : Fin 3 := F.flowerPath.getLast (flowerPath_ne_nil hF)

theorem flowerParent_child_path (m : Fin 3) :
    ((F.flowerParent hF).child m).1.2 = F.flowerPath.dropLast ++ [m] := rfl

theorem flowerParent_child_eq_iff (m : Fin 3) :
    ((F.flowerParent hF).child m).1.2 = F.flowerPath ↔ m = flowerSlot hF := by
  rw [flowerParent_child_path]
  conv_lhs => rhs; rw [← List.dropLast_append_getLast (flowerPath_ne_nil hF)]
  rw [List.append_cancel_left_eq, List.singleton_inj]
  rfl

theorem flowerParent_child_flowerSlot :
    (F.flowerParent hF).child (flowerSlot hF) = F.flowerLeaf.toNode := by
  refine Subtype.ext (Prod.ext (Subsingleton.elim _ _) ?_)
  exact (flowerParent_child_eq_iff hF _).2 rfl

/-- `ζ_{𝔣^pr} = ζ_𝔣 (−1)^{[slot = 1]}`. -/
theorem treeSign_flowerParent :
    treeSign F.toTree (F.flowerParent hF).toNode =
      F.sign * (if flowerSlot hF = 1 then -1 else 1) := by
  have hs := treeSign_flowerLeaf F
  rw [← flowerParent_child_flowerSlot hF] at hs
  obtain ⟨h0, h1, h2⟩ := nodeSign_child (fun _ : Fin 1 => (1 : ℤˣ)) (F.flowerParent hF)
  unfold treeSign at hs ⊢
  have hn : (F.flowerParent hF).toNode.1 = (F.flowerParent hF).1 := rfl
  rw [hn]
  generalize flowerSlot hF = m at hs ⊢
  fin_cases m
  · have := h0.symm.trans hs
    rw [← this]; simp
  · have := h1.symm.trans hs
    rw [← this]; simp
  · have := h2.symm.trans hs
    rw [← this]; simp

end Slot

/-! ## One decoration -/

section Decoration

variable (L γ δ : ℝ) {F : FTree} (hF : F ≠ flower) {k k' : Fin d → ℤ} (κ : FlowerDecoration F d k k')

/-- The index matched by `κ`: the flower slot and the sibling momenta. -/
def dagIdxOf : DagIdx d :=
  ⟨flowerSlot hF, ⟨fun m => if m = flowerSlot hF then 0 else κ.1.1 ((F.flowerParent hF).child m), by simp⟩⟩

theorem treeSib_dagIdxOf : treeSib L F hF (dagLabel L (dagIdxOf hF κ)) κ.1.1 = 1 := by
  unfold treeSib
  refine Finset.prod_eq_one fun m _ => ?_
  by_cases hm : m = flowerSlot hF
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((flowerParent_child_eq_iff hF m).2 hm))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hm ((flowerParent_child_eq_iff hF m).1 h)))]
    simp [dagLabel, dagIdxOf, hm]

theorem treeSib_eq_zero (hd : 0 < d) (hL : L ≠ 0) {x : DagIdx d} (hx : x ≠ dagIdxOf hF κ) :
    treeSib L F hF (dagLabel L x) κ.1.1 = 0 := by
  classical
  unfold treeSib
  obtain ⟨i, w, hw⟩ := x
  by_cases hi : i = flowerSlot hF
  · subst hi
    have hne : ∃ m, w m ≠ (dagIdxOf hF κ).2.1 m := by
      by_contra hall
      push Not at hall
      exact hx (by
        show (⟨flowerSlot hF, ⟨w, hw⟩⟩ : DagIdx d) = ⟨flowerSlot hF, ⟨_, _⟩⟩
        congr 2
        exact funext hall)
    obtain ⟨m, hm⟩ := hne
    have hmi : m ≠ flowerSlot hF := fun e => hm (by subst e; simp [dagIdxOf, hw])
    refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hmi ((flowerParent_child_eq_iff hF m).1 h)))]
    have hval : (dagIdxOf hF κ).2.1 m = κ.1.1 ((F.flowerParent hF).child m) := by simp [dagIdxOf, hmi]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
    simp only [dagLabel, hmi, ↓reduceIte] at h
    exact hm ((latticePoint_injective hL h).symm.trans hval.symm)
  · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hi ((flowerParent_child_eq_iff hF i).1 h)))]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
    simp only [dagLabel, ↓reduceIte] at h
    exact latticePoint_ne_sentinel hd hL _ h

/-- The children momenta of `𝔣^pr` under `κ`. -/
theorem dagChildren_dagIdxOf (m : Fin 3) :
    dagChildren (dagIdxOf hF κ) k' m = κ.1.1 ((F.flowerParent hF).child m) := by
  by_cases hm : m = flowerSlot hF
  · subst hm
    simp only [dagChildren, dagIdxOf, ↓reduceIte]
    rw [flowerParent_child_flowerSlot hF, κ.2]
  · simp [dagChildren, dagIdxOf, hm]

/-- **The phase of the matched index is the phase at `𝔣^pr`.** -/
theorem dagTheta_dagIdxOf {ζ : ℤˣ} (hζ : F.sign = ζ) :
    dagTheta L γ δ ζ (dagIdxOf hF κ) k' = Real.pi * ((treeSign F.toTree (F.flowerParent hF).toNode : ℤˣ) : ℤ) *
      δ * L ^ (2 * γ) * omegaT L F.toTree κ.1.1 (F.flowerParent hF) := by
  unfold dagTheta omegaT
  rw [treeSign_flowerParent hF, hζ]
  simp only [dagChildren_dagIdxOf]
  rw [← κ.1.2.1 (F.flowerParent hF)]
  rfl

theorem extendFixT_flowerParent (pat : FixPat) (t s : ℝ)
    (τ : {b // treeFixPat F hF pat t s b = none} → ℝ) :
    extendFixT (treeFixPat F hF pat t s) τ (F.flowerParent hF) = s := by
  unfold extendFixT
  split
  · next v hv =>
    unfold treeFixPat at hv
    simp only [↓reduceIte, Option.some.injEq] at hv
    exact hv.symm
  · next hv =>
    unfold treeFixPat at hv
    simp at hv

/-- **`TI` with all phases = the `𝔣^pr` phase at time `s` × `TI` with `𝔣^pr` off.** -/
theorem TIpat_off (p : ℕ) (pat : FixPat) (t s : ℝ) :
    TIpat L γ δ hF p ∅ κ.1.1 pat t s =
      Complex.exp ((Real.pi * ((treeSign F.toTree (F.flowerParent hF).toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaT L F.toTree κ.1.1 (F.flowerParent hF) * s : ℝ) * Complex.I) *
      TIpat L γ δ hF p {F.flowerParent hF} κ.1.1 pat t s := by
  classical
  unfold TIpat
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  set x := extendFixT (treeFixPat F hF pat t s) τ
  have hxs : x (F.flowerParent hF) = s := extendFixT_flowerParent hF pat t s τ
  have hph : phaseOffT L γ δ F.toTree ∅ κ.1.1 x =
      Complex.exp ((Real.pi * ((treeSign F.toTree (F.flowerParent hF).toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaT L F.toTree κ.1.1 (F.flowerParent hF) * s : ℝ) * Complex.I) *
      phaseOffT L γ δ F.toTree {F.flowerParent hF} κ.1.1 x := by
    unfold phaseOffT
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (F.flowerParent hF)),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (F.flowerParent hF))]
    simp only [Finset.notMem_empty, ↓reduceIte, Finset.mem_singleton, hxs, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Finset.ne_of_mem_erase hc))]
  beta_reduce
  by_cases hm : x ∈ treeDomFix p F.toTree t (treeFixPat F hF pat t s)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hph]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, mul_zero]

end Decoration

/-! ## The kernels -/

section Kernels

variable (L γ δ : ℝ) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)

theorem treeWeight_dagger {F : FTree} (hF : F ≠ flower) (c : Fin 3 → Mom d) (cut1 cut2 : Option ℕ)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeWeight L F hF (some c) cut1 cut2 κ = treeWeight L F hF none cut1 cut2 κ * treeSib L F hF c κ := by
  simp [treeWeight]

theorem treeSib_eq_ite (hd : 0 < d) (hL : L ≠ 0) {F : FTree} (hF : F ≠ flower) {k k' : Fin d → ℤ}
    (κ : FlowerDecoration F d k k') (x : DagIdx d) :
    treeSib L F hF (dagLabel L x) κ.1.1 = if x = dagIdxOf hF κ then 1 else 0 := by
  split_ifs with h
  · rw [h]; exact treeSib_dagIdxOf L hF κ
  · exact treeSib_eq_zero L hF κ hd hL h

include haP in
/-- **The `†` expansion of one flower kernel.** -/
theorem hasSum_flowerKernelGen_dagger (hd : 0 < d) (hL : L ≠ 0) {F : FTree} {ζ : ℤˣ} (hζ : F.sign = ζ)
    (pat : FixPat) (cut1 cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun x : DagIdx d => dagPhase L γ δ ζ x k' s *
        flowerKernelGen L γ δ p F aP pat (some (dagLabel L x)) cut1 cut2 t s k k')
      (flowerKernelGen L γ δ p F aP pat none cut1 cut2 t s k k') := by
  classical
  by_cases hF : F = flower
  · simp only [flowerKernelGen, hF, ↓reduceDIte, mul_zero]
    exact hasSum_zero
  set pref := treePrefactor L γ δ d F.toTree
  set w0 : (GNode (single F.toTree) → (Fin d → ℤ)) → ℝ := fun κ => treeWeight L F hF none cut1 cut2 κ with hw0
  set g : FlowerDecoration F d k k' × DagIdx d → ℂ := fun z =>
    dagPhase L γ δ ζ z.2 k' s * (epsProd F.toTree z.1.1.1 *
      ((w0 z.1.1.1 * treeSib L F hF (dagLabel L z.2) z.1.1.1 : ℝ) : ℂ) *
      TIpat L γ δ hF p {F.flowerParent hF} z.1.1.1 pat t s * restP F aP z.1.1.1)
  have hR := summable_restP F haP k k'
  have hsib := fun (κ : FlowerDecoration F d k k') (x : DagIdx d) => treeSib_eq_ite L hd hL hF κ x
  have hgle : ∀ z : FlowerDecoration F d k k' × DagIdx d,
      ‖g z‖ ≤ (if z.2 = dagIdxOf hF z.1 then 1 else 0) * ‖restP F aP z.1.1.1‖ := fun z => by
    simp only [g]
    rw [hsib z.1 z.2, norm_mul, norm_dagPhase, one_mul]
    split_ifs with h
    · rw [mul_one]
      have h1 := norm_epsProd_le F.toTree z.1.1.1
      have h2 := abs_treeWeight_le_one L hF none cut1 cut2 z.1.1.1
      have h3 := norm_TIpat_le_one L γ δ hF p {F.flowerParent hF} z.1.1.1 pat t s
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖epsProd F.toTree z.1.1.1‖ * |treeWeight L F hF none cut1 cut2 z.1.1.1| *
            ‖TIpat L γ δ hF p {F.flowerParent hF} z.1.1.1 pat t s‖ * ‖restP F aP z.1.1.1‖
          ≤ 1 * 1 * 1 * ‖restP F aP z.1.1.1‖ := by gcongr
        _ = _ := by ring
    · simp
  have hfibκ : ∀ κ : FlowerDecoration F d k k',
      HasSum (fun x => (if x = dagIdxOf hF κ then (1 : ℝ) else 0) * ‖restP F aP κ.1.1‖) ‖restP F aP κ.1.1‖ :=
    fun κ => by
      have := hasSum_ite_eq (dagIdxOf hF κ) (‖restP F aP κ.1.1‖)
      convert this using 2 with x
      split_ifs <;> simp
  have hbsum : Summable fun z : FlowerDecoration F d k k' × DagIdx d =>
      (if z.2 = dagIdxOf hF z.1 then (1 : ℝ) else 0) * ‖restP F aP z.1.1.1‖ := by
    refine (summable_prod_of_nonneg (fun z => mul_nonneg (by split_ifs <;> norm_num) (norm_nonneg _))).2
      ⟨fun κ => (hfibκ κ).summable, hR.congr fun κ => ((hfibκ κ).tsum_eq).symm⟩
  have hg : Summable g := Summable.of_norm_bounded hbsum hgle
  -- fibers over `κ`
  have hfib1 : ∀ κ : FlowerDecoration F d k k', HasSum (fun x => g (κ, x))
      (epsProd F.toTree κ.1.1 * (w0 κ.1.1 : ℂ) * TIpat L γ δ hF p ∅ κ.1.1 pat t s * restP F aP κ.1.1) := by
    intro κ
    have hz : ∀ x ≠ dagIdxOf hF κ, g (κ, x) = 0 := fun x hx => by
      simp only [g, hsib κ x, ite_eq_right_of_eq_false _ _ (eq_false hx), mul_zero, Complex.ofReal_zero, zero_mul]
    convert hasSum_single (dagIdxOf hF κ) hz using 1
    simp only [g, hsib κ, ↓reduceIte, mul_one]
    rw [TIpat_off L γ δ hF κ p pat t s, dagPhase, dagTheta_dagIdxOf L γ δ hF κ hζ]
    ring
  have hS1 := hg.hasSum.prod_fiberwise hfib1
  have hg' : Summable (g ∘ (Equiv.prodComm (DagIdx d) (FlowerDecoration F d k k'))) :=
    (Equiv.prodComm (DagIdx d) (FlowerDecoration F d k k')).summable_iff.2 hg
  have hS2 : HasSum (fun x => ∑' κ : FlowerDecoration F d k k', g (κ, x)) (∑' z, g z) := by
    have h : HasSum (g ∘ (Equiv.prodComm (DagIdx d) (FlowerDecoration F d k k'))) (∑' z, g z) :=
      (Equiv.prodComm (DagIdx d) (FlowerDecoration F d k k')).hasSum_iff.2 hg.hasSum
    exact h.prod_fiberwise fun x => (hg'.prod_factor x).hasSum
  have hK : flowerKernelGen L γ δ p F aP pat none cut1 cut2 t s k k' = pref * ∑' z, g z := by
    rw [flowerKernelGen_eq L γ δ hF p]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (pref * ·) hS1.tsum_eq
  rw [hK]
  convert hS2.mul_left pref using 1
  funext x
  rw [flowerKernelGen_eq L γ δ hF p]
  simp only [g, Option.isSome_some, ↓reduceIte, treeWeight_dagger, tsum_mul_left]
  ring

variable (Ntr : ℕ) (kind : FlowerKind) (pat : FixPat) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)

include haP in
/-- **The `†` expansion of the random kernel of a kind.** -/
theorem hasSum_randFlowerKernel_dagger (hd : 0 < d) (hL : L ≠ 0) (t s : ℝ) (k k' : Fin d → ℤ) :
    HasSum (fun x : DagIdx d => dagPhase L γ δ ζ x k' s *
        randFlowerKernel L γ δ p Ntr aP kind pat (some (dagLabel L x)) cut1 cut2 ζ t s k k')
      (randFlowerKernel L γ δ p Ntr aP kind pat none cut1 cut2 ζ t s k k') := by
  classical
  unfold randFlowerKernel
  simp only [Finset.mul_sum]
  exact hasSum_sum fun F hF => hasSum_flowerKernelGen_dagger L γ δ p haP hd hL (Finset.mem_filter.1 hF).2.1
    pat cut1 cut2 t s k k'

end Kernels

/-! ## Support of the `†` terms -/

section Support

variable (L γ δ : ℝ) (p : ℕ)

theorem flowerLeaf_not_mem_leavesBelow {F : FTree} (hF : F ≠ flower) {m : Fin 3} (hm : m ≠ flowerSlot hF) :
    F.flowerLeaf ∉ ((F.flowerParent hF).child m).leavesBelow := by
  intro h
  simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have h2 : ((F.flowerParent hF).child m).1.2 <+: F.flowerLeaf.toNode.1.2 := h.2
  rw [← flowerParent_child_flowerSlot hF] at h2
  simp only [flowerParent_child_path] at h2
  have := List.prefix_append_right_inj (F.flowerPath.dropLast) |>.1 h2
  rw [List.cons_prefix_cons] at this
  exact hm this.1

/-- **Sibling momenta are bounded by the `M₁` cutoff.** -/
theorem norm_sibling_lt {F : FTree} (hF : F ≠ flower) (hL : 0 < L) {j : ℕ} {k k' : Fin d → ℤ}
    (κ : FlowerDecoration F d k k') (hcut : treeCut1 L F j κ.1.1 ≠ 0) {m : Fin 3} (hm : m ≠ flowerSlot hF) :
    ‖latticePoint L (κ.1.1 ((F.flowerParent hF).child m))‖ <
      (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j * L) := by
  classical
  set x : NNReal := (Finset.univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ.1.1 ℓ.toNode)‖₊
  have hx : (x : ℝ) < 2 ^ j * L := lt_of_dyadicCut_ne_zero hL (NNReal.coe_nonneg _) hcut
  set a := (F.flowerParent hF).child m
  have hrule := sum_rule (fun _ : Fin 1 => (1 : ℤˣ)) κ.1.1 κ.1.2.1 a
  have hb : ∀ ℓ ∈ a.leavesBelow, ‖latticePoint L
      (((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) ℓ.1 : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode)‖ ≤ x := fun ℓ hℓ => by
    have hne : ℓ ≠ F.flowerLeaf := fun e => flowerLeaf_not_mem_leavesBelow hF hm (e ▸ hℓ)
    have hle := Finset.le_sup (f := fun ℓ => ‖latticePoint L (κ.1.1 ℓ.toNode)‖₊)
      (Finset.mem_erase.2 ⟨hne, Finset.mem_univ ℓ⟩)
    calc _ = ‖latticePoint L (κ.1.1 ℓ.toNode)‖ := by
          rw [latticePoint_zsmul]
          rcases Int.units_eq_one_or (nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) ℓ.1) with h | h <;> simp [h]
      _ ≤ x := by exact_mod_cast hle
  have hsum : ‖latticePoint L (((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) a.1 : ℤˣ) : ℤ) • κ.1.1 a)‖ ≤
      (a.leavesBelow.card : ℝ) * x := by
    rw [hrule, latticePoint_sum]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul _ _ _ hb
    rwa [nsmul_eq_mul] at this
  have hlhs : ‖latticePoint L (((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) a.1 : ℤˣ) : ℤ) • κ.1.1 a)‖ =
      ‖latticePoint L (κ.1.1 a)‖ := by
    rw [latticePoint_zsmul]
    rcases Int.units_eq_one_or (nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) a.1) with h | h <;> simp [h]
  have hcard : (a.leavesBelow.card : ℝ) ≤ Fintype.card (GLeaf (single F.toTree)) := by
    exact_mod_cast Finset.card_le_univ _
  have hx0 : (0 : ℝ) ≤ x := NNReal.coe_nonneg _
  have h2 : (0 : ℝ) < 2 ^ j * L := by positivity
  have hcpos : (0 : ℝ) < Fintype.card (GLeaf (single F.toTree)) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨F.flowerLeaf⟩
  rw [← hlhs]
  calc _ ≤ (a.leavesBelow.card : ℝ) * x := hsum
    _ ≤ (Fintype.card (GLeaf (single F.toTree)) : ℝ) * x := by gcongr
    _ < _ := by gcongr

/-- **The `†` term vanishes off the sibling box.** -/
theorem flowerKernelGen_dagger_eq_zero (hd : 0 < d) (hL : 0 < L) {F : FTree} (aP : (Fin d → ℤ) → ℂ)
    (pat : FixPat) (cut2 : Option ℕ) (j : ℕ) (t s : ℝ) {k k' : Fin d → ℤ} (x : DagIdx d)
    (hx : ∃ m, m ≠ x.1 ∧ (Fintype.card (GLeaf (single F.toTree)) : ℝ) * (2 ^ j * L) ≤
      ‖latticePoint L (x.2.1 m)‖) :
    flowerKernelGen L γ δ p F aP pat (some (dagLabel L x)) (some j) cut2 t s k k' = 0 := by
  classical
  by_cases hF : F = flower
  · simp [flowerKernelGen, hF]
  rw [flowerKernelGen_eq L γ δ hF p]
  refine mul_eq_zero_of_right _ ((tsum_congr fun κ => ?_).trans tsum_zero)
  suffices hw : treeWeight L F hF (some (dagLabel L x)) (some j) cut2 κ.1.1 = 0 by simp [hw]
  rw [treeWeight_dagger, treeWeight_cut1]
  by_cases hsib : treeSib L F hF (dagLabel L x) κ.1.1 = 0
  · rw [hsib, mul_zero]
  by_cases hcut : treeCut1 L F j κ.1.1 = 0
  · rw [hcut, zero_mul, zero_mul]
  exfalso
  have hxe : x = dagIdxOf hF κ := by
    by_contra h
    exact hsib (treeSib_eq_zero L hF κ hd hL.ne' h)
  obtain ⟨m, hm, hbig⟩ := hx
  have hm' : m ≠ flowerSlot hF := by rw [hxe] at hm; exact hm
  have hval : x.2.1 m = κ.1.1 ((F.flowerParent hF).child m) := by
    rw [hxe]; simp [dagIdxOf, hm']
  have := norm_sibling_lt L hF hL κ hcut hm'
  rw [← hval] at this
  linarith

end Support

end WaveTurbulence.Fixedpt
