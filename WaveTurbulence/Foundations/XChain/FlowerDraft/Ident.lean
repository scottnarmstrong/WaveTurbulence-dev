/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.Ops

/-!
# The parametrix identities `(1−ℒ₁)𝒳 = 1 − 𝒴`, `𝒳(1−ℒ₁) = 1 − 𝒲` (packet X1; `GAP.operatorIdent`)

Here `ℒ₁` is snapshot 5's `Lop … 1` with `Ntr = N`. The operators, on arrays over `[p, p+1]`:
* `Xop b = b + ∑_{F ∈ Xset N} 𝒥_F[b]`. This is the parametrix with its identity term (F39; DH23 (kernelexp)).
* `Yop b = ∑_{(Y-1),(Y-2)} 𝒥_F[b]`, `Wop b = ∑_{(W-1)–(W-3)} 𝒥_F[b]`.

**Theorems** (for good `b`, summable data `a(p)`):
- `one_sub_L1op_Xop`: `𝒳b − ℒ₁(𝒳b) = b − 𝒴b`;
- `Xop_one_sub_L1op`: `𝒳(b − ℒ₁b) = b − 𝒲b`.

TARGET L2273 writes `𝒴 = (1−ℒ₁)𝒳 − 1`, `𝒲 = 𝒳(1−ℒ₁) − 1` and says they "have the same expression" as `𝒳`. Here
`(1−ℒ₁)𝒳 − 1 = −Yop` and `𝒳(1−ℒ₁) − 1 = −Wop`. So the kernels of `𝒴`, `𝒲` are `−∑ 𝒥̃_𝒯` over the (Y)/(W)
classes. The sign is irrelevant to the norm bounds, but it matters for exact identities (FLOWER-DESIGN.md).

**Proof.** `ℒ₁ b = ∑_{(i, T₁, T₂)} 𝒥_{node i 𝔣 T₁ T₂}[b]`: one `b`-slot, the two `𝒥`-slots expanded over trees of
order `≤ N` (`L1op_eq`). Then:
- `(Y)`: `ℒ₁` grafts at the root, `ℒ₁ 𝒥_F[b] = ∑ 𝒥_{node i F T₁ T₂}[b]`, and `sum_Rind`.
- `(W)`: `𝒥_F[ℒ₁ b] = ∑ 𝒥_{F.graft (node i 𝔣 T₁ T₂)}[b]` (`fOp_graft`), and `sum_Wind'`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

/-! ## `ℒ₁` as a sum over the flower trees of height one -/

/-- Trees of order `≤ N`, by order. -/
theorem sum_treesLE {M : Type*} [AddCommMonoid M] (N : ℕ) (g : TTree → M) :
    ∑ a : Fin (N + 1), ∑ T ∈ treesOfOrder a, g T = ∑ T ∈ treesLE N, g T := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ T ∈ treesOfOrder a, g T) (N + 1),
    ← Finset.sum_fiberwise_of_maps_to (s := treesLE N) (t := range (N + 1)) (g := TTree.order)
      (fun T hT => Finset.mem_range.2 (Nat.lt_succ_of_le (mem_treesLE.1 hT)))]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr ?_ fun _ _ => rfl
  rw [Finset.mem_range] at ha
  ext T
  simp only [Finset.mem_filter, mem_treesLE, mem_treesOfOrder]
  omega

/-- The slot triples with exactly one `b`-slot. -/
theorem sum_count_one {M : Type*} [AddCommMonoid M] (Ntr : ℕ)
    (G : Slot Ntr × Slot Ntr × Slot Ntr → M) :
    ∑ x ∈ (univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = 1 ∧ (1 = 0 → Ntr ≤ slotOrder x)), G x =
      ∑ a : Fin (Ntr + 1), ∑ c : Fin (Ntr + 1),
        (G (none, some a, some c) + G (some a, none, some c) + G (some a, some c, none)) := by
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, slotCountB, List.count_cons, List.count_nil,
    reduceCtorEq, beq_iff_eq, ↓reduceIte, one_ne_zero, IsEmpty.forall_iff,
    and_true, Finset.sum_add_distrib]
  simp
  abel

variable (L γ δ : ℝ) {d : ℕ}

/-- Multilinearity of the slot form in the two `𝒥`-slots. -/
theorem slotNonlin_sum_vw (i : Fin 3) (s : ℝ) {ι₁ ι₂ : Type*} (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (u : (Fin d → ℤ) → ℂ) (v : ι₁ → (Fin d → ℤ) → ℂ) (w : ι₂ → (Fin d → ℤ) → ℂ)
    (hu : Summable fun k => ‖u k‖) (hv : ∀ j, Summable fun k => ‖v j k‖)
    (hw : ∀ j, Summable fun k => ‖w j k‖) (n : Fin d → ℤ) :
    slotNonlin L γ δ i s u (fun k => ∑ j ∈ S₁, v j k) (fun k => ∑ j ∈ S₂, w j k) n =
      ∑ j₁ ∈ S₁, ∑ j₂ ∈ S₂, slotNonlin L γ δ i s u (v j₁) (w j₂) n := by
  have hu' : ∀ _ : Unit, Summable fun k => ‖u k‖ := fun _ => hu
  have hvc : ∀ j, Summable fun k => ‖(starRingEnd ℂ) (v j k)‖ := fun j => by simpa using hv j
  have hwc : ∀ j, Summable fun k => ‖(starRingEnd ℂ) (w j k)‖ := fun j => by simpa using hw j
  have huc : ∀ _ : Unit, Summable fun k => ‖(starRingEnd ℂ) (u k)‖ := fun _ => by simpa using hu
  fin_cases i
  · simp only [Fin.zero_eta, slotNonlin_zero, map_sum]
    have h := aNonlin_sum L γ δ 1 s (univ : Finset Unit) S₁ S₂ (fun _ => u)
      (fun j k => (starRingEnd ℂ) (v j k)) w hu' hvc hw n
    simpa using h
  · simp only [Fin.mk_one, slotNonlin_one]
    have h := aNonlin_sum L γ δ 1 s S₁ (univ : Finset Unit) S₂ v
      (fun _ k => (starRingEnd ℂ) (u k)) w hv huc hw n
    simpa using h
  · simp only [Fin.reduceFinMk, slotNonlin_two, map_sum]
    have h := aNonlin_sum L γ δ 1 s S₁ S₂ (univ : Finset Unit) v
      (fun j k => (starRingEnd ℂ) (w j k)) (fun _ => u) hv hwc hu' n
    simpa using h

/-- The flower trees of height one with the flower in slot `i`. -/
noncomputable def Rind1 (N : ℕ) : Finset (Fin 3 × TTree × TTree) :=
  (Finset.univ : Finset (Fin 3)) ×ˢ treesLE N ×ˢ treesLE N

/-- Regrouping the slot sum over the trees of the two `𝒥`-slots. -/
theorem sum_regroup {M : Type*} [AddCommMonoid M] (N : ℕ) (g : Fin 3 → TTree → TTree → M) :
    ∑ a : Fin (N + 1), ∑ c : Fin (N + 1), ∑ i : Fin 3, ∑ T₁ ∈ treesOfOrder a,
      ∑ T₂ ∈ treesOfOrder c, g i T₁ T₂ = ∑ x ∈ Rind1 N, g x.1 x.2.1 x.2.2 := by
  rw [Rind1, Finset.sum_product]
  have hR : ∀ i : Fin 3, ∑ y ∈ treesLE N ×ˢ treesLE N, g i y.1 y.2 =
      ∑ T₁ ∈ treesLE N, ∑ T₂ ∈ treesLE N, g i T₁ T₂ := fun i => Finset.sum_product _ _ _
  simp only [hR]
  calc ∑ a : Fin (N + 1), ∑ c : Fin (N + 1), ∑ i : Fin 3, ∑ T₁ ∈ treesOfOrder a,
        ∑ T₂ ∈ treesOfOrder c, g i T₁ T₂
      = ∑ a : Fin (N + 1), ∑ i : Fin 3, ∑ c : Fin (N + 1), ∑ T₁ ∈ treesOfOrder a,
          ∑ T₂ ∈ treesOfOrder c, g i T₁ T₂ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ a : Fin (N + 1), ∑ c : Fin (N + 1), ∑ T₁ ∈ treesOfOrder a,
          ∑ T₂ ∈ treesOfOrder c, g i T₁ T₂ := Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ a : Fin (N + 1), ∑ T₁ ∈ treesOfOrder a, ∑ c : Fin (N + 1),
          ∑ T₂ ∈ treesOfOrder c, g i T₁ T₂ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ T₁ ∈ treesLE N, ∑ T₂ ∈ treesLE N, g i T₁ T₂ := by
        simp only [sum_treesLE]

/-- **`ℒ₁` as a sum over the flower trees of height one** (T (eqnbk1.5); DH21 Prop 11.2). -/
theorem Lop_one_eq (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) (t : Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr aP 1 b t n =
      ∑ x ∈ Rind1 Ntr, fOp L γ δ p aP (node x.1 flower x.2.1 x.2.2) b t n := by
  obtain ⟨U, hU, hU0, hbU⟩ := hb.maj
  have hbs : ∀ s, Summable fun k => ‖Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k‖ :=
    fun s => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbU _ k) hU
  -- one `b`-slot, two `𝒥_N`-slots, each `𝒥_N` a sum over trees
  have hslot : ∀ (i : Fin 3) (a c : Fin (Ntr + 1)),
      ∫ s in (p : ℝ)..t, slotNonlin L γ δ i s (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s)
        (treeTermN L γ δ p a aP s) (treeTermN L γ δ p c aP s) n =
      ∑ T₁ ∈ treesOfOrder a, ∑ T₂ ∈ treesOfOrder c,
        fOp L γ δ p aP (node i flower T₁ T₂) b t n := by
    intro i a c
    have hexp : ∀ s, slotNonlin L γ δ i s (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s)
        (treeTermN L γ δ p a aP s) (treeTermN L γ δ p c aP s) n =
        ∑ T₁ ∈ treesOfOrder a, ∑ T₂ ∈ treesOfOrder c, slotNonlin L γ δ i s
          (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s) (treeTerm L γ δ p T₁ aP s)
          (treeTerm L γ δ p T₂ aP s) n := by
      intro s
      have e1 : treeTermN L γ δ p a aP s = fun k => ∑ T ∈ treesOfOrder a, treeTerm L γ δ p T aP s k :=
        funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
      have e2 : treeTermN L γ δ p c aP s = fun k => ∑ T ∈ treesOfOrder c, treeTerm L γ δ p T aP s k :=
        funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
      rw [e1, e2]
      exact slotNonlin_sum_vw L γ δ i s _ _ _ (fun T => treeTerm L γ δ p T aP s)
        (fun T => treeTerm L γ δ p T aP s) (hbs s) (fun T => summable_norm_treeTerm L γ δ p T haP s)
        (fun T => summable_norm_treeTerm L γ δ p T haP s) n
    rw [intervalIntegral.integral_congr fun s _ => hexp s,
      intervalIntegral.integral_finsetSum fun T₁ _ => ?_]
    · refine Finset.sum_congr rfl fun T₁ _ => ?_
      rw [intervalIntegral.integral_finsetSum fun T₂ _ =>
        intervalIntegrable_slot L γ δ p haP i T₁ T₂ hb t.2 n]
      rfl
    · have h := IntervalIntegrable.sum (treesOfOrder c) fun T₂ _ =>
        intervalIntegrable_slot L γ δ p haP i T₁ T₂ hb t.2 n
      convert h using 1
      funext s
      simp [Finset.sum_apply]
  rw [Lop_eq_sum, sum_count_one]
  have hG : ∀ a c : Fin (Ntr + 1),
      (∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b none s)
          (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b (some a) s m))
          (slotVal L γ δ p Ntr aP b (some c) s) n) +
        (∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b (some a) s)
          (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b none s m))
          (slotVal L γ δ p Ntr aP b (some c) s) n) +
        (∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b (some a) s)
          (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b (some c) s m))
          (slotVal L γ δ p Ntr aP b none s) n) =
      ∑ i : Fin 3, ∫ s in (p : ℝ)..t, slotNonlin L γ δ i s
        (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s)
        (treeTermN L γ δ p a aP s) (treeTermN L γ δ p c aP s) n := by
    intro a c
    rw [Fin.sum_univ_three]
    simp only [slotNonlin_zero, slotNonlin_one, slotNonlin_two, slotVal]
  simp only [hG, hslot]
  exact sum_regroup Ntr fun i T₁ T₂ => fOp L γ δ p aP (node i flower T₁ T₂) b t n

/-! ## The operators and the identities -/

/-- `ℒ₁` on arrays over `[p, p+1]` (snapshot 5's `Lop … 1`, as used in B1.3 `fixedpoint`). -/
noncomputable def L1op (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d) : ArrI p d :=
  fun t n => Lop L γ δ p Ntr aP 1 b t n

/-- **The parametrix `𝒳 = 1 + ∑_{1 ≤ n(F) ≤ N} 𝒥_F`** (T (operatorx), (operatorxker), with the identity
term of DH23 (kernelexp); F39). -/
noncomputable def Xop (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d) : ArrI p d :=
  b + ∑ F ∈ Xset N, fOp L γ δ p aP F b

/-- `−𝒴`: the sum of `𝒥_F` over the class (Y-1), (Y-2). -/
noncomputable def Yop (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d) : ArrI p d :=
  ∑ x ∈ Yind N, fOp L γ δ p aP (rootOf x) b

/-- `−𝒲`: the sum of `𝒥_F` over the class (W-1)–(W-3). -/
noncomputable def Wop (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : ArrI p d) : ArrI p d :=
  ∑ x ∈ Wind N, fOp L γ δ p aP (bottomOf x) b

variable (p N : ℕ) {aP : (Fin d → ℤ) → ℂ}

theorem L1op_eq (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    L1op L γ δ p N aP b = ∑ x ∈ Rind1 N, fOp L γ δ p aP (node x.1 flower x.2.1 x.2.2) b := by
  funext t n
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Lop_one_eq L γ δ p N haP hb t n

theorem good_L1op (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    Good p (L1op L γ δ p N aP b) := by
  rw [L1op_eq L γ δ p N haP hb]
  exact Good.sum _ fun x _ => good_fOp L γ δ p haP hb _

theorem good_Xop (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    Good p (Xop L γ δ p N aP b) :=
  hb.add (Good.sum _ fun F _ => good_fOp L γ δ p haP hb F)

theorem ftreesLE_eq (N : ℕ) : ftreesLE N = insert flower (Xset N) := by
  ext F
  simp only [Finset.mem_insert, Xset, Finset.mem_filter, mem_ftreesLE]
  constructor
  · intro h
    by_cases hF : F = flower
    · exact Or.inl hF
    · exact Or.inr ⟨h, hF⟩
  · rintro (rfl | ⟨h, -⟩)
    · simp [order]
    · exact h

theorem flower_not_mem_Xset (N : ℕ) : flower ∉ Xset N := by simp [Xset]

/-- **`(1 − ℒ₁)𝒳 = 1 − 𝒴`** (T L2273; `GAP.operatorIdent`, first identity). -/
theorem one_sub_L1op_Xop (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    Xop L γ δ p N aP b - L1op L γ δ p N aP (Xop L γ δ p N aP b) = b - Yop L γ δ p N aP b := by
  have hX := good_Xop L γ δ p N haP hb
  have hstep : ∀ x : Fin 3 × TTree × TTree,
      fOp L γ δ p aP (node x.1 flower x.2.1 x.2.2) (Xop L γ δ p N aP b) =
        ∑ F ∈ ftreesLE N, fOp L γ δ p aP (node x.1 F x.2.1 x.2.2) b := by
    intro x
    unfold Xop
    rw [fOp_add L γ δ p haP hb (Good.sum _ fun F _ => good_fOp L γ δ p haP hb F),
      fOp_sum L γ δ p haP _ (fun F _ => good_fOp L γ δ p haP hb F), ftreesLE_eq,
      Finset.sum_insert (flower_not_mem_Xset N)]
    congr 1
  have hR : ∑ x ∈ Rind1 N, ∑ F ∈ ftreesLE N, fOp L γ δ p aP (node x.1 F x.2.1 x.2.2) b =
      ∑ y ∈ Rind N, fOp L γ δ p aP (rootOf y) b := by
    rw [Rind1, Rind, Finset.sum_product, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_product (s := ftreesLE N), Finset.sum_comm]
    rfl
  rw [L1op_eq L γ δ p N haP hX, Finset.sum_congr rfl fun x _ => hstep x, hR,
    sum_Rind N fun G => fOp L γ δ p aP G b]
  unfold Xop Yop
  abel

/-- **`𝒳(1 − ℒ₁) = 1 − 𝒲`** (T L2273; `GAP.operatorIdent`, second identity). -/
theorem Xop_one_sub_L1op (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    Xop L γ δ p N aP (b - L1op L γ δ p N aP b) = b - Wop L γ δ p N aP b := by
  have hL := good_L1op L γ δ p N haP hb
  have hstep : ∀ F : FTree, fOp L γ δ p aP F (L1op L γ δ p N aP b) =
      ∑ x ∈ Rind1 N, fOp L γ δ p aP (F.graft (node x.1 flower x.2.1 x.2.2)) b := by
    intro F
    rw [L1op_eq L γ δ p N haP hb, fOp_sum L γ δ p haP _ (fun x _ => good_fOp L γ δ p haP hb _)]
    exact Finset.sum_congr rfl fun x _ => fOp_graft L γ δ p aP F _ b
  have hW : L1op L γ δ p N aP b + ∑ F ∈ Xset N, fOp L γ δ p aP F (L1op L γ δ p N aP b) =
      ∑ G ∈ Xset N, fOp L γ δ p aP G b + Wop L γ δ p N aP b := by
    have h1 : L1op L γ δ p N aP b =
        ∑ x ∈ Rind1 N, fOp L γ δ p aP (flower.graft (node x.1 flower x.2.1 x.2.2)) b :=
      L1op_eq L γ δ p N haP hb
    rw [Finset.sum_congr rfl fun F _ => hstep F, h1, ← Finset.sum_insert (flower_not_mem_Xset N)
      (f := fun F => ∑ x ∈ Rind1 N, fOp L γ δ p aP (F.graft (node x.1 flower x.2.1 x.2.2)) b),
      ← ftreesLE_eq]
    have h2 : ∑ F ∈ ftreesLE N, ∑ x ∈ Rind1 N,
        fOp L γ δ p aP (F.graft (node x.1 flower x.2.1 x.2.2)) b =
        ∑ y ∈ Wind' N, fOp L γ δ p aP (bottomOf y) b := by
      rw [Wind', Finset.sum_product]
      rfl
    rw [h2, sum_Wind' N fun G => fOp L γ δ p aP G b]
    rfl
  unfold Xop
  rw [Finset.sum_congr rfl fun F _ => fOp_sub L γ δ p haP hb hL F, Finset.sum_sub_distrib,
    show ∀ x y z w : ArrI p d, x - y + (z - w) = x + z - (y + w) from fun x y z w => by abel, hW]
  abel

end WaveTurbulence.SysAPI
