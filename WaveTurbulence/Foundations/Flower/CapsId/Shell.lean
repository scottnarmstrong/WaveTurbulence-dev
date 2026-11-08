/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Transport
public import WaveTurbulence.Foundations.Flower.FlShell.Product
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.CapsFub.Shell
/-! # A2 CAPS-ID: transport of the `M₂` shell weight to selected-face weights (`cutWeight2P → selWeightCap`)

By A4 FL-SHELL (`FlShell.cutWeight2P_eq_integral`), the positive shell `cutWeight2P L j₂` is an integral over per-tree
scales `R_j ∈ [2^{j₂-1}L, 2^{j₂}L]` of a sum over selected stem vertices `v_j`. On the capped garden each summand
is the selected-face weight `MkDefs.selWeightCap` with `v_j` transported and no selection at the caps
(`cutWeight2P_capLayered`).

The garden-dependent selections are then relabelled by their stem depths (B0's intrinsic `selCap`, weight `selOK`):
the stem of a tree is a chain, so a stem vertex is determined by its depth, and a requested depth without a stem
vertex has weight `0` (`sum_stemSet_eq_sum_depth`). `capW_coreG` gives the whole Core-G weight as an integral over
the shell box of a sum over depth labels `kk ∈ ∏_j range (M+1)` of `selOK · markedWeight`, i.e. exactly the integrand
of `MkAsm.CompData.val` with `kSel = capKSel kk`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset MeasureTheory Set WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {w d : ℕ}

/-- Selected vertices on the capped garden: `v j` in the original tree `j`, none at the caps. -/
def capSel (G : Garden w) (v : Fin w → GBranch G.tree) : Fin (2 * w) → Option (GBranch (capGarden G).tree) :=
  capExt (fun j => some (cBranch G (v j))) none

/-- The two copies of `χD u = -u χ₀'(u)` (A1 and A4) agree. -/
theorem mkDefs_chiD_eq_flShell_chiD : MkDefs.chiD = FlShell.chiD := rfl

/-- The selected-face weight of one transported selection (the scale `c₀` at the caps is never read). -/
theorem selWeightCap_capSel (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (v : Fin w → GBranch LG.garden.tree) (R : Fin w → ℝ) (c₀ : ℝ) (k : GNode (capGarden LG.garden).tree → Mom d) :
    selWeightCap (capLayered LG p) (capJ w) (capSel LG.garden v) (capExt R c₀) k =
      ∏ j : Fin w, (R j)⁻¹ * (FlShell.chiD (|omegaNode LG.garden (pullK LG.garden k) (v j)| / R j) *
        ∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden (pullK LG.garden k) b| / R j)) := by
  unfold selWeightCap
  rw [← (capσ w).prod_comp, Fintype.prod_sum_type]
  simp only [capSel, capExt_inr, Option.elim_none, Finset.prod_const_one, mul_one, capExt_inl,
    Option.elim_some]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [stemSetCap_inl LG p hF, ← Equiv.coe_toEmbedding, ← Finset.map_erase, Finset.prod_map]
  simp only [Equiv.coe_toEmbedding, omegaNode_cBranch, mkDefs_chiD_eq_flShell_chiD, mul_assoc]

/-- **Transport of the `M₂` shell**: `cutWeight2P → selWeightCap` (positive shell `0 < j₂`, `0 < L`). -/
theorem cutWeight2P_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (L : ℝ) (hL : 0 < L)
    (j₂ : ℕ) (hj : 0 < j₂) (k : GNode (capGarden LG.garden).tree → Mom d) :
    LG.cutWeight2P L j₂ (pullK LG.garden k) =
      ∫ R in Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)),
        ∑ v ∈ Fintype.piFinset (Cases.stemSet LG),
          selWeightCap (capLayered LG p) (capJ w) (capSel LG.garden v) (capExt R L) k := by
  rw [FlShell.cutWeight2P_eq_integral LG L hL j₂ hj]
  simp only [selWeightCap_capSel LG p hF]

/-- The capped weight of the Core-G integrand, in `markedWeight` form (no stem filters; selected vertices and
scales integrated as in FL-SHELL). Pointwise in the labelling. -/
theorem capW_coreG (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (L : ℝ) (hL : 0 < L)
    (j₂ : ℕ) (hj : 0 < j₂) (Rf : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (dagger : Option (Fin w → Fin 3 → Mom d)) (k : GNode (capGarden LG.garden).tree → Mom d) :
    capW LG dagger (fun k => Typed.frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P L j₂ k *
        Typed.leafProd LG h k) k =
      ∫ R in Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)),
        ∑ v ∈ Fintype.piFinset (Cases.stemSet LG),
          markedWeight (capLayered LG p) (capJ w) p L (capExt (fun j => some (Rf j)) none) (fun _ => none)
            (capSel LG.garden v) (capExt R L) (capH h) (capDag dagger) k := by
  unfold capW pullW
  dsimp only
  rw [cutWeight2P_capLayered LG p hF L hL j₂ hj k]
  have hst : stemFilterCap (capLayered LG p) (capJ w) L (fun _ => none) k = 1 := by
    simp [stemFilterCap]
  have hsib : (capDag dagger).elim 1 (fun c => sibWeightCap (capLayered LG p) (capJ w) c k) =
      dagger.elim 1 (fun c => LG.sibWeight c (pullK LG.garden k)) := by
    rcases dagger with _ | c
    · rfl
    · simp only [capDag, Option.map_some, Option.elim_some, sibWeightCap_capLayered LG p hF]
  have hmw : ∀ (R : Fin w → ℝ) (v : Fin w → GBranch LG.garden.tree),
      markedWeight (capLayered LG p) (capJ w) p L (capExt (fun j => some (Rf j)) none) (fun _ => none)
        (capSel LG.garden v) (capExt R L) (capH h) (capDag dagger) k =
      (Typed.frontierW LG p (fun j => some (Rf j)) (pullK LG.garden k) * Typed.leafProd LG h (pullK LG.garden k) *
        dagger.elim 1 (fun c => LG.sibWeight c (pullK LG.garden k))) *
        selWeightCap (capLayered LG p) (capJ w) (capSel LG.garden v) (capExt R L) k := by
    intro R v
    unfold markedWeight
    rw [frontierW_capLayered LG p hF hfl, hst, leafProdCap_capLayered LG p hF, hsib]
    ring
  simp only [hmw, ← Finset.mul_sum, integral_const_mul]
  ring

/-! ## Selections by stem depth (B0's `selCap`) -/

/-- Depth labels on the capped garden: label `kk j` on the original tree `j`, none at the caps. -/
def capKSel (kk : Fin w → ℕ) : Fin (2 * w) → Option ℕ := capExt (fun j => some (kk j)) none

theorem length_lt_order_of_mem_branching : ∀ (t : TTree) {q : TTree.Path}, q ∈ t.branching → q.length < t.order
  | .leaf, q, h => by simp [TTree.branching] at h
  | .node l m r, q, h => by
    simp only [TTree.branching, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | ((h | h) | h)
    · simp [TTree.order]
    · obtain ⟨q', hq', rfl⟩ := TTree.mem_pre.1 h
      have := length_lt_order_of_mem_branching l hq'
      simp only [TTree.order, List.length_cons]; omega
    · obtain ⟨q', hq', rfl⟩ := TTree.mem_pre.1 h
      have := length_lt_order_of_mem_branching m hq'
      simp only [TTree.order, List.length_cons]; omega
    · obtain ⟨q', hq', rfl⟩ := TTree.mem_pre.1 h
      have := length_lt_order_of_mem_branching r hq'
      simp only [TTree.order, List.length_cons]; omega

/-- Stem depths are below the garden order (so `M = N` works on the carrier). -/
theorem stemSet_length_le_order (LG : LayeredGarden w) (j : Fin w) (b : GBranch LG.garden.tree)
    (_hb : b ∈ Cases.stemSet LG j) : b.1.2.length ≤ LG.garden.order := by
  have h1 := length_lt_order_of_mem_branching _ b.2
  have h2 : (LG.garden.tree b.1.1).order ≤ LG.garden.order := by
    unfold Garden.order
    exact Finset.single_le_sum (f := fun j => (LG.garden.tree j).order) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ _)
  omega

/-- A stem vertex is determined by its depth (the stem is a chain of prefixes of the flower's path). -/
theorem stemSet_eq_of_length (LG : LayeredGarden w) (hF : OneFlower LG.garden) {j : Fin w}
    {b b' : GBranch LG.garden.tree} (hb : b ∈ Cases.stemSet LG j) (hb' : b' ∈ Cases.stemSet LG j)
    (hl : b.1.2.length = b'.1.2.length) : b = b' := by
  simp only [Cases.stemSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
  obtain ⟨hj, ⟨ℓ, hℓ, hd⟩, -⟩ := hb
  obtain ⟨hj', ⟨ℓ', hℓ', hd'⟩, -⟩ := hb'
  have e1 : ℓ.1.1 = j := hd.1.symm.trans hj
  have e2 : ℓ'.1.1 = j := hd'.1.symm.trans hj'
  have hℓℓ' : ℓ = ℓ' := (hF j).unique ⟨e1, hℓ⟩ ⟨e2, hℓ'⟩
  subst hℓℓ'
  have hp : b.1.2 = b'.1.2 := (List.prefix_of_prefix_length_le hd.2 hd'.2 hl.le).eq_of_length hl
  exact Subtype.ext (Prod.ext (hj.trans hj'.symm) hp)

theorem stemAt_eq_some_of {w' : ℕ} (LG' : LayeredGarden w') (J : Finset (Fin w')) (j : Fin w') (k : ℕ)
    (b : GBranch LG'.garden.tree) (h : ((stemSetCap LG' J j).filter fun x => x.1.2.length = k) = {b}) :
    stemAt LG' J j k = some b := by
  unfold stemAt
  have hc : ((stemSetCap LG' J j).filter fun x => x.1.2.length = k).card = 1 := by rw [h]; rfl
  rw [dite_eq_left hc]
  congr 1
  have hs := Classical.choose_spec (Finset.card_eq_one.mp hc)
  exact (Finset.singleton_injective (h.symm.trans hs)).symm

theorem stemAt_spec {w' : ℕ} (LG' : LayeredGarden w') (J : Finset (Fin w')) (j : Fin w') (k : ℕ)
    (b : GBranch LG'.garden.tree) (h : stemAt LG' J j k = some b) :
    b ∈ stemSetCap LG' J j ∧ b.1.2.length = k := by
  unfold stemAt at h
  split_ifs at h with hc
  cases h
  have hs := Classical.choose_spec (Finset.card_eq_one.mp hc)
  have hm := (Finset.eq_singleton_iff_unique_mem.1 hs).1
  exact (Finset.mem_filter.1 hm)

/-- The capped stem vertex of an original tree at the depth of a stem vertex `v` is `v`. -/
theorem stemAt_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (j : Fin w)
    (v : GBranch LG.garden.tree) (hv : v ∈ Cases.stemSet LG j) :
    stemAt (capLayered LG p) (capJ w) (capσ w (.inl j)) v.1.2.length = some (cBranch LG.garden v) := by
  apply stemAt_eq_some_of
  rw [stemSetCap_inl LG p hF]
  ext b
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_singleton]
  simp only [cBranch_val]
  constructor
  · rintro ⟨hb, hl⟩
    rw [stemSet_eq_of_length LG hF hb hv hl]
  · intro h
    obtain rfl := (cBranch LG.garden).injective h
    exact ⟨hv, rfl⟩

theorem stemAt_capLayered_spec (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (j : Fin w) (k : ℕ)
    (b : GBranch (capLayered LG p).garden.tree) (h : stemAt (capLayered LG p) (capJ w) (capσ w (.inl j)) k = some b) :
    ∃ v ∈ Cases.stemSet LG j, v.1.2.length = k ∧ b = cBranch LG.garden v := by
  obtain ⟨hm, hl⟩ := stemAt_spec _ _ _ _ _ h
  rw [stemSetCap_inl LG p hF] at hm
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hm
  refine ⟨b, hm, ?_, rfl⟩
  simpa only [cBranch_val] using hl

/-- The depth selection at the depths of a stem selection `v` is the transported selection of `v`. -/
theorem selCap_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (v : Fin w → GBranch LG.garden.tree)
    (hv : v ∈ Fintype.piFinset (Cases.stemSet LG)) :
    selCap (capLayered LG p) (capJ w) (capKSel fun j => (v j).1.2.length) = capSel LG.garden v := by
  funext c
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · simp only [selCap, capKSel, capSel, capExt_inl, Option.bind_some]
    exact stemAt_capLayered LG p hF j (v j) (Fintype.mem_piFinset.1 hv j)
  · simp only [selCap, capKSel, capSel, capExt_inr, Option.bind_none]

theorem selOK_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (v : Fin w → GBranch LG.garden.tree)
    (hv : v ∈ Fintype.piFinset (Cases.stemSet LG)) :
    selOK (capLayered LG p) (capJ w) (capKSel fun j => (v j).1.2.length) = 1 := by
  unfold selOK
  rw [selCap_depth LG p hF v hv]
  refine ite_eq_left fun c _ => ?_
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · simp [capSel]
  · simp [capKSel] at *

/-- **Relabelling by stem depth.** A sum over stem selections `v ∈ ∏_j stemSet j` is the sum over depth labels
`kk ∈ ∏_j range (M+1)` of `selOK · F(selCap kk)` (B0's intrinsic selection), for any depth bound `M`. -/
theorem sum_stemSet_eq_sum_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (M : ℕ)
    (hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ M)
    (F : (Fin (2 * w) → Option (GBranch (capGarden LG.garden).tree)) → ℝ) :
    ∑ v ∈ Fintype.piFinset (Cases.stemSet LG), F (capSel LG.garden v) =
      ∑ kk ∈ Fintype.piFinset (fun _ : Fin w => Finset.range (M + 1)),
        selOK (capLayered LG p) (capJ w) (capKSel kk) * F (selCap (capLayered LG p) (capJ w) (capKSel kk)) := by
  refine Finset.sum_bij_ne_zero (fun v _ _ => fun j => (v j).1.2.length) ?_ ?_ ?_ ?_
  · intro v hv _
    rw [Fintype.mem_piFinset] at hv ⊢
    exact fun j => Finset.mem_range.2 (Nat.lt_succ_of_le (hM j _ (hv j)))
  · intro v₁ hv₁ _ v₂ hv₂ _ he
    funext j
    exact stemSet_eq_of_length LG hF (Fintype.mem_piFinset.1 hv₁ j) (Fintype.mem_piFinset.1 hv₂ j)
      (congrFun he j)
  · intro kk _ hne
    have hok : ∀ c, (capKSel kk c).isSome → (selCap (capLayered LG p) (capJ w) (capKSel kk) c).isSome := by
      by_contra hc
      apply hne
      have h0 : selOK (capLayered LG p) (capJ w) (capKSel kk) = 0 := by
        unfold selOK; exact ite_eq_right hc
      rw [h0, zero_mul]
    have hex : ∀ j, ∃ v ∈ Cases.stemSet LG j, v.1.2.length = kk j := by
      intro j
      have h1 := hok (capσ w (.inl j)) (by simp [capKSel])
      simp only [selCap, capKSel, capExt_inl, Option.bind_some] at h1
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h1
      obtain ⟨v, hv, hl, -⟩ := stemAt_capLayered_spec LG p hF j (kk j) b hb
      exact ⟨v, hv, hl⟩
    choose v hv hl using hex
    have hvmem : v ∈ Fintype.piFinset (Cases.stemSet LG) := Fintype.mem_piFinset.2 hv
    have hdepth : (fun j => (v j).1.2.length) = kk := funext hl
    refine ⟨v, hvmem, ?_, hdepth⟩
    intro h0
    apply hne
    rw [← hdepth, selCap_depth LG p hF v hvmem, h0, mul_zero]
  · intro v hv _
    rw [selOK_depth LG p hF v hv, one_mul, selCap_depth LG p hF v hv]

/-- **Transport of the `M₂` shell, depth form**: `cutWeight2P` as an integral over the shell box of a sum over depth
labels of `selOK · selWeightCap` (B0's intrinsic selection). -/
theorem cutWeight2P_capLayered_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (L : ℝ) (hL : 0 < L)
    (j₂ : ℕ) (hj : 0 < j₂) (M : ℕ) (hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ M)
    (k : GNode (capGarden LG.garden).tree → Mom d) :
    LG.cutWeight2P L j₂ (pullK LG.garden k) =
      ∫ R in Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)),
        ∑ kk ∈ Fintype.piFinset (fun _ : Fin w => Finset.range (M + 1)),
          selOK (capLayered LG p) (capJ w) (capKSel kk) *
            selWeightCap (capLayered LG p) (capJ w) (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) k := by
  rw [cutWeight2P_capLayered LG p hF L hL j₂ hj k]
  congr 1
  funext R
  exact sum_stemSet_eq_sum_depth LG p hF M hM (fun v' => selWeightCap (capLayered LG p) (capJ w) v' (capExt R L) k)

/-- **The Core-G weight in `CompData` form**: an integral over the shell box of a sum over depth labels
`kk ∈ ∏_j range (M+1)` of `selOK · markedWeight` at `kSel = capKSel kk` (no stem filters), pointwise in the
labelling. -/
theorem capW_coreG_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (L : ℝ) (hL : 0 < L)
    (j₂ : ℕ) (hj : 0 < j₂) (M : ℕ) (hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ M) (Rf : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (dagger : Option (Fin w → Fin 3 → Mom d))
    (k : GNode (capGarden LG.garden).tree → Mom d) :
    capW LG dagger (fun k => Typed.frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P L j₂ k *
        Typed.leafProd LG h k) k =
      ∫ R in Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)),
        ∑ kk ∈ Fintype.piFinset (fun _ : Fin w => Finset.range (M + 1)),
          selOK (capLayered LG p) (capJ w) (capKSel kk) *
            markedWeight (capLayered LG p) (capJ w) p L (capExt (fun j => some (Rf j)) none) (fun _ => none)
              (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) (capH h) (capDag dagger) k := by
  rw [capW_coreG LG p hF hfl L hL j₂ hj Rf h dagger k]
  congr 1
  funext R
  exact sum_stemSet_eq_sum_depth LG p hF M hM (fun v' => markedWeight (capLayered LG p) (capJ w) p L
    (capExt (fun j => some (Rf j)) none) (fun _ => none) v' (capExt R L) (capH h) (capDag dagger) k)

/-! ## At a fixed shell scale `R` (to compose with CAPS-FUBINI's `coreG_shell_exchange`) -/

/-- CAPS-FUBINI's shell integrand at a fixed scale vector `R`, on the capped garden: a sum over depth labels of
`selOK · selWeightCap` (B0's intrinsic selection). -/
theorem shellIntegrand_capLayered_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (L : ℝ) (M : ℕ)
    (hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ M) (R : Fin w → ℝ)
    (k : GNode (capGarden LG.garden).tree → Mom d) :
    CapsFub.shellIntegrand LG L (pullK LG.garden k) R =
      ∑ kk ∈ Fintype.piFinset (fun _ : Fin w => Finset.range (M + 1)),
        selOK (capLayered LG p) (capJ w) (capKSel kk) *
          selWeightCap (capLayered LG p) (capJ w) (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) k := by
  unfold CapsFub.shellIntegrand
  simp only [← selWeightCap_capSel LG p hF _ R L k]
  exact sum_stemSet_eq_sum_depth LG p hF M hM (fun v' => selWeightCap (capLayered LG p) (capJ w) v' (capExt R L) k)

/-- **The Core-G weight at a fixed shell scale `R`, in `CompData` form**: with CAPS-FUBINI's integrand
(`coreG_shell_exchange`), the capped weight is the sum over depth labels `kk ∈ ∏_j range (M+1)` of
`selOK · markedWeight` at `kSel = capKSel kk`, scales `capExt R L` (no stem filters). -/
theorem capW_shell_depth (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (L : ℝ) (M : ℕ)
    (hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ M) (Rf : Fin w → ℝ) (R : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (dagger : Option (Fin w → Fin 3 → Mom d)) :
    capW LG dagger (fun k => Typed.frontierW LG p (fun j => some (Rf j)) k * CapsFub.shellIntegrand LG L k R *
        Typed.leafProd LG h k) =
      fun k => ∑ kk ∈ Fintype.piFinset (fun _ : Fin w => Finset.range (M + 1)),
        selOK (capLayered LG p) (capJ w) (capKSel kk) *
          markedWeight (capLayered LG p) (capJ w) p L (capExt (fun j => some (Rf j)) none) (fun _ => none)
            (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) (capH h) (capDag dagger) k := by
  funext k
  unfold capW pullW
  dsimp only
  rw [shellIntegrand_capLayered_depth LG p hF L M hM R k]
  have hst : stemFilterCap (capLayered LG p) (capJ w) L (fun _ => none) k = 1 := by
    simp [stemFilterCap]
  have hsib : (capDag dagger).elim 1 (fun c => sibWeightCap (capLayered LG p) (capJ w) c k) =
      dagger.elim 1 (fun c => LG.sibWeight c (pullK LG.garden k)) := by
    rcases dagger with _ | c
    · rfl
    · simp only [capDag, Option.map_some, Option.elim_some, sibWeightCap_capLayered LG p hF]
  have hmw : ∀ kk : Fin w → ℕ,
      selOK (capLayered LG p) (capJ w) (capKSel kk) *
        markedWeight (capLayered LG p) (capJ w) p L (capExt (fun j => some (Rf j)) none) (fun _ => none)
          (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) (capH h) (capDag dagger) k =
      (Typed.frontierW LG p (fun j => some (Rf j)) (pullK LG.garden k) * Typed.leafProd LG h (pullK LG.garden k) *
        dagger.elim 1 (fun c => LG.sibWeight c (pullK LG.garden k))) *
        (selOK (capLayered LG p) (capJ w) (capKSel kk) *
          selWeightCap (capLayered LG p) (capJ w) (selCap (capLayered LG p) (capJ w) (capKSel kk)) (capExt R L) k) := by
    intro kk
    unfold markedWeight
    rw [frontierW_capLayered LG p hF hfl, hst, leafProdCap_capLayered LG p hF, hsib]
    ring
  simp only [hmw, ← Finset.mul_sum]
  ring

end WaveTurbulence.Flower.CapsId
