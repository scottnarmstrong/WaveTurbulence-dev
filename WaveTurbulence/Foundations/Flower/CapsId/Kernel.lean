/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Decoration
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapKernel
public import WaveTurbulence.Foundations.FC23.FlowerSlices
/-! # A2 CAPS-ID: the kernel identity (supplement Lemma 2.2) and the capped form of `flowerWeighted`

`kernelKgen` of a flower garden `LG` with an arbitrary leaf input `F` equals `kernelKgen` of `capLayered LG p`
with input `1`, the same designated times, removed phases, upper caps and base vector (transported along the
branch bijection `cBranch`), and the weight pulled back along `embN` and multiplied by the original input product
(`kernelKgen_capLayered`). The flower-cap pairs carry input `1`, and caps add no time variable and no phase.

`flowerWeighted_eq_capSum` is the resulting identity for the frozen flower carrier. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7

variable {w d : ℕ}

/-! ## Transport of kernel data along the branch bijection -/

/-- Designated times on the capped garden. -/
def liftFix (G : Garden w) (fix : GBranch G.tree → Option ℝ) : GBranch (capGarden G).tree → Option ℝ :=
  fun b => fix ((cBranch G).symm b)

/-- Removed phases on the capped garden. -/
def liftOff (G : Garden w) (off : Finset (GBranch G.tree)) : Finset (GBranch (capGarden G).tree) :=
  off.map (cBranch G).toEmbedding

/-- Upper time caps on the capped garden. -/
def liftUp (G : Garden w) (up : GBranch G.tree → ℝ) : GBranch (capGarden G).tree → ℝ :=
  fun b => up ((cBranch G).symm b)

/-- Pull back of a vector labelling of the capped garden to the original nodes. -/
def pullK (G : Garden w) (k : GNode (capGarden G).tree → Mom d) : GNode G.tree → Mom d :=
  fun a => k (embN G a)

/-- A weight of the original garden as a weight of the capped garden. -/
def pullW (G : Garden w) (wt : (GNode G.tree → Mom d) → ℝ) : (GNode (capGarden G).tree → Mom d) → ℝ :=
  fun k => wt (pullK G k)

@[simp] theorem liftFix_cBranch (G : Garden w) (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) :
    liftFix G fix (cBranch G b) = fix b := by simp [liftFix]

@[simp] theorem liftUp_cBranch (G : Garden w) (up : GBranch G.tree → ℝ) (b : GBranch G.tree) :
    liftUp G up (cBranch G b) = up b := by simp [liftUp]

@[simp] theorem cBranch_mem_liftOff (G : Garden w) (off : Finset (GBranch G.tree)) (b : GBranch G.tree) :
    cBranch G b ∈ liftOff G off ↔ b ∈ off := by
  simp [liftOff]

@[simp] theorem liftUp_const (G : Garden w) (t : ℝ) : liftUp G (fun _ => t) = fun _ => t := rfl

@[simp] theorem pullK_apply (G : Garden w) (k : GNode (capGarden G).tree → Mom d) (a : GNode G.tree) :
    pullK G k a = k (embN G a) := rfl

theorem pullK_coset_capLabel (G : Garden w) (L : ℝ) (k₀ : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (n' : Fin d → ℤ) : pullK G (cosetDecoration (capGarden G) L k₀ (capLabel G κ n')) = cosetDecoration G L k₀ κ :=
  funext fun a => by simp [pullK, cosetDecoration]

theorem omegaNode_cBranch (G : Garden w) (k : GNode (capGarden G).tree → Mom d) (b : GBranch G.tree) :
    omegaNode (capGarden G) k (cBranch G b) = omegaNode G (pullK G k) b := by
  unfold omegaNode
  simp only [cBranch_child, cBranch_toNode, pullK_apply]

theorem epsDec_capLabel (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) (n' : Fin d → ℤ) :
    epsDec (capGarden G) (capLabel G κ n') = epsDec G κ := by
  unfold epsDec
  rw [← (cBranch G).prod_comp]
  simp only [cBranch_child, capLabel_embN]

/-- **Lemma 2.1(1)**: `ζ(𝒢)` is unchanged. -/
theorem zeta_capGarden (G : Garden w) : (capGarden G).zeta = G.zeta := by
  unfold Garden.zeta
  rw [← (cBranch G).prod_comp]
  simp only [cBranch_toNode, capGarden_sign_embN]

/-- The free branching nodes of the capped garden. -/
def freeEquiv (G : Garden w) (fix : GBranch G.tree → Option ℝ) :
    {b : GBranch G.tree // fix b = none} ≃ {b : GBranch (capGarden G).tree // liftFix G fix b = none} :=
  (cBranch G).subtypeEquiv fun b => by simp

theorem extendFix_lift (G : Garden w) (fix : GBranch G.tree → Option ℝ) (τ : {b // fix b = none} → ℝ) :
    (capGarden G).extendFix (liftFix G fix) (fun b' => τ ((freeEquiv G fix).symm b')) =
      fun b => G.extendFix fix τ ((cBranch G).symm b) := by
  funext b
  obtain ⟨b, rfl⟩ := (cBranch G).surjective b
  rw [Equiv.symm_apply_apply]
  rcases hb : fix b with _ | v
  · rw [extendFix_none _ _ _ _ (by simpa using hb), extendFix_none _ _ _ _ hb]
    congr 1
    rw [Equiv.symm_apply_eq]
    rfl
  · rw [extendFix_some _ _ _ _ v (by simpa using hb), extendFix_some _ _ _ _ v hb]

theorem isChildOf_cBranch (G : Garden w) (b' b : GBranch G.tree) :
    (cBranch G b').IsChildOf (cBranch G b) ↔ b'.IsChildOf b := by
  simp only [GBranch.IsChildOf, cBranch_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem mem_kDomainFix_lift (LG : LayeredGarden w) (p : ℕ) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (T : GBranch LG.garden.tree → ℝ) :
    (fun b => T ((cBranch LG.garden).symm b)) ∈
        kDomainFix (capLayered LG p) (liftUp LG.garden up) (liftFix LG.garden fix) ↔
      T ∈ kDomainFix LG up fix := by
  constructor
  · intro h b
    have hb := h (cBranch LG.garden b)
    simp only [liftFix_cBranch, liftUp_cBranch, Equiv.symm_apply_apply, cBranch_toNode,
      capLayer_embN] at hb
    refine ⟨hb.1, fun b' hb' hfree => ?_⟩
    have := hb.2 (cBranch LG.garden b') ((isChildOf_cBranch _ b' b).2 hb') (by simpa using hfree)
    simpa using this
  · intro h b
    obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
    simp only [liftFix_cBranch, liftUp_cBranch, Equiv.symm_apply_apply, cBranch_toNode,
      capLayer_embN]
    refine ⟨(h b).1, fun b' hb' hfree => ?_⟩
    obtain ⟨b', rfl⟩ := (cBranch LG.garden).surjective b'
    have := (h b).2 b' ((isChildOf_cBranch _ b' b).1 hb') (by simpa using hfree)
    simpa using this

theorem phaseProdOff_lift (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree))
    (k : GNode (capGarden G).tree → Mom d) (T : GBranch G.tree → ℝ) :
    phaseProdOff L γ δ (capGarden G) (liftOff G off) k (fun b => T ((cBranch G).symm b)) =
      phaseProdOff L γ δ G off (pullK G k) T := by
  unfold phaseProdOff
  rw [← (cBranch G).prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [cBranch_mem_liftOff, cBranch_toNode, capGarden_sign_embN, omegaNode_cBranch,
    Equiv.symm_apply_apply]

/-- The time integral is unchanged: caps carry no time variable. -/
theorem integral_lift (L γ δ : ℝ) (LG : LayeredGarden w) (p : ℕ) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (up : GBranch LG.garden.tree → ℝ)
    (k : GNode (capGarden LG.garden).tree → Mom d) :
    (∫ τ : {b : GBranch (capLayered LG p).garden.tree // liftFix LG.garden fix b = none} → ℝ,
        (kDomainFix (capLayered LG p) (liftUp LG.garden up) (liftFix LG.garden fix)).indicator
          (phaseProdOff L γ δ (capLayered LG p).garden (liftOff LG.garden off) k)
          ((capLayered LG p).garden.extendFix (liftFix LG.garden fix) τ)) =
      ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
        (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off (pullK LG.garden k))
          (LG.garden.extendFix fix τ) := by
  rw [integral_equiv_pi (freeEquiv LG.garden fix)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [extendFix_lift]
  by_cases hT : LG.garden.extendFix fix τ ∈ kDomainFix LG up fix
  · rw [Set.indicator_of_mem ((mem_kDomainFix_lift LG p up fix _).2 hT), Set.indicator_of_mem hT,
      phaseProdOff_lift]
  · rw [Set.indicator_of_notMem (fun h => hT ((mem_kDomainFix_lift LG p up fix _).1 h)),
      Set.indicator_of_notMem hT]

/-! ## The kernel identity (Lemma 2.2) -/

/-- The summand identity, for every labelling. -/
theorem kgTerm_capLayered (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (p : ℕ)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (κ : GNode LG.garden.tree → (Fin d → ℤ)) (n' : Fin d → ℤ) :
    kgTerm L γ δ (fun _ _ => 1) (capLayered LG p) (liftFix LG.garden fix) (liftOff LG.garden off)
        (pullW LG.garden fun k => wt k * ∏ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) (k ℓ.toNode))
        (liftUp LG.garden up) k₀ (capLabel LG.garden κ n') =
      kgTerm L γ δ F LG fix off wt up k₀ κ := by
  unfold kgTerm
  rw [integral_lift L γ δ LG p fix off up, pullK_coset_capLabel]
  show (epsDec (capGarden LG.garden) (capLabel LG.garden κ n') : ℂ) *
      ((pullW LG.garden fun k => wt k * ∏ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) (k ℓ.toNode))
        (cosetDecoration (capGarden LG.garden) L k₀ (capLabel LG.garden κ n')) : ℂ) * _ * _ = _
  rw [epsDec_capLabel]
  simp only [pullW, pullK_coset_capLabel, Complex.ofReal_one, Finset.prod_const_one, mul_one,
    Complex.ofReal_mul, Complex.ofReal_prod]
  ring

/-- **Lemma 2.2** (capped kernel identity). The flower kernel with input `F` equals the capped kernel with input
`1`, transported designated times, removed phases and caps, and the weight times the original input product. -/
theorem kernelKgen_capLayered (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (p : ℕ)
    (hF : OneFlower LG.garden) (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nr : Fin w → (Fin d → ℤ)) (n' m : Fin d → ℤ) :
    kernelKgen L γ δ (fun _ _ => 1) (capLayered LG p) (liftFix LG.garden fix) (liftOff LG.garden off)
        (pullW LG.garden fun k => wt k * ∏ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) (k ℓ.toNode))
        (liftUp LG.garden up) k₀ (capRoots nr n') m =
      kernelKgen L γ δ F LG fix off wt up k₀ nr n' := by
  rw [kernelKgen_eq_tsum, kernelKgen_eq_tsum]
  have hsum : ∑' κ : GenDecoration (capLayered LG p).garden d (capRoots nr n') m,
      kgTerm L γ δ (fun _ _ => 1) (capLayered LG p) (liftFix LG.garden fix) (liftOff LG.garden off)
        (pullW LG.garden fun k => wt k * ∏ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) (k ℓ.toNode))
        (liftUp LG.garden up) k₀ κ.1 =
      ∑' κ : GenDecoration LG.garden d nr n', kgTerm L γ δ F LG fix off wt up k₀ κ.1 := by
    rw [← (capDecEquiv LG.garden hF d nr n' m).symm.tsum_eq]
    refine tsum_congr fun κ => ?_
    rw [capDecEquiv_symm_apply]
    exact kgTerm_capLayered L γ δ F LG p fix off wt up k₀ κ.1 n'
  rw [hsum]
  show (coupling d L γ δ : ℂ) ^ (capGarden LG.garden).order * (capGarden LG.garden).zeta * _ = _
  rw [capGarden_order, zeta_capGarden]

/-- **Lemma 2.2** at input `1` on both sides. -/
theorem kernelKgen_capLayered_one (L γ δ : ℝ) (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nr : Fin w → (Fin d → ℤ)) (n' m : Fin d → ℤ) :
    kernelKgen L γ δ (fun _ _ => 1) (capLayered LG p) (liftFix LG.garden fix) (liftOff LG.garden off)
        (pullW LG.garden wt) (liftUp LG.garden up) k₀ (capRoots nr n') m =
      kernelKgen L γ δ (fun _ _ => 1) LG fix off wt up k₀ nr n' := by
  have hw : (fun k => wt k * ∏ ℓ ∈ inputLeaves LG.garden,
      (fun (_ : ℕ) (_ : Mom d) => (1 : ℝ)) (LG.layer ℓ.toNode) (k ℓ.toNode)) = wt := by
    funext k; simp
  have := kernelKgen_capLayered L γ δ (fun _ _ => 1) LG p hF fix off wt up k₀ nr n' m
  rw [hw] at this
  exact this

/-! ## The capped form of `flowerWeighted` -/

/-- The flower pins `fixPat pat t s` on the capped garden. -/
def capFix (LG : LayeredGarden w) (pat : Fin w → FixPat) (t s : ℝ) : GBranch (capGarden LG.garden).tree → Option ℝ :=
  liftFix LG.garden (LG.fixPat pat t s)

/-- The removed phases of the dagger (flower parents) on the capped garden. -/
def capOff (LG : LayeredGarden w) (dagger : Option (Fin w → Fin 3 → Mom d)) :
    Finset (GBranch (capGarden LG.garden).tree) :=
  liftOff LG.garden (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)

/-- The flower weight (with the dagger's sibling indicators) on the capped garden. -/
def capW (LG : LayeredGarden w) (dagger : Option (Fin w → Fin 3 → Mom d)) (W : (GNode LG.garden.tree → Mom d) → ℝ) :
    (GNode (capGarden LG.garden).tree → Mom d) → ℝ :=
  pullW LG.garden fun k => W k * dagger.elim 1 fun c => LG.sibWeight c k

/-- The literal flower kernel of one carrier garden as a capped kernel. -/
theorem flowerKernel_eq_capped (P : WTParams) (p : ℕ) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (LG : LayeredGarden w) (hF : OneFlower LG.garden) :
    FC23.flowerKernel P (fun _ _ => 1) p pat dagger W t s n n' LG =
      kernelKgen P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p) (capFix LG pat t s) (capOff LG dagger)
        (capW LG dagger (W LG)) (fun _ => t) 0 (capRoots (fun _ => n) n') 0 :=
  (kernelKgen_capLayered_one P.L P.γ P.δ LG p hF _ _ _ (fun _ => t) 0 (fun _ => n) n' 0).symm

/-- **CAPS-ID** (supplement Lemmas 2.1–2.2): `flowerWeighted` with input `1` is the sum, over the frozen flower
carrier, of the ordinary kernels `kernelKgen` of the capped gardens `capLayered LG p` (width `2 * w`), with the
pins and removed phases transported, the weight pulled back, original roots `n` and cap roots `n'`. -/
theorem flowerWeighted_eq_capSum (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (ζ : ℤˣ) (t s : ℝ)
    (n n' : Fin P.d → ℤ) :
    FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger W ζ t s n n' =
      ∑ LG ∈ (FC23.flowerCarrier_finite P p N kind pat ζ).toFinset,
        kernelKgen P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p) (capFix LG pat t s) (capOff LG dagger)
          (capW LG dagger (W LG)) (fun _ => t) 0 (capRoots (fun _ => n) n') 0 := by
  rw [FC23.flowerWeighted_eq_sum]
  refine Finset.sum_congr rfl fun LG hLG => ?_
  have hc : LG ∈ FC23.flowerCarrier P p N kind pat ζ := (Set.Finite.mem_toFinset _).1 hLG
  exact flowerKernel_eq_capped P p pat dagger W t s n n' LG (oneFlower_of_isFlowerGarden hc.1.1)

end WaveTurbulence.Flower.CapsId
