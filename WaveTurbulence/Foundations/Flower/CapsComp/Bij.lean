/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Decomp
public import WaveTurbulence.Foundations.Flower.CapsGlue.Identity
/-! # A3b CAPS-COMP: the carrier bijection and the sum identity (supplement Lemma 2.1(3)–(4))

* `bwd_exists`: every tuple of class members glues to the capped garden of a carrier member of the same
  structure (uses the uncapping inverse `exists_uncap`).
* `sum_carrier_eq_prod`: the capped flower sum `∑_{LG ∈ carrier} compValue (capLayered LG p) …` equals
  `∑_{x} ∏_c ∑_{G ∈ classX x c} compValue G …` (structures × products of component classes), via A3a's
  `CapsGlue.compValue_glueN`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine

theorem rep_eq_of {W : ℕ} {G : Garden W} {y r : Fin W} (hr : r ∈ compOf G y) (hle : ∀ k ∈ compOf G y, r ≤ k) :
    rep G y = r :=
  le_antisymm (Finset.min'_le _ _ hr) (Finset.le_min' _ _ _ hle)

section Setting

variable {w : ℕ} {P : WTParams} {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat} {ζ : ℤˣ}

/-- The decomposition of the capped garden of a carrier member of structure `x`. -/
theorem exists_decomp {LG : LayeredGarden w} (hLG : LG ∈ carrierF P p N kind pat ζ) {x : RawStr w N}
    (hxL : xF p N LG = x) (hx : ValidStr x) :
    ∃ G : ∀ c : Fin x.m, LayeredGarden (2 * x.R c), glueL (x.sigmaX hx (capSgn ζ)) G = capLayered LG p := by
  have hc := (Set.Finite.mem_toFinset _).1 hLG
  obtain ⟨_, _, hshape, -⟩ := capGlob_of_mem_carrier P p N kind pat ζ hc
  have hrep : rep (capLayered LG p).garden = x.1 := by rw [← hxL]; rfl
  exact exists_glueL _ _ (blocks_closed x hx (capSgn ζ) hshape.plain hrep)

/-- The component orders of a realized structure sum to `N`. -/
theorem sum_n_of_mem (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) {x : RawStr w N}
    (hxS : x ∈ strSet P p N kind pat ζ) : ∑ c, x.n c = N := by
  have hx := valid_of_mem hxS
  obtain ⟨LG, hLG, hxL⟩ := mem_image.1 hxS
  obtain ⟨G, hG⟩ := exists_decomp hLG hxL hx
  have hc := (Set.Finite.mem_toFinset _).1 hLG
  have hmem := fun c => fwd_mem_classX hp hN hLG hxL hx hG c
  have hord : ∀ c, (G c).garden.order = x.n c := fun c => by
    have := hmem c
    unfold classX at this
    exact (mem_classOf.1 this).1.1.2.2.1
  have h1 : (capLayered LG p).garden.order = N := by rw [capGarden_order]; exact hc.2.2.1
  rw [← hG, glueN_order] at h1
  refine Eq.trans ?_ h1
  exact Finset.sum_congr rfl fun c _ => (hord c).symm

/-- A realized structure carries order label `0` at the original trees that are not least in their component. -/
theorem ord_zero_of_mem {x : RawStr w N} (hxS : x ∈ strSet P p N kind pat ζ) (j : Fin w)
    (hj : x.1 (capσ w (.inl j)) ≠ capσ w (.inl j)) : x.2 j = 0 := by
  obtain ⟨LG, -, rfl⟩ := mem_image.1 hxS
  show (if _ then _ else _) = _
  exact if_neg hj

/-- **Backward half**: a tuple of class members glues to the capped garden of a carrier member of the same
structure. -/
theorem bwd_exists (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) {x : RawStr w N}
    (hxS : x ∈ strSet P p N kind pat ζ) (hx : ValidStr x) (G : ∀ c : Fin x.m, LayeredGarden (2 * x.R c))
    (hG : ∀ c, G c ∈ classX P p N kind pat ζ x hx c) :
    ∃ LG ∈ carrierF P p N kind pat ζ, xF p N LG = x ∧ capLayered LG p = glueL (x.sigmaX hx (capSgn ζ)) G := by
  set σ := x.sigmaX hx (capSgn ζ) with hσ
  have hG' := fun c => by have := hG c; unfold classX at this; exact mem_classOf.1 this
  have hmk : ∀ c, MkCarries P p (x.n c) (G c) := fun c => (hG' c).1.1
  have hsig : ∀ c, (G c).garden.sig = resF σ (capSgn ζ) c := fun c => (hG' c).1.2
  have hcaps := fun c => (hG' c).2.1
  have hmatch := fun c => (hG' c).2.2.1
  have hlab := fun c => (hG' c).2.2.2
  have hpl : (glueL σ G).garden.IsPlain := (isPlain_glueN σ G).2 fun c => (hmk c).1.1
  have hirr : ∀ c, (G c).garden.Irreducible := fun c => irreducible_of_isCanonGC (hmk c).1
  have hsg : ∀ y, (glueL σ G).garden.sig y = capSgn ζ y := by
    intro y
    obtain ⟨⟨c, i⟩, rfl⟩ := σ.surjective y
    rw [sig_glueN, hsig c]; rfl
  have hshape : CapShape (glueL σ G).garden := by
    refine ⟨hpl, fun j => ?_, fun ℓ j hℓ => ?_⟩
    · obtain ⟨⟨c, i⟩, hci⟩ := σ.surjective (capσ w (.inr j))
      rw [← hci, tree_glueN]
      exact hcaps c i (by rw [mem_resJ, hci]; exact capσ_inr_mem_capJ j)
    · obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (G c).garden.tree).surjective ℓ
      have hℓ' : σ ⟨c, y.1.1⟩ = capσ w (.inr j) := hℓ
      have hy : y.1.1 ∈ resJ σ (capJ w) c := by rw [mem_resJ, hℓ']; exact capσ_inr_mem_capJ j
      have hm := hmatch c y hy
      rw [show (glueL σ G).garden.pair = (glueGardenN σ fun c => (G c).garden).pair from rfl, glueN_pair_leaf,
        glueLeafN_val]
      show σ ⟨c, ((G c).garden.pair y).1.1⟩ = _
      have hm' : σ ⟨c, ((G c).garden.pair y).1.1⟩ = capσ w (.inl (origIdx (σ ⟨c, y.1.1⟩))) := hm
      rw [hm', hℓ', origIdx_inr]
  obtain ⟨LG, hF, hm, hsigL, hcap⟩ := exists_uncap (glueL σ G) p hshape
  have hglob : CapGlob P p N kind pat ζ (capLayered LG p) := by
    rw [hcap]
    refine ⟨(canonCriterion_glueN σ G p).2 fun c => (hmk c).1.2.2, ?_, fun j => by rw [hsg, capSgn_inl],
      fun j => by rw [hsg, capSgn_inr], fun j => ?_⟩
    · rw [glueN_order]
      refine Eq.trans ?_ (sum_n_of_mem hp hN hxS)
      exact Finset.sum_congr rfl fun c _ => (hmk c).2.2.1
    · obtain ⟨⟨c, i⟩, hci⟩ := σ.surjective (capσ w (.inl j))
      have hi : i ∉ resJ σ (capJ w) c := by rw [mem_resJ, hci]; exact capσ_inl_notMem_capJ j
      obtain ⟨h1, h2, h3⟩ := hlab c i hi
      rw [← hci]
      refine ⟨(capStem_glueN σ G (capJ w) p c i).2 h1, (capKindOK_glueN σ G (capJ w) p _ c i kind).2 h2, ?_⟩
      refine (capPatExist_glueN σ G (capJ w) p c i (pat j)).2 ?_
      have e : resF σ (capExt pat .plain) c i = pat j := by
        show capExt pat .plain (σ ⟨c, i⟩) = pat j
        rw [hci, capExt_inl]
      rw [← e]; exact h3
  have hLGc : LG ∈ FC23.flowerCarrier P p N kind pat ζ :=
    mem_carrier_of_capGlob P p N hp hN kind pat ζ hF hm (fun j => by rw [hsigL, hcap]) hglob
  refine ⟨LG, (Set.Finite.mem_toFinset _).2 hLGc, ?_, hcap⟩
  -- the structure of the glued garden is `x`
  have hcomp : ∀ c i, compOf (glueL σ G).garden (σ ⟨c, i⟩) = blockOf σ c := compOf_glueN σ G hpl hirr
  have hrep : rep (glueL σ G).garden = x.1 := by
    funext k
    obtain ⟨⟨c, i⟩, rfl⟩ := σ.surjective k
    rw [x.rep_sigmaX hx (capSgn ζ) c i]
    refine rep_eq_of ?_ fun k hk => ?_
    · rw [hcomp, x.blockOf_sigmaX]; exact x.repAt_mem_blk c
    · rw [hcomp, x.blockOf_sigmaX] at hk; exact x.repAt_le hx c hk
  unfold xF
  rw [hcap]
  refine Prod.ext hrep (funext fun j => ?_)
  show (if _ then _ else _) = _
  split_ifs with hj
  · rw [hrep] at hj
    obtain ⟨⟨c, i⟩, hci⟩ := σ.surjective (capσ w (.inl j))
    have hrc : x.repAt c = capσ w (.inl j) := by rw [← hj, ← hci, x.rep_sigmaX]
    have hco : compOrder (glueL σ G).garden (capσ w (.inl j)) = x.n c := by
      unfold compOrder
      rw [← hci, hcomp, order_glue_piece]
      exact (hmk c).2.2.1
    have hnj : x.n c = x.2 j := by unfold RawStr.n; rw [hrc, origIdx_inl]
    apply Fin.ext
    show min N (compOrder (glueL σ G).garden (capσ w (.inl j))) = _
    rw [hco, hnj]
    exact min_eq_right (Nat.lt_succ_iff.1 (x.2 j).2)
  · rw [hrep] at hj
    exact (ord_zero_of_mem hxS j hj).symm

/-! ## The sum identity -/

variable (P p N kind pat ζ)

/-- The capped value with global data on `Fin (2w)`. -/
def capVal (KSEL : Fin (2 * w) → Option ℕ) (RF : Fin (2 * w) → Option ℝ) (SG : Fin (2 * w) → Option ℕ)
    (RS : Fin (2 * w) → ℝ) (H : ℕ → Fin (2 * w) → Fin (2 * w) → Mom P.d → ℝ)
    (DAG : Option (Fin (2 * w) → Fin 3 → Mom P.d)) (ROOTS : Fin (2 * w) → (Fin P.d → ℤ)) (t s : ℝ)
    (G : LayeredGarden (2 * w)) : ℂ :=
  compValue P G (fixCap G (capJ w) (capExt pat .plain) t s) (offCap G (capJ w) DAG.isSome)
    (capWt G (capJ w) p P.L KSEL RF SG RS H DAG) t ROOTS

/-- The component value with restricted data. -/
def compVal (x : RawStr w N) (hx : ValidStr x) (KSEL : Fin (2 * w) → Option ℕ) (RF : Fin (2 * w) → Option ℝ)
    (SG : Fin (2 * w) → Option ℕ) (RS : Fin (2 * w) → ℝ) (H : ℕ → Fin (2 * w) → Fin (2 * w) → Mom P.d → ℝ)
    (DAG : Option (Fin (2 * w) → Fin 3 → Mom P.d)) (ROOTS : Fin (2 * w) → (Fin P.d → ℤ)) (t s : ℝ) (c : Fin x.m)
    (G : LayeredGarden (2 * x.R c)) : ℂ :=
  compValue P G (fixCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c)
      (resF (x.sigmaX hx (capSgn ζ)) (capExt pat .plain) c) t s)
    (offCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) DAG.isSome)
    (capWt G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) p P.L (resF (x.sigmaX hx (capSgn ζ)) KSEL c)
      (resF (x.sigmaX hx (capSgn ζ)) RF c) (resF (x.sigmaX hx (capSgn ζ)) SG c)
      (resF (x.sigmaX hx (capSgn ζ)) RS c) (resH (x.sigmaX hx (capSgn ζ)) H c)
      (resDag (x.sigmaX hx (capSgn ζ)) DAG c))
    t (resF (x.sigmaX hx (capSgn ζ)) ROOTS c)

variable {P p N kind pat ζ}

/-- **The capped sum as structures × products of component classes.** -/
theorem sum_carrier_eq_prod (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4)
    (KSEL : Fin (2 * w) → Option ℕ) (RF : Fin (2 * w) → Option ℝ) (SG : Fin (2 * w) → Option ℕ)
    (RS : Fin (2 * w) → ℝ) (H : ℕ → Fin (2 * w) → Fin (2 * w) → Mom P.d → ℝ)
    (DAG : Option (Fin (2 * w) → Fin 3 → Mom P.d)) (ROOTS : Fin (2 * w) → (Fin P.d → ℤ)) (t s : ℝ)
    (hs : ∀ (x : RawStr w N) (hx : ValidStr x) (c : Fin x.m) (G : LayeredGarden (2 * x.R c)),
      G ∈ classX P p N kind pat ζ x hx c →
      Summable fun κ : GenDecoration G.garden P.d (resF (x.sigmaX hx (capSgn ζ)) ROOTS c) 0 =>
        FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) G
          (fixCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) (resF (x.sigmaX hx (capSgn ζ)) (capExt pat .plain) c) t s)
          (offCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) DAG.isSome)
          (capWt G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) p P.L (resF (x.sigmaX hx (capSgn ζ)) KSEL c)
            (resF (x.sigmaX hx (capSgn ζ)) RF c) (resF (x.sigmaX hx (capSgn ζ)) SG c)
            (resF (x.sigmaX hx (capSgn ζ)) RS c) (resH (x.sigmaX hx (capSgn ζ)) H c)
            (resDag (x.sigmaX hx (capSgn ζ)) DAG c))
          (fun _ => t) 0 κ.1) :
    ∑ LG ∈ carrierF P p N kind pat ζ, capVal P p pat KSEL RF SG RS H DAG ROOTS t s (capLayered LG p) =
      ∑ x : ↥(strSet P p N kind pat ζ), ∏ c : Fin x.1.m,
        ∑ G ∈ classX P p N kind pat ζ x.1 (valid_of_mem x.2) c,
          compVal P p N pat ζ x.1 (valid_of_mem x.2) KSEL RF SG RS H DAG ROOTS t s c G := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := carrierF P p N kind pat ζ) (t := strSet P p N kind pat ζ)
    (g := xF p N) (fun LG hLG => mem_image_of_mem _ hLG)]
  rw [← Finset.sum_attach (strSet P p N kind pat ζ), ← Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun xx _ => ?_
  obtain ⟨x, hxS⟩ := xx
  have hx : ValidStr x := valid_of_mem hxS
  show _ = ∏ c : Fin x.m, ∑ G ∈ classX P p N kind pat ζ x hx c, compVal P p N pat ζ x hx KSEL RF SG RS H DAG ROOTS t s c G
  set σ := x.sigmaX hx (capSgn ζ) with hσ
  rw [Finset.prod_univ_sum]
  have hfib : ∀ LG ∈ (carrierF P p N kind pat ζ).filter (fun LG => xF p N LG = x),
      LG ∈ carrierF P p N kind pat ζ ∧ xF p N LG = x := fun LG h => mem_filter.1 h
  refine Finset.sum_bij (fun LG h => Classical.choose (exists_decomp (hfib LG h).1 (hfib LG h).2 hx)) ?_ ?_ ?_ ?_
  · intro LG h
    rw [Fintype.mem_piFinset]
    exact fun c => fwd_mem_classX hp hN (hfib LG h).1 (hfib LG h).2 hx
      (Classical.choose_spec (exists_decomp (hfib LG h).1 (hfib LG h).2 hx)) c
  · intro LG₁ h₁ LG₂ h₂ e
    have e1 := Classical.choose_spec (exists_decomp (hfib LG₁ h₁).1 (hfib LG₁ h₁).2 hx)
    have e2 := Classical.choose_spec (exists_decomp (hfib LG₂ h₂).1 (hfib LG₂ h₂).2 hx)
    rw [e] at e1
    have hc1 := (Set.Finite.mem_toFinset _).1 (hfib LG₁ h₁).1
    have hc2 := (Set.Finite.mem_toFinset _).1 (hfib LG₂ h₂).1
    exact capLayered_injective p hc1.1.1 hc2.1.1 (e1.symm.trans e2)
  · intro G hG
    rw [Fintype.mem_piFinset] at hG
    obtain ⟨LG, hLG, hxL, hcap⟩ := bwd_exists hp hN hxS hx G hG
    have hmemLG : LG ∈ (carrierF P p N kind pat ζ).filter (fun LG => xF p N LG = x) := mem_filter.2 ⟨hLG, hxL⟩
    refine ⟨LG, hmemLG, ?_⟩
    apply glueL_injective σ
    rw [Classical.choose_spec (exists_decomp (hfib LG hmemLG).1 (hfib LG hmemLG).2 hx), hcap]
  · intro LG h
    have e := Classical.choose_spec (exists_decomp (hfib LG h).1 (hfib LG h).2 hx)
    have hG := fun c => fwd_mem_classX hp hN (hfib LG h).1 (hfib LG h).2 hx e c
    have e2 : capVal P p pat KSEL RF SG RS H DAG ROOTS t s (capLayered LG p) =
        capVal P p pat KSEL RF SG RS H DAG ROOTS t s
          (glueL σ (Classical.choose (exists_decomp (hfib LG h).1 (hfib LG h).2 hx))) := by
      rw [e]
    rw [e2]
    exact compValue_glueN P σ _ (capJ w) (capExt pat .plain) t s KSEL p RF SG RS H DAG ROOTS
      fun c => hs x hx c _ (hG c)

end Setting

end WaveTurbulence.Flower.CapsComp
