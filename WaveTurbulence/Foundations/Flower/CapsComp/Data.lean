/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Summ
public import WaveTurbulence.Foundations.Flower.CapsComp.Geo
public import WaveTurbulence.Foundations.XChain.AnsatzBase
/-! # A3b CAPS-COMP: the component data (`MkAsm.CompData`) of a structure, and the counts

For a realized structure `x` and global data on the capped trees (pins from `pat`, depth selections `KSEL`, frontier
scales, stem filters, shell scales `RS`, pair profiles `capH h`, dagger, roots `capRoots n n'`), `compData` builds the
`CompData` of component `c` with class `classX x c`; every premise of `MarkedComponentBoundAtI` is checked here
(the twist closure from `CapsTwistStable`). `val_compData` identifies its value with A3a's component value. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm

variable {w : ℕ} {P : WTParams} {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat} {ζ : ℤˣ}

/-! ## Facts on realized structures -/

theorem n_le_of_mem (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) {x : RawStr w N}
    (hxS : x ∈ strSet P p N kind pat ζ) (c : Fin x.m) : x.n c ≤ N := by
  exact (Finset.single_le_sum (f := fun c => x.n c) (fun _ _ => Nat.zero_le _) (mem_univ c)).trans
    (sum_n_of_mem hp hN hxS).le

/-- Every component of a realized structure has positive order (each original tree has positive top order). -/
theorem one_le_n_of_mem (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) {x : RawStr w N}
    (hxS : x ∈ strSet P p N kind pat ζ) (c : Fin x.m) : 1 ≤ x.n c := by
  have hx := valid_of_mem hxS
  obtain ⟨LG, hLG, hxL⟩ := mem_image.1 hxS
  obtain ⟨G, hG⟩ := exists_decomp hLG hxL hx
  have hmem := fwd_mem_classX hp hN hLG hxL hx hG c
  unfold classX at hmem
  obtain ⟨⟨hmk, -⟩, -, -, hlab⟩ := mem_classOf.1 hmem
  -- an original tree of the component
  have hcard := x.card_resJ hx (capSgn ζ) c
  have hR := x.one_le_R hx c
  have hex : ∃ i, i ∉ resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c := by
    by_contra hall
    push Not at hall
    have : resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c = univ := eq_univ_of_forall hall
    rw [this, card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨i, hi⟩ := hex
  have hk := (hlab i hi).2.1
  have htop : 1 ≤ (G c).topOrder p i := by
    cases kind with
    | X => exact hk.1
    | Y => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hk.1
    | W => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hk.1
  rw [← hmk.2.2.1]
  exact htop.trans ((G c).topOrder_le_order p i)

theorem sum_two_R {x : RawStr w N} (hv : ValidStr x)
    (sgn : Fin (2 * w) → ℤˣ) : ∑ c, 2 * x.R c = 2 * w := by
  have := Fintype.card_congr (x.sigmaX hv sgn)
  rw [Fintype.card_sigma, Fintype.card_fin] at this
  simpa using this

/-! ## Restrictions of the global data -/

theorem resF_capExt_some {α : Type*} {x : RawStr w N} (hv : ValidStr x) (f : Fin w → Option α) (c : Fin x.m)
    (i : Fin (2 * x.R c)) {r : α} (h : resF (x.sigmaX hv (capSgn ζ)) (capExt f none) c i = some r) :
    ∃ j, x.sigmaX hv (capSgn ζ) ⟨c, i⟩ = capσ w (.inl j) ∧ f j = some r := by
  obtain ⟨s, hs⟩ := (capσ w).surjective (x.sigmaX hv (capSgn ζ) ⟨c, i⟩)
  have h' : capExt f none (x.sigmaX hv (capSgn ζ) ⟨c, i⟩) = some r := h
  rw [← hs] at h'
  rcases s with j | j
  · exact ⟨j, hs.symm, by simpa using h'⟩
  · simp at h'

theorem SNormR_capH_le {d : ℕ} (h : ℕ → Fin w → Fin w → Mom d → ℝ) (b : ℝ) (hb : 0 ≤ b) (p : ℕ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) :
    ∀ q ≤ p, ∀ c c', SNormR (40 * d) (40 * d) (capH h q c c') ≤ ENNReal.ofReal b := by
  intro q hq c c'
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  obtain ⟨s', rfl⟩ := (capσ w).surjective c'
  rcases s with j | j <;> rcases s' with j' | j'
  · rw [capH_inl]; exact hh q hq j j'
  all_goals
    simp only [capH, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    rw [Induct.SNormR_zero_function]; exact zero_le

/-! ## The component data -/

variable (P p N kind pat ζ)

/-- **The component data** of component `c` of the realized structure `x`. -/
def compData (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hst : CapsTwistStable) (t s b : ℝ) (hb : 1 ≤ b)
    (KSEL : Fin w → Option ℕ) (hKSEL : ∀ j, (KSEL j).isSome → pat j = .plain)
    (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (sg : Fin w → Option ℕ)
    (RS : Fin w → ℝ) (hRS : ∀ j, P.L ≤ RS j) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (n n' : Fin P.d → ℤ)
    (hdecay : ((∃ i, sg i ≠ none) ∨ ∃ i, KSEL i ≠ none) → ∀ j, ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L n‖)
    (x : ↥(strSet P p N kind pat ζ)) (c : Fin x.1.m) : CompData P p t s b where
  R := x.1.R c
  hR := x.1.one_le_R (valid_of_mem x.2) c
  n := x.1.n c
  hn := one_le_n_of_mem hp hN x.2 c
  J := resJ (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capJ w) c
  hJ := x.1.card_resJ (valid_of_mem x.2) (capSgn ζ) c
  roots := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capRoots (fun _ => n) n') c
  pat := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt pat .plain) c
  kSel := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt KSEL none) c
  A := classX P p N kind pat ζ x.1 (valid_of_mem x.2) c
  h := resH (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capH h) c
  Rf := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt Rf none) c
  σ := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt sg none) c
  Rs := resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt RS P.L) c
  dag := resDag (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capDag dagger) c
  hA := fun G hG => by
    have hgeo := capGeo_of_mem_classX hG
    unfold classX at hG
    obtain ⟨⟨hmk, -⟩, hcaps, -⟩ := mem_classOf.1 hG
    exact ⟨hmk, irreducible_of_isCanonGC hmk.1, hcaps, hgeo.1, hgeo.2⟩
  hplain := fun i hi => by
    obtain ⟨j, hj, -⟩ := resF_capExt_some (valid_of_mem x.2) KSEL c i (Option.get_mem hi)
    show capExt pat .plain (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ) ⟨c, i⟩) = _
    rw [hj, capExt_inl]
    refine hKSEL j ?_
    have h' : capExt KSEL none (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ) ⟨c, i⟩) = KSEL j := by rw [hj, capExt_inl]
    have : (resF (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capExt KSEL none) c i).isSome := hi
    unfold resF at this
    rwa [h'] at this
  hclosed := by
    unfold classX
    exact markedTwistClosed_of_stable hst P hp ((n_le_of_mem hp hN x.2 c).trans hN) kind _ _ _ _ _ t s
  hh := fun q hq i i' => SNormR_capH_le h b (by linarith) p hh q hq _ _
  hRf := fun i r hr => by
    obtain ⟨j, -, hj⟩ := resF_capExt_some (valid_of_mem x.2) Rf c i hr
    exact hRf j r hj
  hRs := fun i => by
    show P.L ≤ capExt RS P.L (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ) ⟨c, i⟩)
    obtain ⟨s', hs'⟩ := (capσ w).surjective (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ) ⟨c, i⟩)
    rw [← hs']
    rcases s' with j | j
    · rw [capExt_inl]; exact hRS j
    · rw [capExt_inr]
  hdecay := fun hor i hi => by
    have hor' : (∃ i, sg i ≠ none) ∨ ∃ i, KSEL i ≠ none := by
      rcases hor with ⟨i', hi'⟩ | ⟨i', hi'⟩
      · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hi'
        obtain ⟨j, -, hj⟩ := resF_capExt_some (valid_of_mem x.2) sg c i' hr
        exact Or.inl ⟨j, by rw [hj]; exact Option.some_ne_none _⟩
      · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hi'
        obtain ⟨j, -, hj⟩ := resF_capExt_some (valid_of_mem x.2) KSEL c i' hr
        exact Or.inr ⟨j, by rw [hj]; exact Option.some_ne_none _⟩
    set σx := x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)
    obtain ⟨s', hs'⟩ := (capσ w).surjective (σx ⟨c, i⟩)
    rcases s' with j | j
    · obtain ⟨r, hr, hsupp, hdec⟩ := hdecay hor' j
      refine ⟨r, ?_, fun j' y hy => ?_, ?_⟩
      · show capExt Rf none (σx ⟨c, i⟩) = some r
        rw [← hs', capExt_inl]; exact hr
      · show capH h p (σx ⟨c, i⟩) (σx ⟨c, j'⟩) y = 0 ∧ capH h p (σx ⟨c, j'⟩) (σx ⟨c, i⟩) y = 0
        rw [← hs']
        obtain ⟨s'', hs''⟩ := (capσ w).surjective (σx ⟨c, j'⟩)
        rw [← hs'']
        rcases s'' with j2 | j2
        · rw [capH_inl, capH_inl]; exact hsupp j2 y hy
        · rw [capH_inr_left, capH_inr_right]; exact ⟨rfl, rfl⟩
      · show r ^ 10 ≤ ‖latticePoint P.L (capRoots (fun _ => n) n' (σx ⟨c, i⟩))‖
        rw [← hs', capRoots_inl]; exact hdec
    · exfalso
      apply hi
      rw [mem_resJ, ← hs']; exact capσ_inr_mem_capJ j

end WaveTurbulence.Flower.CapsComp
