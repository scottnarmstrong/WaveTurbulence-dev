/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Data
public import WaveTurbulence.Foundations.Flower.MkAsm.Helpers
/-! # A3b CAPS-COMP: `CapsDecompF` (the filtered core), from the label twist stability

`capsDecompF_of_stable : CapsTwistStable → MkAsm.CapsDecompF`. The structures are the realized ones
(`strSet`, at most `(4Pm)^{4Pm}(N+1)^{2Pm}`), the components are `compData`, and the identity is A2's
`flowerWeighted_coreF_eq_capSum` followed by `sum_carrier_eq_prod` (with the summability `summable_kgTerm_capWt`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm

variable {w : ℕ}

theorem capExt_const {V : Type*} (v : V) : capExt (w := w) (fun _ => v) v = fun _ => v := by
  funext c
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j <;> simp

theorem card_strSet_le (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat) (ζ : ℤˣ) :
    (strSet P p N kind pat ζ).card ≤ (2 * w) ^ (2 * w) * (N + 1) ^ w := by
  rw [← card_rawStr]
  exact Finset.card_le_univ _

theorem val_compData {P : WTParams} {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat} {ζ : ℤˣ}
    (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hst : CapsTwistStable) (t s b : ℝ) (hb : 1 ≤ b)
    (KSEL : Fin w → Option ℕ) (hKSEL : ∀ j, (KSEL j).isSome → pat j = .plain)
    (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (sg : Fin w → Option ℕ)
    (RS : Fin w → ℝ) (hRS : ∀ j, P.L ≤ RS j) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (n n' : Fin P.d → ℤ)
    (hdecay : ((∃ i, sg i ≠ none) ∨ ∃ i, KSEL i ≠ none) → ∀ j, ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L n‖)
    (x : ↥(strSet P p N kind pat ζ)) (c : Fin x.1.m) :
    (compData P p N kind pat ζ hp hN hst t s b hb KSEL hKSEL Rf hRf sg RS hRS h hh dagger n n' hdecay x c).val =
      ∑ G ∈ classX P p N kind pat ζ x.1 (valid_of_mem x.2) c,
        compVal P p N pat ζ x.1 (valid_of_mem x.2) (capExt KSEL none) (capExt Rf none) (capExt sg none)
          (capExt RS P.L) (capH h) (capDag dagger) (capRoots (fun _ => n) n') t s c G := by
  unfold CompData.val compVal
  refine Finset.sum_congr rfl fun G _ => ?_
  have e : (resDag (x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)) (capDag dagger) c).isSome = (capDag dagger).isSome := by
    simp [resDag]
  simp only [compData]
  rw [e]
  rfl

/-- The summability side condition for the classes. -/
theorem hs_classX {P : WTParams} (hL : 0 < P.L) {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat} {ζ : ℤˣ}
    (t s b : ℝ) (hb : 1 ≤ b) (KSEL : Fin (2 * w) → Option ℕ) (RF : Fin (2 * w) → Option ℝ)
    (SG : Fin (2 * w) → Option ℕ) (RS : Fin (2 * w) → ℝ) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (DAG : Option (Fin (2 * w) → Fin 3 → Mom P.d)) (n n' : Fin P.d → ℤ) :
    ∀ (x : RawStr w N) (hx : ValidStr x) (c : Fin x.m) (G : LayeredGarden (2 * x.R c)),
      G ∈ classX P p N kind pat ζ x hx c →
      Summable fun κ : GenDecoration G.garden P.d (resF (x.sigmaX hx (capSgn ζ)) (capRoots (fun _ => n) n') c) 0 =>
        FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) G
          (fixCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) (resF (x.sigmaX hx (capSgn ζ)) (capExt pat .plain) c) t s)
          (offCap G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) DAG.isSome)
          (capWt G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) p P.L (resF (x.sigmaX hx (capSgn ζ)) KSEL c)
            (resF (x.sigmaX hx (capSgn ζ)) RF c) (resF (x.sigmaX hx (capSgn ζ)) SG c)
            (resF (x.sigmaX hx (capSgn ζ)) RS c) (resH (x.sigmaX hx (capSgn ζ)) (capH h) c)
            (resDag (x.sigmaX hx (capSgn ζ)) DAG c))
          (fun _ => t) 0 κ.1 := by
  intro x hx c G hG
  unfold classX at hG
  obtain ⟨⟨hmk, -⟩, hcaps, -⟩ := mem_classOf.1 hG
  refine summable_kgTerm_capWt P hL G hmk.1.1 (Canon.layer_le_of_isCanonGC hmk.1) _ hcaps _ n' ?_ _ _ _ _ _ _ _ _ _
    b hb fun q hq i i' => SNormR_capH_le h b (by linarith) p hh q hq _ _
  intro i hi
  rw [mem_resJ, mem_capJ_iff] at hi
  obtain ⟨j, hj⟩ := hi
  show capRoots (fun _ => n) n' (x.sigmaX hx (capSgn ζ) ⟨c, i⟩) = n'
  rw [hj, capRoots_inr]

/-- **`CapsDecompF` from the label twist stability.** -/
theorem capsDecompFAt_of_stable (hst : CapsTwistStable) (Pm : ℕ) (P : WTParams) : CapsDecompFAt Pm P := by
  intro hL _ p hp t _ s _ n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  have hdecay' : ((∃ i, σ i ≠ none) ∨ ∃ i, (fun _ : Fin (2 * Pm) => (none : Option ℕ)) i ≠ none) →
      ∀ j, ∃ r, Rf j = some r ∧ (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        r ^ 10 ≤ ‖latticePoint P.L n‖ := by
    rintro (h1 | ⟨i, hi⟩)
    · exact hdecay h1
    · exact absurd rfl hi
  refine ⟨↥(strSet P p N kind pat ζ), inferInstance, fun x => x.1.m,
    fun x c => compData P p N kind pat ζ hp hN hst t s b hb (fun _ => none) (fun j hj => by simp at hj) Rf hRf σ
      (fun _ => P.L) (fun _ => le_rfl) h hh dagger n n' hdecay' x c, ?_, fun x => ?_, fun x => ?_,
    fun x c j => ?_, ?_⟩
  · rw [Fintype.card_coe]
    have := card_strSet_le P p N kind pat ζ (w := 2 * Pm)
    have e : 2 * (2 * Pm) = 4 * Pm := by ring
    rw [e] at this
    exact_mod_cast this
  · show ∑ c, 2 * x.1.R c = 4 * Pm
    rw [sum_two_R (valid_of_mem x.2) (capSgn ζ)]
    ring
  · exact sum_n_of_mem hp hN x.2
  · show capExt (fun _ => none) none _ = none
    rw [capExt_const]
  · rw [flowerWeighted_coreF_eq_capSum P p N kind pat dagger h Rf σ (capExt (fun _ => P.L) P.L) ζ t s n n']
    have e : ∀ LG : LayeredGarden (2 * Pm), selOK (capLayered LG p) (capJ (2 * Pm)) (fun _ => none) =
        selOK (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => none) none) := fun LG => by rw [capExt_const]
    have e2 : ∀ LG : LayeredGarden (2 * Pm), selCap (capLayered LG p) (capJ (2 * Pm)) (fun _ => none) =
        selCap (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => none) none) := fun LG => by rw [capExt_const]
    simp only [e, e2]
    have hS := sum_carrier_eq_prod (P := P) (p := p) (N := N) (kind := kind) (pat := pat) (ζ := ζ) hp hN
      (capExt (fun _ => none) none) (capExt Rf none) (capExt σ none) (capExt (fun _ => P.L) P.L) (capH h)
      (capDag dagger) (capRoots (fun _ => n) n') t s
      (hs_classX hL t s b hb _ _ _ _ h hh _ n n')
    unfold capVal capWt at hS
    refine hS.trans (Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun c _ => ?_)
    exact (val_compData hp hN hst t s b hb (fun _ => none) _ Rf hRf σ (fun _ => P.L) _ h hh dagger n n'
      hdecay' x c).symm

/-- **`CapsDecompF`** (all parameters), from the label twist stability. -/
theorem capsDecompF_of_stable (hst : CapsTwistStable) : CapsDecompF :=
  fun Pm P => capsDecompFAt_of_stable hst Pm P

end WaveTurbulence.Flower.CapsComp
