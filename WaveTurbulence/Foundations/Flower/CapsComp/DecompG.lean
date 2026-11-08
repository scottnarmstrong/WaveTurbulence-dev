/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.DecompF
public import WaveTurbulence.Foundations.Flower.CapsFub.Top
public import WaveTurbulence.Foundations.Flower.CapsId.Shell
/-! # A3b CAPS-COMP: `CapsDecompG` (the gain core), from the label twist stability

The shell integral is moved outside the flower sum by CAPS-FUBINI (`coreG_shell_exchange`); at a fixed shell scale
`R` the capped weight is A2's depth sum (`capW_shell_depth`, depth labels `kk ∈ ∏_j range (N+1)`), which is moved out
of the decoration sum by FL-POLAR's `kernelKgen_linear_step`. Each depth label is then decomposed as in Core-F.
The structures are `(realized structure, depth labels)`: at most `(4Pm)^{4Pm}(N+1)^{4Pm}`. Every original tree
carries a selection, so `∏ gain = ∏_j R_j⁻¹ R_j^{-1/18}` on the shell box. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm GraftGen

variable {w : ℕ}

/-- The depth labels. -/
def depthSet (w N : ℕ) : Finset (Fin w → ℕ) := Fintype.piFinset fun _ => Finset.range (N + 1)

theorem card_depthSet (w N : ℕ) : (depthSet w N).card = (N + 1) ^ w := by
  simp [depthSet, Fintype.card_piFinset]

theorem le_of_mem_shellBox {L : ℝ} (hL : 0 < L) {j₂ : ℕ} {R : Fin w → ℝ} (hR : R ∈ shellBox w L j₂) (j : Fin w) :
    L ≤ R j := by
  have h1 := (hR j (Set.mem_univ _)).1
  have h2 : (1 : ℝ) ≤ 2 ^ (j₂ - 1) := one_le_pow₀ (by norm_num)
  nlinarith

theorem capExt_max_eq {L : ℝ} (R : Fin w → ℝ) (hR : ∀ j, L ≤ R j) :
    capExt (fun j => max L (R j)) L = capExt R L := by
  funext c
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · simp [max_eq_right (hR j)]
  · simp

/-- The product of the gains over the components of a structure. -/
theorem prod_gain {P : WTParams} {p N : ℕ} {kind : FlowerKind} {ζ : ℤˣ} (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4)
    (hst : CapsTwistStable) (t s b : ℝ) (hb : 1 ≤ b) (kk : Fin w → ℕ) (Rf : Fin w → Option ℝ)
    (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (RS : Fin w → ℝ) (hRS : ∀ j, P.L ≤ RS j)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (n n' : Fin P.d → ℤ)
    (hdecay : ((∃ i, (fun _ : Fin w => (none : Option ℕ)) i ≠ none) ∨ ∃ i, (fun j => some (kk j)) i ≠ none) →
      ∀ j, ∃ r, Rf j = some r ∧ (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        r ^ 10 ≤ ‖latticePoint P.L n‖)
    (x : ↥(strSet P p N kind (fun _ => .plain) ζ)) :
    ∏ c, (compData P p N kind (fun _ => .plain) ζ hp hN hst t s b hb (fun j => some (kk j)) (fun _ _ => rfl) Rf hRf
      (fun _ => none) RS hRS h hh dagger n n' hdecay x c).gain = ∏ j : Fin w, ((RS j)⁻¹ * (RS j) ^ (-(1 / 18 : ℝ))) := by
  set σx := x.1.sigmaX (valid_of_mem x.2) (capSgn ζ)
  set f : Fin (2 * w) → ℝ := fun y => if (capExt (fun j => some (kk j)) none y).isSome then
    (capExt RS P.L y)⁻¹ * (capExt RS P.L y) ^ (-(1 / 18 : ℝ)) else 1 with hf
  have e1 : ∀ c, (compData P p N kind (fun _ => .plain) ζ hp hN hst t s b hb (fun j => some (kk j)) (fun _ _ => rfl) Rf
      hRf (fun _ => none) RS hRS h hh dagger n n' hdecay x c).gain = ∏ i, f (σx ⟨c, i⟩) := fun c => rfl
  simp only [e1]
  rw [(Fintype.prod_sigma fun z => f (σx z)).symm, Equiv.prod_comp σx f, ← Equiv.prod_comp (capσ w) f,
    Fintype.prod_sum_type]
  have e2 : ∀ j, f (capσ w (.inr j)) = 1 := fun j => by simp [hf]
  simp only [e2, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [hf]

/-- The per-depth summability of a capped carrier garden. -/
theorem summable_capped {P : WTParams} (hL : 0 < P.L) {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat}
    {ζ : ℤˣ} {LG : LayeredGarden w} (hLG : LG ∈ FC23.flowerCarrier P p N kind pat ζ) (fix off)
    (KSEL : Fin (2 * w) → Option ℕ) (RF : Fin (2 * w) → Option ℝ) (SG : Fin (2 * w) → Option ℕ)
    (RS : Fin (2 * w) → ℝ) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (DAG : Option (Fin (2 * w) → Fin 3 → Mom P.d)) (t : ℝ) (n n' : Fin P.d → ℤ) :
    Summable (kernelGenFactor P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p) fix off
      (capWt (capLayered LG p) (capJ w) p P.L KSEL RF SG RS (capH h) DAG) (fun _ => t) 0
      (n := capRoots (fun _ => n) n') (nfl := 0)) := by
  obtain ⟨-, -, hshape, hglob⟩ := capGlob_of_mem_carrier P p N kind pat ζ hLG
  have hs := summable_kgTerm_capWt P hL (capLayered LG p) hshape.plain hglob.1.1 (capJ w)
    (fun i hi => capGarden_tree_of_mem_capJ LG.garden hi) (capRoots (fun _ => n) n') n'
    (fun i hi => by obtain ⟨j, rfl⟩ := (mem_capJ_iff i).1 hi; exact capRoots_inr _ _ j) fix off (fun _ => t)
    KSEL RF SG RS (capH h) DAG b hb (SNormR_capH_le h b (by linarith) p hh)
  exact hs.congr fun κ => rfl

/-- **`CapsDecompG` from the label twist stability.** -/
theorem capsDecompGAt_of_stable (hst : CapsTwistStable) (Pm : ℕ) (P : WTParams) : CapsDecompGAt Pm P := by
  intro hL _ p hp t _ s _ n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hsupp
  have hRf' : ∀ j r, (fun j => some (Rf j)) j = some r → P.L / 2 ≤ r := fun j r hr => by
    have : Rf j = r := Option.some.inj hr
    rw [← this]; exact hRf j
  have hdecay : ∀ kk : Fin (2 * Pm) → ℕ,
      ((∃ i, (fun _ : Fin (2 * Pm) => (none : Option ℕ)) i ≠ none) ∨ ∃ i, (fun j => some (kk j)) i ≠ none) →
      ∀ j, ∃ r, (fun j => some (Rf j)) j = some r ∧ (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        r ^ 10 ≤ ‖latticePoint P.L n‖ := fun _ _ j => ⟨Rf j, rfl, (hsupp j).1, (hsupp j).2⟩
  let D : (Fin (2 * Pm) → ℝ) → ∀ X : ↥(strSet P p N kind (fun _ => .plain) ζ) × ↥(depthSet (2 * Pm) N),
      Fin X.1.1.m → CompData P p t s b := fun Rs X c =>
    compData P p N kind (fun _ => .plain) ζ hp hN hst t s b hb (fun j => some (X.2.1 j)) (fun _ _ => rfl)
      (fun j => some (Rf j)) hRf' (fun _ => none) (fun j => max P.L (Rs j)) (fun j => le_max_left _ _) h hh dagger
      n n' (hdecay X.2.1) X.1 c
  refine ⟨↥(strSet P p N kind (fun _ => .plain) ζ) × ↥(depthSet (2 * Pm) N), inferInstance, fun X => X.1.1.m, D,
    ?_, fun Rs hRs X => ⟨?_, sum_n_of_mem hp hN X.1.2, fun _ => ?_⟩, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_depthSet]
    have h1 := card_strSet_le P p N kind (fun _ => FixPat.plain) ζ (w := 2 * Pm)
    have e : 2 * (2 * Pm) = 4 * Pm := by ring
    rw [e] at h1
    have h2 : ((N : ℝ) + 1) ^ (4 * Pm) = ((N : ℝ) + 1) ^ (2 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm) := by
      rw [← pow_add]; ring_nf
    rw [h2, ← mul_assoc]
    push_cast
    gcongr
    exact_mod_cast h1
  · show ∑ c, 2 * X.1.1.R c = 4 * Pm
    rw [sum_two_R (valid_of_mem X.1.2) (capSgn ζ)]
    ring
  · have := prod_gain hp hN hst t s b hb X.2.1 (fun j => some (Rf j)) hRf' (fun j => max P.L (Rs j))
      (fun j => le_max_left _ _) h hh dagger n n' (hdecay X.2.1) X.1
    refine this.trans (Finset.prod_congr rfl fun j _ => ?_)
    rw [max_eq_right (le_of_mem_shellBox hL hRs j)]
  · rw [CapsFub.coreG_shell_exchange P hL p N kind dagger h b hb hh Rf hRf j₂ hj₂ ζ t s n n']
    refine setIntegral_congr_fun (CapsFub.measurableSet_shellBox _ _ _) fun R hR => ?_
    have hRL : ∀ j, P.L ≤ R j := le_of_mem_shellBox hL hR
    rw [flowerWeighted_eq_capSum]
    -- the depth sum at every carrier garden
    have hLG : ∀ LG ∈ carrierF P p N kind (fun _ => FixPat.plain) ζ,
        kernelKgen P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p) (capFix LG (fun _ => .plain) t s)
          (capOff LG dagger) (capW LG dagger (fun k => Typed.frontierW LG p (fun j => some (Rf j)) k *
            CapsFub.shellIntegrand LG P.L k R * Typed.leafProd LG h k)) (fun _ => t) 0 (capRoots (fun _ => n) n') 0 =
        ∑ kk ∈ depthSet (2 * Pm) N, capVal P p (fun _ => .plain) (capKSel kk) (capExt (fun j => some (Rf j)) none)
          (fun _ => none) (capExt R P.L) (capH h) (capDag dagger) (capRoots (fun _ => n) n') t s (capLayered LG p) := by
      intro LG hLG
      have hc := (Set.Finite.mem_toFinset _).1 hLG
      have hF := oneFlower_of_isFlowerGarden hc.1.1
      have hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p :=
        fun ℓ hℓ => hc.1.2.1 _ ⟨ℓ, hℓ, GNode.isDesc_refl _⟩
      have hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ N := fun j b hb' => by
        have := stemSet_length_le_order LG j b hb'
        rwa [hc.2.2.1] at this
      rw [capW_shell_depth LG p hF hfl P.L N hM Rf R h dagger, capFix_eq_fixCap LG p hF,
        capOff_eq_offCap LG p hF]
      have hlin := Polar.kernelKgen_linear_step P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p)
        (fixCap (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => FixPat.plain) .plain) t s)
        (offCap (capLayered LG p) (capJ (2 * Pm)) (capDag dagger).isSome) (fun _ => t) 0 (capRoots (fun _ => n) n') 0
        (depthSet (2 * Pm) N) (fun _ => 1) 1
        (fun k => ∑ kk ∈ depthSet (2 * Pm) N, capWt (capLayered LG p) (capJ (2 * Pm)) p P.L (capKSel kk)
          (capExt (fun j => some (Rf j)) none) (fun _ => none) (capExt R P.L) (capH h) (capDag dagger) k)
        (fun kk => capWt (capLayered LG p) (capJ (2 * Pm)) p P.L (capKSel kk) (capExt (fun j => some (Rf j)) none)
          (fun _ => none) (capExt R P.L) (capH h) (capDag dagger))
        (fun κ => by simp only [one_mul])
        (fun kk _ => summable_capped hL hc _ _ _ _ _ _ h b hb hh _ t n n')
      simp only [Complex.ofReal_one, one_mul] at hlin
      exact hlin
    refine (Finset.sum_congr rfl hLG).trans ?_
    rw [Finset.sum_comm, ← Finset.sum_coe_sort (depthSet (2 * Pm) N)]
    -- each depth label decomposes as in Core-F
    have hdep : ∀ kk : ↥(depthSet (2 * Pm) N),
        ∑ LG ∈ carrierF P p N kind (fun _ => FixPat.plain) ζ, capVal P p (fun _ => .plain) (capKSel kk.1)
          (capExt (fun j => some (Rf j)) none) (fun _ => none) (capExt R P.L) (capH h) (capDag dagger)
          (capRoots (fun _ => n) n') t s (capLayered LG p) =
        ∑ x : ↥(strSet P p N kind (fun _ => .plain) ζ), ∏ c : Fin x.1.m, (D R (x, kk) c).val := by
      intro kk
      refine (sum_carrier_eq_prod hp hN _ _ _ _ _ _ _ t s (hs_classX hL t s b hb _ _ _ _ h hh _ n n')).trans
        (Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun c _ => ?_)
      rw [val_compData, capExt_const, capExt_max_eq R hRL]
      rfl
    rw [Finset.sum_congr rfl fun kk _ => hdep kk, Fintype.sum_prod_type]
    exact Finset.sum_comm

/-- **`CapsDecompG`** (all parameters), from the label twist stability. -/
theorem capsDecompG_of_stable (hst : CapsTwistStable) : CapsDecompG :=
  fun Pm P => capsDecompGAt_of_stable hst Pm P

end WaveTurbulence.Flower.CapsComp
