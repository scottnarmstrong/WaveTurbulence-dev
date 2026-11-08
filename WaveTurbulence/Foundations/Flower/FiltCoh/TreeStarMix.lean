/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarId

/-! # FILT-COH (c2): a star-weighted layer-zero paired tree as a presentation mixture

* `kernelLeavesW_tree_star_eq`: the star-weighted kernel is the presentation integral of root characters times the
  character-twisted lattice source sum (`kernelLeavesW_tree_lattice`, `tree_starWeight_eq_value`, main's root
  independence of the tree coefficient, `star_swap`).
* `tree_char_inner_eq`: the character-twisted lattice source sum is main's moving-root mixture of tree profile
  scalars at shifted modulations (main's `tree_bounded_mixture_eq_source` and `tree_leaf_mixture_finite_profiles`
  with the twisted Wick weight, then `treeProfileArrayScalar_char`).
* `stronglyMeasurable_treeNormalizedScalar_param`: main's joint measurability of the normalized tree scalar, with a
  measurable family parameter. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

/-- **The star-weighted tree kernel as a presentation mixture.** -/
theorem kernelLeavesW_tree_star_eq {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hwf : X.wf = true) (h0 : ∀ a, LG.layer a = 0) (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    {K M : ℕ} {B : ℝ} (hK : d+1 ≤ K) (hM : 2*d ≤ M) (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm K M (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B)
    (J : ℕ) (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ Sset, IncTop.StarPresented J (ω a) (cω a))
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 (IncTop.starWeight Sset ω) =
      ∫ a, (IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.amplitude a *
          rootChar ((IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).root a) k *
        ((coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
          ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
            ((Real.fourierChar (inner ℝ
              ((IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.frequency a)
                (pairedLattice L p)) : ℂ) *
              RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
            (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
              (fun j i => latticePoint L (p (j,i))))
        ∂(IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX)).base.μ := by
  set Gm := IncTop.starRootMeasure J Sset ω cω hpres (IncTop.treeRow hX) with hGm
  rw [kernelLeavesW_tree_lattice L γ δ LG hX H t s k]
  have hroot (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) :
      RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s k p =
        RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p :=
    RA1Leafwise.treeOriginalLatticeCoefficient_root_independent L γ δ LG hX hwf h0 hs hst ht p k 0
  simp_rw [hroot]
  exact star_swap Gm L k _ (fun p => IncTop.tree_starWeight_eq_value hX J Sset ω cω hpres L k p) _ _
    (fun p => RA1Leafwise.treeOriginalLatticeCoefficient_norm_le L γ δ LG hX h0 t s 0 p)
    ((treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice hd _ hL hK hM hf k) _

/-- **The character-twisted tree source sum is a moving-root mixture at shifted modulations.** -/
theorem tree_char_inner_eq {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a = 0)
    {I : Type*} [Fintype I] (c : I → ℂ) (J : I → Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
    (C : (i : I) → ({j : Fin (X.treeLinks (LG.garden.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) {L : ℝ} (hL : 1 ≤ L) (μ γ δ t s : ℝ)
    (hH : RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)
    {K M : ℕ} {B Ccover : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ b, Fourier.spatialNorm K M (RA1Leafwise.treeInputFunctionsL LG H b) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    (k : Mom d) (ν : PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) :
    ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
          (fun j i => latticePoint L (p (j,i))) =
      ∑ i, c i * ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX
          (fun lam β γ' z => treeProfileArrayScalar L μ RA1Leafwise.treeWickArrayWeight z
            (shiftL β ν 0) (shiftL γ' ν 1) (J i) (C i) lam) S lam u) ![t,s] ∂treeLeafCellMeasure S := by
  let Hν : ((Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) → ℂ := fun g =>
    arrayChar ν L g * RA1Leafwise.treeOriginalArrayCoefficient L γ δ LG hX t s g
  have hHν : ∀ g, ‖Hν g‖ ≤ 1 := fun g => by
    simp only [Hν, norm_mul, norm_arrayChar, one_mul]
    exact RA1Leafwise.treeOriginalArrayCoefficient_norm_le L γ δ LG hX h0 t s g
  have hsrc := tree_bounded_mixture_eq_source hX hL Hν zero_le_one hHν (RA1Leafwise.treeInputFunctionsL LG H) hK hM hB hf S hcover hS k
  let E := (linkLatticeArrayEquiv (Fin (X.treeLinks (LG.garden.sig 0)).length) (Fin d → ℤ)).trans
    (Equiv.arrowProdEquivProdArrow (Fin (X.treeLinks (LG.garden.sig 0)).length) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ))
  have hEs (g : (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) :
      E.symm g = fun p => if p.2 = 0 then g.1 p.1 else g.2 p.1 := rfl
  have hstep : (∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
        ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
          RA1Leafwise.treeOriginalLatticeCoefficient L γ δ LG hX t s 0 p) *
        (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k (fun j i => latticePoint L (p (j,i)))) =
      ∑' g, Hν g * (treeCarrier hX).sourceLeafWeight (RA1Leafwise.treeInputFunctionsL LG H) k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
    refine (E.symm.tsum_eq _).symm.trans (tsum_congr fun g => ?_)
    rw [hEs g, fourierChar_pairedLattice]
    have hx : (fun j i => latticePoint L ((fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 => if p.2 = 0 then g.1 p.1 else g.2 p.1) (j,i))) =
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
      funext j i
      fin_cases i <;> rfl
    rw [hx]
    rfl
  rw [hstep, ← hsrc]
  let Wν : ((Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ) × (Fin (X.treeLinks (LG.garden.sig 0)).length → Fin d → ℤ)) → ℂ := fun g =>
    arrayChar ν L g * RA1Leafwise.treeWickArrayWeight g
  have hWν : ∀ g, ‖Wν g‖ ≤ 1 := fun g => by
    simp only [Wν, norm_mul, norm_arrayChar, one_mul]
    exact RA1Leafwise.treeWickArrayWeight_norm_le g
  have hHW : Hν = fun g => Wν g * ∑ i, c i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
      (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*
        e2 lam ((![t,s] : Fin 2 → ℝ) 0) ((![t,s] : Fin 2 → ℝ) 1) := by
    funext g
    simp only [Hν, Wν, hH]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hHW, tree_leaf_mixture_finite_profiles hX hL μ Wν zero_le_one hWν c J C hC (RA1Leafwise.treeInputFunctionsL LG H) hK hM hB hf S hS ![t,s] k]
  simp only [Wν, treeProfileArrayScalar_char]

/-- Main's joint measurability of the normalized tree scalar, with a measurable family parameter. -/
theorem stronglyMeasurable_treeNormalizedScalar_param {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {α : Type*} [MeasurableSpace α]
    (R : α → (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : α × ((ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d))) =>
        R p.1 p.2.1 p.2.2.1 p.2.2.2 z))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) ×
        ((SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) =>
      treeNormalizedScalar hX (R p.2.2) S p.1 p.2.1) := by
  have hm : Measurable (fun p : SourceCellIndex S ×
      (α × ((ℝ × ℝ) × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ))) =>
      R p.2.1 p.2.2.1 (treeLeafModulations hX p.2.2.2).1 (treeLeafModulations hX p.2.2.2).2 p.1.2.val /
        (treeLeafModulationWeight p.2.2.2:ℂ)) := by
    apply measurable_from_prod_countable_right
    intro cell
    have hmap : Measurable (fun p : α × ((ℝ × ℝ) × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) =>
        (p.1, (p.2.1, treeLeafModulations hX p.2.2))) :=
      measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((continuous_treeLeafModulations hX).measurable.comp measurable_snd.snd))
    have hscalar := (hR cell.2.val).comp_measurable hmap
    exact hscalar.measurable.div (Complex.continuous_ofReal.measurable.comp
      (continuous_treeLeafModulationWeight.measurable.comp (measurable_snd.comp measurable_snd)))
  have hp : Measurable (fun p : (ℝ × ℝ) ×
      ((SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) × α) =>
        (p.2.1.1, (p.2.2, (p.1, p.2.1.2)))) :=
    measurable_snd.fst.fst.prodMk (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst.snd))
  exact (hm.comp hp).stronglyMeasurable

end WaveTurbulence.Flower.FiltCoh
