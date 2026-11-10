/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FibreSum
public import WaveTurbulence.Foundations.Spine.ChainBound
public import WaveTurbulence.Foundations.Spine.RungTotal
public import WaveTurbulence.Foundations.Spine.TimeReindex
public import WaveTurbulence.Foundations.Spine.LadderTime
public import WaveTurbulence.Foundations.Spine.FiniteSupp
/-! # The core bound for the local ladder kernel (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

/-- The pair of times of the interior rungs, as engine variables `(t_v, t_u)`. -/
noncomputable def tauOf (t : (Molecule.ladderAtoms u v) → ℝ) : Fin n → ℝ × ℝ :=
  fun k => (tExt _ t (v (LadderDarts.ir k)), tExt _ t (u (LadderDarts.ir k)))

/-- Edge amplitude of a chain code. -/
noncomputable def edgeF (D : SplicedKernelData G d) : LadderDarts.Ctx.Code n → Mom d → ℂ :=
  fun c => D.edgeAmplitude (C.outDart c)

/-- Centre of a chain code. -/
noncomputable def edgeCtr (D : SplicedKernelData G d) : LadderDarts.Ctx.Code n → Mom d :=
  fun c => D.center (C.outDart c)

include C in
lemma edgeF_snorm (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (c : LadderDarts.Ctx.Code n) :
    SNorm (30 * d) 0 (C.edgeF D c) ≤ ENNReal.ofReal 1 := by
  have := (hD.2.1 (C.outDart c) (by simp [Molecule.bonds, C.out_outDart c])).1
  rw [ENNReal.ofReal_one]
  exact this

include C in
lemma edgeF_supp (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (c : LadderDarts.Ctx.Code n)
    (x : Mom d) (hx : 1 < ‖x - C.edgeCtr D c‖) : C.edgeF D c x = 0 :=
  (hD.2.1 (C.outDart c) (by simp [Molecule.bonds, C.out_outDart c])).2 x hx


lemma chainLab_eval_labOf {n : ℕ} (S : ChainSigns n) (a0 b0 : Fin d → ℤ) (P : Fin n → Pt d)
    (c : LadderDarts.Ctx.Code n) :
    (chainLab S a0 b0 c).eval P = LadderDarts.Ctx.labOf (S.inv a0 b0 P) c := by
  rw [chainLab_eval]
  rcases c with ⟨i, k⟩ | j | j <;> rfl


lemma windowOK_of_layers {T1 L δ γ : ℝ} {lu lv : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hlu : 0 ≤ lu) (hlv : 0 ≤ lv) (h1 : δ * (lu + 1) ≤ T1) (h2 : δ * (lv + 1) ≤ T1) :
    WindowOK T1 L (δ * L ^ (2 * γ)) lu (lu + 1) lv (lv + 1) γ := by
  intro t ht
  have hp : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  have hc : 0 < δ * L ^ (2 * γ) := mul_pos hδ hp
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · have : δ * L ^ (2 * γ) * (lv + 1) ≤ T1 * L ^ (2 * γ) := by nlinarith
    nlinarith
  · have : δ * L ^ (2 * γ) * (lu + 1) ≤ T1 * L ^ (2 * γ) := by nlinarith
    nlinarith

lemma abs_epsCoef_le (a b c : Fin d → ℤ) : |epsCoef a b c| ≤ 1 := by
  unfold epsCoef; split_ifs <;> simp

lemma abs_gapAtomSpec_le {a : GBranch G.tree} (spec : Option (LocalGapSpecification G a)) (L γ η : ℝ)
    (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : |gapAtomSpec spec L γ η base z| ≤ 1 := by
  rcases spec with _ | q
  · simp [gapAtomSpec]
  · simp only [gapAtomSpec]; split_ifs <;> simp

lemma abs_atomFac_le (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (zz : GNode G.tree → (Fin d → ℤ)) (a : GBranch G.tree) : |atomFac D L γ η base zz a| ≤ 1 := by
  unfold atomFac
  rw [abs_mul]
  exact mul_le_one₀ (abs_epsCoef_le _ _ _) (abs_nonneg _) (abs_gapAtomSpec_le _ _ _ _ _ _)

include C in
lemma norm_classTheta_le (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (L γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (zs : GenDecoration G d roots 0)
    (t : (Molecule.ladderAtoms u v) → ℝ) : ‖C.classTheta D L γ η δ base roots zs t‖ ≤ 1 := by
  classical
  unfold classTheta
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖((∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, atomFac D L γ η base zs.1 a : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun a _ => abs_atomFac_le D L γ η base zs.1 a)
  have h2 : ‖∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, phaseAt D L γ δ base zs.1 a (tExt _ t a)‖ = 1 := by
    rw [norm_prod]; exact Finset.prod_eq_one (fun a _ => norm_phaseAt _ _ _ _ _ _ _ _)
  have h3 : ‖∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G zs.1 x))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun x hx => ?_)
    have hxb : x ∈ G.molecule.bonds := (Finset.mem_filter.mp hx).1
    have hSN := (hD.2.1 x hxb).1
    have := Sumint.weighted_norm_le_of_SNorm_le (N := 30 * d) (K := 0) (F := D.edgeAmplitude x)
      (B := 1) (by norm_num) (by rw [ENNReal.ofReal_one]; exact hSN) (base + latticePoint L (bondIndex G zs.1 x))
    simpa using this
  have h4 : ‖∏ i : Fin n, Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) *
        ((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ)) *
        ‖latticePoint L (C.signs.qrel (C.chainOf (bondIndex G zs.1)) i)‖ ^ 2 +
        D.frequency (v (LadderDarts.ir i))) * tExt _ t (v (LadderDarts.ir i)) +
        D.frequency (u (LadderDarts.ir i)) * tExt _ t (u (LadderDarts.ir i))) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_prod]; exact Finset.prod_eq_one (fun i _ => Complex.norm_exp_ofReal_mul_I _)
  rw [h2, h4]
  have : ‖∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G zs.1 x))‖ * 1 ≤ 1 := by simpa using h3
  nlinarith [norm_nonneg ((∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G zs.1 x))))]

open scoped Classical in
include C in
/-- **One class.** -/
theorem class_bound (hP : G.IsPlain) {L : ℝ} (hL0 : 0 < L) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (hd : 1 ≤ d)
    (γ η δ x T1 C0 : ℝ) (hδ : 0 < δ) (hρ : 0 ≤ L ^ (-γ + η)) (hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η))
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x T1 δ L C0 a b χ)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 1) ≤ T1)
    (boundary : GardenDart G → (Fin d → ℤ))
    (T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hTw : ∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0)
    (hTz : ∀ z, z ∉ T → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0)
    (zs : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)) (hzs : zs ∈ T) :
    ∃ H : (Fin n → ℝ × ℝ) → ℝ, Continuous H ∧
      (∀ t : (Molecule.ladderAtoms u v) → ℝ,
        ‖∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
            bondIndex G z.1.1 x = bondIndex G zs.1.1 x),
          ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
            ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤ H (tauOf (u := u) (v := v) t)) ∧
      ∫ τ in Set.pi Set.univ (fun k : Fin n =>
          Icc (D.layer (v (LadderDarts.ir k)) : ℝ) (D.layer (v (LadderDarts.ir k)) + 1) ×ˢ
          Icc (D.layer (u (LadderDarts.ir k)) : ℝ) (D.layer (u (LadderDarts.ir k)) + 1)), H τ ≤
        (Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
          ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
            ∏ k : Fin n, rungBudget d γ x δ L C0
              ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
               (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))) := by
  have hL : L ≠ 0 := hL0.ne'
  have hsz := C.isSol_dec hP hL base roots hn zs.1
  set a0s := (C.chainOf (bondIndex G zs.1.1)).a 0 with ha0s
  set b0s := (C.chainOf (bondIndex G zs.1.1)).b 0 with hb0s
  set q := a0s - b0s with hq
  set c0 := (C.chainOf (bondIndex G zs.1.1)).a (Fin.last n) - a0s with hc0
  set ca : Fin n → (Fin d → ℝ) := fun k => (pairCentres C.signs (C.edgeCtr D) k).1 with hca
  set cb : Fin n → (Fin d → ℝ) := fun k => (pairCentres C.signs (C.edgeCtr D) k).2 with hcb
  have hGS : ∀ k, GoodSum L (L ^ (1 - γ + η)) (ca k) (cb k) ((Fin 3 × Fin 2) × (Fin 3 × Fin 2))
      (C.rungW D L γ η k q) := fun k => C.rungW_goodSum D γ η L _ hL0 hρ hR k q
  choose s χ hs hχ hw using hGS
  have hχabs : ∀ k j p, |χ k j p| ≤ 1 := fun k j p => (hχ k j).abs_le p
  have hRungk : ∀ k j, RungOK γ x T1 δ L C0 (ca k) (cb k) (χ k j) := fun k j => hRung _ _ _ (hχ k j)
  set lam : Fin n → Pt d →+ ℝ := fun k => lamHom L (δ * L ^ (2 * γ)) C.signs k
    (C.signs.qrel (C.chainOf (bondIndex G zs.1.1)) k) with hlam
  have hcut : ∀ P : Fin n → Pt d,
      (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) ≠ 0 →
      ∀ k, cutW L (ca k) (cb k) (P k) = 1 := by
    intro P hP0 k
    have hball : ∀ c, ‖base + latticePoint L (LadderDarts.Ctx.labOf (C.signs.inv a0s b0s P) c) -
        C.edgeCtr D c‖ ≤ 1 := by
      intro c
      by_contra hcon
      push_neg at hcon
      apply hP0
      refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
      rw [chainLab_eval_labOf]
      exact C.edgeF_supp D hD c _ hcon
    exact pair_cutW_eq_one C.signs (C.edgeCtr D) hL0 base a0s b0s P hball k
  set Hf : (Fin n → ℝ × ℝ) → ℝ := fun τ => ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)),
      (if ∑ k, chainΔ C.signs k (P k) = c0 then
        (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
          (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) *
          ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) *
            rungPh L (δ * L ^ (2 * γ)) (lam k) (τ k) (P k)) else 0)‖ with hHf
  refine ⟨Hf, ?_, ?_, ?_⟩
  · exact (continuous_chain_sum L (δ * L ^ (2 * γ)) lam _ _
      (fun P => ∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P)))
      (fun k p => ((∑ j, s k j * χ k j p : ℝ) : ℂ))).norm
  · intro t
    set f : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) → ℂ := fun z =>
      ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t with hf
    set θ := C.classTheta D L γ η δ base roots zs.1 t with hθdef
    set g : (Fin n → Pt d) → ℂ := fun P =>
      (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) *
      ∏ k : Fin n, (((C.rungW D L γ η k q (P k) : ℝ) : ℂ) *
        rungPh L (δ * L ^ (2 * γ)) (lam k) (tauOf (u := u) (v := v) t k) (P k)) with hg
    have hfac : ∀ z : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
        (∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1.1 x = bondIndex G zs.1.1 x) →
          f z = θ * g (C.signs.pairs (C.chainOf (bondIndex G z.1.1))) := by
      intro z hz
      have := C.weight_phase_factor hP hL base roots hn D γ η δ z.1 zs.1 hz t
      simp only [hf]
      rw [this, mul_assoc]
      rfl
    have hfz : f zs ≠ 0 := by
      simp only [hf]
      refine mul_ne_zero (hTw zs hzs) ?_
      intro h0
      have := norm_ladderPhase D (Molecule.ladderAtoms u v) L γ δ base zs.1.1 t
      rw [h0] at this; simp at this
    have hθ0 : θ ≠ 0 := by
      intro h0
      apply hfz
      rw [hfac zs (fun _ _ => rfl), h0, zero_mul]
    have hgsupp : ∀ P, g P ≠ 0 → ∀ k, P k ∈ cutBox d L (ca k) (cb k) := by
      intro P hP0 k
      have h1 := left_ne_zero_of_mul hP0
      have h2 := hcut P h1 k
      exact cutW_mem_cutBox hL0 _ _ _ (by rw [h2]; exact one_ne_zero)
    have hsum := C.fibre_sum hP hL base roots hn boundary T f
      (fun z hz => by simp only [hf]; rw [hTz z hz, zero_mul]) zs hzs θ g hθ0 hfac
      (fun k => cutBox d L (ca k) (cb k)) hgsupp
    have hnorm := C.norm_classTheta_le D hD L γ η δ base roots zs.1 t
    calc ‖∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
            bondIndex G z.1.1 x = bondIndex G zs.1.1 x),
          ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
            ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖
        = ‖θ * ∑ P ∈ (Fintype.piFinset (fun k => cutBox d L (ca k) (cb k))).filter
            (fun P => ∑ k, chainΔ C.signs k (P k) = c0), g P‖ := by rw [← hsum]
      _ ≤ ‖∑ P ∈ (Fintype.piFinset (fun k => cutBox d L (ca k) (cb k))).filter
            (fun P => ∑ k, chainΔ C.signs k (P k) = c0), g P‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hnorm
      _ = Hf (tauOf (u := u) (v := v) t) := by
          rw [Finset.sum_filter]
          simp only [hHf]
          congr 1
          refine Finset.sum_congr rfl (fun P _ => ?_)
          by_cases hc : ∑ k, chainΔ C.signs k (P k) = c0
          · simp only [hc, if_true, hg]
            congr 1
            refine Finset.prod_congr rfl (fun k _ => ?_)
            rw [hw k (P k)]
          · simp [hc]
  · have hcb := chain_bound (J := (Fin 3 × Fin 2) × (Fin 3 × Fin 2)) hd (γ := γ) (x := x) (T1 := T1) (δ := δ)
      (L := L) (C0 := C0) hL0 ca cb C.signs a0s b0s c0 base (C.edgeF D) (C.edgeCtr D)
      (C.edgeF_snorm D hD) (C.edgeF_supp D hD) s hs χ hχabs hRungk lam
      (fun k => (D.layer (u (LadderDarts.ir k)) : ℝ)) (fun k => (D.layer (u (LadderDarts.ir k)) : ℝ) + 1)
      (fun k => (D.layer (v (LadderDarts.ir k)) : ℝ)) (fun k => (D.layer (v (LadderDarts.ir k)) : ℝ) + 1)
      (fun k => by simp) (fun k => by simp) (fun k => by simp) (fun k => by simp)
      (fun k => windowOK_of_layers hL0 hδ (by positivity) (by positivity) (hlay _) (hlay _)) hcut
    exact hcb

include C in
lemma ir_injective : Function.Injective (LadderDarts.ir (n := n)) := fun a b h => by
  apply Fin.ext; have := congrArg Fin.val h; simp [LadderDarts.ir] at this; exact this

/-- The coordinates of the interior-rung atoms inside the ladder atoms. -/
noncomputable def evIdx (k : Fin n) : ↥(Molecule.ladderAtoms u v) :=
  ⟨v (LadderDarts.ir k), by
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩

noncomputable def euIdx (k : Fin n) : ↥(Molecule.ladderAtoms u v) :=
  ⟨u (LadderDarts.ir k), by
    unfold Molecule.ladderAtoms
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩

include C in
lemma idx_injective : Function.Injective (Sum.elim (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v))) := by
  intro a b h
  rcases a with k | k <;> rcases b with k' | k'
  · have := congrArg Subtype.val h
    simp only [Sum.elim_inl, evIdx] at this
    exact congrArg Sum.inl (C.ir_injective (C.hvinj this))
  · have := congrArg Subtype.val h
    simp only [Sum.elim_inl, Sum.elim_inr, evIdx, euIdx] at this
    exact absurd this.symm (C.hne _ _)
  · have := congrArg Subtype.val h
    simp only [Sum.elim_inl, Sum.elim_inr, evIdx, euIdx] at this
    exact absurd this (C.hne _ _)
  · have := congrArg Subtype.val h
    simp only [Sum.elim_inr, euIdx] at this
    exact congrArg Sum.inr (C.ir_injective (C.huinj this))

lemma tauOf_eq (t : (Molecule.ladderAtoms u v) → ℝ) :
    tauOf (u := u) (v := v) t = fun k => (t (evIdx k), t (euIdx k)) := by
  funext k
  have h1 : v (LadderDarts.ir k) ∈ Molecule.ladderAtoms u v := (evIdx (u := u) (v := v) k).2
  have h2 : u (LadderDarts.ir k) ∈ Molecule.ladderAtoms u v := (euIdx (u := u) (v := v) k).2
  simp [tauOf, tExt, evIdx, euIdx, h1, h2]

/-- The class of a decoration: its labels off the interior atoms. -/
noncomputable def clsOf {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0) :
    GardenDart G → (Fin d → ℤ) :=
  fun x => if G.molecule.atom x ∈ intAtoms u v then 0 else bondIndex G z.1 x

lemma clsOf_eq_iff {roots : Fin w → (Fin d → ℤ)} (z z' : GenDecoration G d roots 0) :
    clsOf (u := u) (v := v) z = clsOf (u := u) (v := v) z' ↔
      ∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1 x = bondIndex G z'.1 x := by
  constructor
  · intro h x hx
    have := congrFun h x
    simpa [clsOf, hx] using this
  · intro h
    funext x
    unfold clsOf
    by_cases hx : G.molecule.atom x ∈ intAtoms u v
    · simp [hx]
    · simp [hx, h x hx]

open scoped Classical in
include C in
/-- **The core bound for the local ladder kernel.** -/
theorem kernel_core (hP : G.IsPlain) {L : ℝ} (hL0 : 0 < L) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (hd : 1 ≤ d)
    (γ η δ x T1 C0 : ℝ) (hδ : 0 < δ) (hC0 : 0 ≤ C0) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η))
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x T1 δ L C0 a b χ)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 1) ≤ T1)
    (outside : GBranch G.tree → ℝ) (boundary : GardenDart G → (Fin d → ℤ)) (NC : ℕ)
    (hNC : ∀ T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) →
        (T.image (fun z => clsOf (u := u) (v := v) z.1)).card ≤ NC) :
    ‖sourceLocalLadderKernel G D (Molecule.ladderAtoms u v) outside L γ η δ base roots boundary‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
        ((NC : ℝ) * ((Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
          ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
            ∏ k : Fin n, rungBudget d γ x δ L C0
              ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
               (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))))) := by
  set S := Molecule.ladderAtoms u v with hS
  set Bt : ℝ := (Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
    ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
      ∏ k : Fin n, rungBudget d γ x δ L C0
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
         (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))) with hBt
  have hBt0 : 0 ≤ Bt := by
    have hcff := cellFourierFactor_nonneg d
    have hbud : ∀ k : Fin n, 0 ≤ rungBudget d γ x δ L C0
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
         (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k))) := by
      intro k
      unfold rungBudget
      have hLx : 0 < L ^ (-x) := Real.rpow_pos_of_pos hL0 _
      have hE : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
      refine mul_nonneg hC0 (mul_nonneg hE ?_)
      split_ifs
      · exact hLx.le
      · exact zero_le_one
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hcff) _) (Finset.prod_nonneg fun k _ => hbud k))
  have hfin := weight_support_finite hP hL0 base D hD S γ η roots boundary
  set T := hfin.toFinset with hTdef
  have hTmem : ∀ z, z ∈ T ↔ ladderWeight D S L γ η base z.1.1 ≠ 0 := fun z => by
    simp [hTdef]
  have hTz : ∀ z, z ∉ T → ladderWeight D S L γ η base z.1.1 = 0 := fun z hz => by
    by_contra h; exact hz ((hTmem z).mpr h)
  have hTw : ∀ z ∈ T, ladderWeight D S L γ η base z.1.1 ≠ 0 := fun z hz => (hTmem z).mp hz
  refine (kernel_norm_le D S outside L γ η δ base roots boundary T hTz).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hTe : T.Nonempty
  swap
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTe
    rw [this]
    simp only [Finset.sum_empty, norm_zero]
    simp only [MeasureTheory.integral_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hBt0
  obtain ⟨z0, hz0⟩ := hTe
  have hcb := fun zs (hzs : zs ∈ T) => C.class_bound hP hL0 base roots hn D hD hd γ η δ x T1 C0 hδ hρ hR hRung
    hlay boundary T hTw hTz zs hzs
  choose! H hHc hHp hHi using hcb
  set cls : ↥(localLadderDecorations G S roots boundary) → (GardenDart G → (Fin d → ℤ)) :=
    fun z => clsOf (u := u) (v := v) z.1 with hcls
  set 𝒞 := T.image cls with h𝒞
  set rep : (GardenDart G → (Fin d → ℤ)) → ↥(localLadderDecorations G S roots boundary) :=
    fun c => if h : ∃ zs ∈ T, cls zs = c then Classical.choose h else z0 with hrep
  have hrepc : ∀ c ∈ 𝒞, rep c ∈ T ∧ cls (rep c) = c := by
    intro c hc
    obtain ⟨zs, hzs, hzc⟩ := Finset.mem_image.mp hc
    have hex : ∃ zs ∈ T, cls zs = c := ⟨zs, hzs, hzc⟩
    simp only [hrep, dif_pos hex]
    exact Classical.choose_spec hex
  have hpt : ∀ t : ↥S → ℝ, ‖∑ z ∈ T, ladderWeight D S L γ η base z.1.1 *
      ladderPhase D S L γ δ base z.1.1 t‖ ≤ ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) := by
    intro t
    have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := 𝒞) (g := cls)
      (fun z hz => Finset.mem_image_of_mem cls hz)
      (fun z => ladderWeight D S L γ η base z.1.1 * ladderPhase D S L γ δ base z.1.1 t)
    rw [← hfib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c hc => ?_))
    obtain ⟨hrT, hrc⟩ := hrepc c hc
    have heq : T.filter (fun z => cls z = c) = T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
        bondIndex G z.1.1 x = bondIndex G (rep c).1.1 x) := by
      refine Finset.filter_congr (fun z _ => ?_)
      have h1 : cls z = c ↔ cls z = cls (rep c) := by rw [hrc]
      exact h1.trans (clsOf_eq_iff (u := u) (v := v) z.1 (rep c).1)
    rw [heq]
    exact hHp (rep c) hrT t
  have hre : ∀ G' : (Fin n → ℝ × ℝ) → ℝ,
      (∫ t in timeBox G D.layer S, G' (tauOf (u := u) (v := v) t)) =
        ∫ τ in Set.pi Set.univ (fun k : Fin n =>
          Icc (D.layer (v (LadderDarts.ir k)) : ℝ) (D.layer (v (LadderDarts.ir k)) + 1) ×ˢ
          Icc (D.layer (u (LadderDarts.ir k)) : ℝ) (D.layer (u (LadderDarts.ir k)) + 1)), G' τ := by
    intro G'
    have := integral_time_reindex (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)) C.idx_injective
      (fun a : ↥S => Icc (D.layer a.1 : ℝ) (D.layer a.1 + 1)) (fun a => measurableSet_Icc) G'
    have hvol : (∏ r : {a : ↥S // a ∉ Set.range (Sum.elim (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)))},
        (volume (Icc (D.layer r.1.1 : ℝ) (D.layer r.1.1 + 1))).toReal) = 1 := by
      refine Finset.prod_eq_one (fun r _ => ?_)
      simp [Real.volume_Icc]
    rw [hvol, one_mul] at this
    simp only [tauOf_eq]
    exact this
  have hI1 : IntegrableOn (fun t : ↥S → ℝ => ‖∑ z ∈ T, ladderWeight D S L γ η base z.1.1 *
      ladderPhase D S L γ δ base z.1.1 t‖) (timeBox G D.layer S) := by
    have hc : Continuous (fun t : ↥S → ℝ => ∑ z ∈ T, ladderWeight D S L γ η base z.1.1 *
        ladderPhase D S L γ δ base z.1.1 t) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul (continuous_ladderPhase D S L γ δ base z.1.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_timeBox G D.layer S)
  have hcontH : ∀ c ∈ 𝒞, Continuous (fun t : ↥S → ℝ => H (rep c) (tauOf (u := u) (v := v) t)) := by
    intro c hc
    have hcτ : Continuous (fun t : ↥S → ℝ => tauOf (u := u) (v := v) t) := by
      simp only [tauOf_eq]
      exact continuous_pi (fun k => (continuous_apply _).prodMk (continuous_apply _))
    exact (hHc (rep c) (hrepc c hc).1).comp hcτ
  have hIH : ∀ c ∈ 𝒞, IntegrableOn (fun t : ↥S → ℝ => H (rep c) (tauOf (u := u) (v := v) t))
      (timeBox G D.layer S) := fun c hc =>
    (hcontH c hc).continuousOn.integrableOn_compact (isCompact_timeBox G D.layer S)
  calc ∫ t in timeBox G D.layer S, ‖∑ z ∈ T, ladderWeight D S L γ η base z.1.1 *
          ladderPhase D S L γ δ base z.1.1 t‖
      ≤ ∫ t in timeBox G D.layer S, ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_mono hI1 (integrable_finsetSum _ hIH) (fun t => hpt t)
    _ = ∑ c ∈ 𝒞, ∫ t in timeBox G D.layer S, H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_finsetSum _ hIH
    _ = ∑ c ∈ 𝒞, ∫ τ in Set.pi Set.univ (fun k : Fin n =>
          Icc (D.layer (v (LadderDarts.ir k)) : ℝ) (D.layer (v (LadderDarts.ir k)) + 1) ×ˢ
          Icc (D.layer (u (LadderDarts.ir k)) : ℝ) (D.layer (u (LadderDarts.ir k)) + 1)), H (rep c) τ :=
        Finset.sum_congr rfl (fun c _ => hre _)
    _ ≤ ∑ _c ∈ 𝒞, Bt := Finset.sum_le_sum (fun c hc => hHi (rep c) (hrepc c hc).1)
    _ = (𝒞.card : ℝ) * Bt := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (NC : ℝ) * Bt := by
        refine mul_le_mul_of_nonneg_right ?_ hBt0
        exact_mod_cast hNC T hTw

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
