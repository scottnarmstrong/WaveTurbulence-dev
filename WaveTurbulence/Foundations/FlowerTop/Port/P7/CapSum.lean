/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapIdentity
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSurj
/-! FLOWER-P7: summability of the decoration sum of `kernelKgen` with designated nodes, and the sum-level
decapitation identity.  The injectivity proof is copied from `WaveBDraft.summable_kernelK_summand`
(`WaveBDraft/Lemmas.lean` L713, sha recorded in COPIED-SHA256SUMS). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- A decoration is determined by its input-leaf values (at most one lone leaf per tree). -/
theorem decoration_injective_of_inputs {w d : ℕ} (LG : LayeredGarden w) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) :
    Function.Injective fun (κ : GenDecoration LG.garden d nroot nfl)
      (ℓ : {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}) => κ.1 ℓ.1.toNode := by
  classical
  have hlone' : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsLone ℓ → LG.garden.IsLone ℓ' →
      ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ' := fun ℓ ℓ' h h' hj =>
    Finset.card_le_one.1 (hlone ℓ.1.1) ℓ (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, h⟩) ℓ'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.symm, h'⟩)
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let Φ : GenDecoration LG.garden d nroot nfl → (ι → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.1.toNode
  have hΦ : Function.Injective Φ := by
    intro κ κ' hκ
    let δ : GNode LG.garden.tree → (Fin d → ℤ) := fun a => κ.1 a - κ'.1 a
    have hδb : ∀ b : GBranch LG.garden.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2) := by
      intro b
      simp only [δ, κ.2.1.1 b, κ'.2.1.1 b]
      abel
    have hin : ∀ ℓ ∈ inputLeaves LG.garden, δ ℓ.toNode = 0 := fun ℓ hℓ => by
      have := congrFun hκ ⟨ℓ, hℓ⟩
      simp only [Φ] at this
      simp [δ, this]
    have hleaf : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsLone ℓ → δ ℓ.toNode = 0 := by
      intro ℓ hnl
      by_cases hm : LG.garden.mark ℓ = none
      · by_cases hs : LG.garden.sign ℓ.toNode = 1
        · exact hin ℓ (by simp [inputLeaves, hs, hm])
        · -- a minus leaf: use its (plus) partner
          have hne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
          have hs' : LG.garden.sign ℓ.toNode = -1 := by
            rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with h | h
            · exact absurd h hs
            · exact h
          have hpm : LG.garden.mark (LG.garden.pair ℓ) = none := by
            by_contra h
            have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 h
            rw [LG.garden.pair_pair] at this
            exact hne this.symm
          have hps : LG.garden.sign (LG.garden.pair ℓ).toNode = 1 := by
            have := LG.garden.pair_sign ℓ hne
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = -nodeSign LG.garden.sig ℓ.1 at this
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
            rw [this]
            change -LG.garden.sign ℓ.toNode = 1
            rw [hs']
            rfl
          have h0 := hin (LG.garden.pair ℓ) (by simp [inputLeaves, hps, hpm])
          simp only [δ] at h0 ⊢
          rw [κ.2.1.2 ℓ, κ'.2.1.2 ℓ]
          exact h0
      · -- a marked leaf that is not lone is a flower
        have hfl : LG.garden.IsFlower ℓ := by
          rcases hmk : LG.garden.mark ℓ with _ | tag
          · exact absurd hmk hm
          · cases tag
            · exact absurd hmk hnl
            · exact hmk
        simp [δ, κ.2.2.2 ℓ hfl, κ'.2.2.2 ℓ hfl]
    have hroot : ∀ j, δ (GNode.root LG.garden.tree j) = 0 := fun j => by
      simp [δ, κ.2.2.1 j, κ'.2.2.1 j]
    apply Subtype.ext
    funext a
    exact sub_eq_zero.1
      (eq_zero_of_roots_leaves_zero δ hδb LG.garden.IsLone hlone' hroot hleaf a)
  exact hΦ

/-- The pinned phase integral is bounded by the volume of the unit box of the free times. -/
theorem norm_pinnedIntegral_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    ‖∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
        (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden ∅ k) (LG.garden.extendFix fix τ)‖ ≤
      (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) := by
  set Box : Set ({b : GBranch LG.garden.tree // fix b = none} → ℝ) :=
    Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  rw [← integral_indicator_one hBm]
  refine norm_integral_le_of_norm_le ((integrable_indicator_iff hBm).2
    (integrableOn_const hBc.measure_lt_top.ne)) (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hD : LG.garden.extendFix fix τ ∈ kDomainFix LG up fix
  · have hτ : τ ∈ Box := fun b _ => by
      have h := (hD b.1).1 b.2
      rw [extendFix_none LG.garden fix τ b.1 b.2] at h
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
    simp only [phaseProdOff, norm_prod, Finset.notMem_empty, ite_false]
    refine le_of_eq (Finset.prod_eq_one fun b _ => ?_)
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- Absolute summability of the decoration sum of `kernelKgen` (no removed phases, weight `1`). -/
theorem summable_kgTerm {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      kgTerm L γ δ F LG fix ∅ (fun _ => 1) up k₀ κ.1 := by
  classical
  refine Summable.of_norm ?_
  have hΦ := decoration_injective_of_inputs LG nroot nfl hlone
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |F (LG.layer ℓ.1.toNode) (k₀ + latticePoint L n)|
  have hf : Summable fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) fun ℓ => hF ℓ.1 ℓ.2
  set C := (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
    (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_)
    ((hf.comp_injective hΦ).mul_left C)
  unfold kgTerm
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Function.comp_apply, norm_one]
  have hprod : ∏ ℓ ∈ inputLeaves LG.garden, |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| =
      ∏ ℓ : ι, f ℓ (κ.1 ℓ.1.toNode) := by
    rw [← Finset.prod_coe_sort]
    rfl
  rw [hprod]
  have hC : 0 ≤ C := measureReal_nonneg
  have hP : 0 ≤ ∏ ℓ : ι, f ℓ (κ.1 ℓ.1.toNode) := Finset.prod_nonneg fun _ _ => abs_nonneg _
  calc _ ≤ 1 * 1 * C * ∏ ℓ : ι, f ℓ (κ.1 ℓ.1.toNode) := by
        gcongr
        · exact abs_epsDec_le_one LG.garden κ.1
        · exact norm_pinnedIntegral_le L γ δ LG up fix _
    _ = C * ∏ ℓ : ι, f ℓ (κ.1 ℓ.1.toNode) := by ring

/-- The sources of decapitation: width-six layered gardens with the alternating child signature and all
layers `≤ p`. -/
abbrev CapSrc (p : ℕ) : Type :=
  {LG : LayeredGarden (2 * 3) // (∀ c, LG.garden.sig c = childSig c) ∧ ∀ a, LG.layer a ≤ p}

/-- The cap of a source. -/
noncomputable def CapSrc.cap {p : ℕ} (y : CapSrc p) : LayeredGarden 2 :=
  capLayered y.1 y.2.1 p y.2.2

theorem CapSrc.cap_injective (p : ℕ) : Function.Injective (CapSrc.cap (p := p)) := fun y y' h =>
  Subtype.ext (capLayered_injective y.1 y'.1 y.2.1 y'.2.1 p y.2.2 y'.2.2 h)

/-- A couple with the alternating-sign shape, branching roots and roots in layer `p` is a cap. -/
theorem exists_capSrc {p : ℕ} (Q : LayeredGarden 2) (hc : Q.garden.sig = ![1, -1])
    (hroot : ∀ j, Q.garden.tree j ≠ TTree.leaf) (hp : ∀ x, Q.layer x ≤ p)
    (hl : ∀ (j : Fin 2) (b : GBranch Q.garden.tree), b.1 = (j, []) → Q.layer b.toNode = p) :
    ∃ y : CapSrc p, y.cap = Q := by
  obtain ⟨LG, hsig, hp6, h⟩ := exists_cap_layered Q hc hroot p hp hl
  exact ⟨⟨LG, hsig, hp6⟩, h⟩

/-- **Sum-level decapitation identity** (T L2312, L2340; the `∂_t` term).  For a set `A` of couples that are
plain, have branching roots in layer `p` (all of them, as in `coupleSum` with `dt = true`) and layers `≤ p`,
the sum of the pinned-root kernels over `A` equals the sum over the decapitated sources of
`c² ∑_n outerWeight · kernelKgen` (six-tree garden kernels with caps `t`). -/
theorem finsum_cap_eq {p : ℕ} (A : Set (LayeredGarden 2))
    (hA : ∀ Q ∈ A, Q.garden.sig = ![1, -1] ∧ Q.garden.IsPlain ∧ (∀ j, Q.garden.tree j ≠ TTree.leaf) ∧
      (∀ x, Q.layer x ≤ p) ∧
      ∀ (j : Fin 2) (b : GBranch Q.garden.tree), b.1 = (j, []) → Q.layer b.toNode = p)
    (g : LayeredGarden 2 → ℂ) :
    ∑ᶠ (Q : LayeredGarden 2) (_ : Q ∈ A), g Q =
      ∑ᶠ (y : CapSrc p) (_ : y.cap ∈ A), g y.cap := by
  classical
  have himg : A = (CapSrc.cap (p := p)) '' {y | y.cap ∈ A} := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨h1, -, h3, h4, h5⟩ := hA Q hQ
      obtain ⟨y, hy⟩ := exists_capSrc Q h1 h3 h4 h5
      exact ⟨y, by simpa [hy] using hQ, hy⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  conv_lhs => rw [himg]
  rw [finsum_mem_image (CapSrc.cap_injective p).injOn]
  rfl

/-- The conditions of `coupleSum` other than the time pinning (T L2312). -/
def CoupleCond (P : WTParams) (p N : ℕ) (kind : TreeKind) (Q : LayeredGarden 2) : Prop :=
  IsCanonC (p + 1) Q ∧ (∀ u ∈ Q.attachNodes p, Q.attachedOrder p u ≤ P.N p) ∧ Q.garden.order = N ∧
    Q.TreeKindOK p (P.N (p + 1)) kind ∧
    ∀ j : Fin 2, ∃ b : GBranch Q.garden.tree, b.1 = (j, []) ∧ Q.layer b.toNode = p

theorem tree_ne_leaf_of_branch {w : ℕ} {T : Fin w → TTree} (b : GBranch T) (j : Fin w) (h : b.1 = (j, [])) :
    T j ≠ TTree.leaf := by
  intro hl
  have hb := b.2
  rw [h] at hb
  simp [hl, TTree.branching] at hb

theorem coupleCond_facts (P : WTParams) (p N : ℕ) (kind : TreeKind) (Q : LayeredGarden 2)
    (hQ : CoupleCond P p N kind Q) :
    Q.garden.sig = ![1, -1] ∧ Q.garden.IsPlain ∧ (∀ j, Q.garden.tree j ≠ TTree.leaf) ∧
      (∀ x, Q.layer x ≤ p) ∧
      ∀ (j : Fin 2) (b : GBranch Q.garden.tree), b.1 = (j, []) → Q.layer b.toNode = p := by
  obtain ⟨⟨hc, hcrit⟩, -, -, -, hroot⟩ := hQ
  refine ⟨hc.2, hc.1, fun j => ?_, hcrit.1, fun j b hb => ?_⟩
  · obtain ⟨b, hb, -⟩ := hroot j
    exact tree_ne_leaf_of_branch b j hb
  · obtain ⟨b', hb', hl⟩ := hroot j
    have : b = b' := Subtype.ext (hb.trans hb'.symm)
    rw [this]
    exact hl

/-- **The sum-level decapitation identity for `coupleSum … true`** (T L2312/L2340).  `hF` is the summability of
the lattice values of every layer on the coset `k + ℤ_L^d`. -/
theorem coupleSum_true_cap (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) (t : ℝ)
    (k : Mom P.d)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |F q (k + latticePoint P.L n)|) :
    coupleSum P F p N kind true t k =
      ∑ᶠ (y : CapSrc p) (_ : CoupleCond P p N kind y.cap),
        (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d,
          outerWeight P.L P.γ P.δ k t n.1 *
            kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
  classical
  unfold coupleSum
  have hset : ∀ Q : LayeredGarden 2,
      (IsCanonC (p + 1) Q ∧ (∀ u ∈ Q.attachNodes p, Q.attachedOrder p u ≤ P.N p) ∧ Q.garden.order = N ∧
        Q.TreeKindOK p (P.N (p + 1)) kind ∧
        (true = true → ∀ j : Fin 2, ∃ b : GBranch Q.garden.tree, b.1 = (j, []) ∧ Q.layer b.toNode = p)) ↔
      CoupleCond P p N kind Q := fun Q => by
    simp only [CoupleCond, forall_const]
  rw [finsum_congr fun Q => (propext (hset Q) ▸ rfl :
    ∑ᶠ (_ : _), kernelKgen P.L P.γ P.δ F Q (fun b => if true = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0 = ∑ᶠ (_ : CoupleCond P p N kind Q), kernelKgen P.L P.γ P.δ F Q
        (fun b => if true = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0)]
  refine (finsum_cap_eq (p := p) {Q | CoupleCond P p N kind Q}
    (fun Q hQ => coupleCond_facts P p N kind Q hQ)
    (fun Q => kernelKgen P.L P.γ P.δ F Q (fun b => if true = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0)).trans ?_
  refine finsum_congr fun y => finsum_congr_Prop rfl fun hy => ?_
  have hplain : y.cap.garden.IsPlain := (coupleCond_facts P p N kind _ hy).2.1
  have hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf y.cap.garden.tree =>
      ℓ.1.1 = j ∧ y.cap.garden.IsLone ℓ).card ≤ 1 := fun j => by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun ℓ _ h => by
      have := hplain ℓ
      have h2 := h.2
      unfold Garden.IsLone at h2
      rw [this] at h2
      exact absurd h2 (by simp))]
    exact Nat.zero_le _
  have hsum := summable_kgTerm P.L P.γ P.δ F y.cap (fun _ => t)
    (pinRoots (T := y.1.garden.tree) t) k (fun _ => 0) 0 hlone (fun ℓ _ => hF _)
  have hfix : (fun b : GBranch (capTree y.1.garden.tree) =>
      if true = true ∧ b.1.2 = [] then some t else none) = pinRoots (T := y.1.garden.tree) t := by
    funext b
    simp [pinRoots]
  have h := kernelKgen_cap P.L P.γ P.δ F y.1 y.2.1 p y.2.2 t k hsum
  rw [← h]
  exact congrArg (fun f => kernelKgen P.L P.γ P.δ F y.cap f ∅ (fun _ => 1) (fun _ => t) k (fun _ => 0) 0) hfix

end WaveTurbulence.FlowerP7
