/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotCpl
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum3
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed

/-! # STAGE1W-O4: the weighted tree slot target (row O4c)

`tree_slot_targetW`: the frontier-weighted native tree kernel `treeLeavesTop p g a` (weight layer `a`: the clock layer,
or the root layer when the root is a garden root) is a superposition on the clock box `timeBoxGt q q'`, with main's
slot mass times `cψ ^ treeExp`.  Nil chains: one root multiplier.  Incoherent chains: the staged INC-TOP tree clause at
the weight layer, extended to the closure of its box by time continuity, then the clock is frozen.  Coherent chains:
COH-TRUNK's `rowTopAgreementTree`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Reg WaveTurbulence.PL2330

/-- The nodes of a regular tree that can carry a frontier factor for the weight layer `a`. -/
def treeNodes (LG : LayeredGarden 1) (a : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun x => x.1.2 ≠ [] ∨ a ≠ LG.layer (GNode.root LG.garden.tree 0)

/-- The frontier exponent of a tree slot. -/
def treeExp (LG : LayeredGarden 1) (a : ℕ) : ℕ := (treeNodes LG a).card

theorem nonroot_le_treeExp (LG : LayeredGarden 1) (a : ℕ) : 3 * LG.garden.order ≤ treeExp LG a := by
  have h := card_nonroot LG.garden.tree
  unfold treeExp treeNodes
  rw [← show (∑ j, (LG.garden.tree j).order) = LG.garden.order from rfl, ← h]
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact Or.inl hx

/-- Every node lies at a layer at most that of its root. -/
theorem node_layer_le_root {w : ℕ} (LG : LayeredGarden w) (x : GNode LG.garden.tree) :
    LG.layer x ≤ LG.layer (GNode.root LG.garden.tree x.1.1) := by
  by_cases hx : x.1.2 = []
  · have e : x = GNode.root LG.garden.tree x.1.1 := Subtype.ext (Prod.ext rfl hx)
    rw [← e]
  · have e := Skeleton.child_parent x hx
    have h1 : LG.layer x ≤ LG.layer (x.parent hx).toNode := by
      conv_lhs => rw [← e]
      exact LG.isLayering.1 _ _
    exact h1.trans (branch_layer_le_root LG (x.parent hx))

/-- A point of `timeBox a q'` with `t₁ ≤ t₀ = a + 1` is in the closure of `timeBoxGt a q'`. -/
theorem mem_closure_timeBoxGt {a q' : ℝ} (hq : q' ≤ a) {t1 : ℝ} (h1 : q' ≤ t1) (h2 : t1 ≤ q' + 1) :
    (![a + 1, t1] : Fin 2 → ℝ) ∈ closure (timeBoxGt a q') := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := min (ε / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  by_cases ht : t1 < a + 1
  · refine ⟨![a + 1, t1], ⟨⟨⟨by simp, by simp⟩, ⟨by simpa using h1, by simpa using h2⟩⟩, by simpa using ht⟩, ?_⟩
    rw [dist_self]; exact hε
  · have ht' : t1 = a + 1 := by linarith
    have hqa : q' = a := by linarith
    refine ⟨![a + 1, t1 - δ], ⟨⟨⟨by simp, by simp⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]; linarith
    · refine lt_of_le_of_lt ((dist_pi_le_iff hδ0.le).mpr fun i => ?_) hδε
      fin_cases i
      · simp [hδ0.le]
      · simp [abs_of_pos hδ0, hδ0.le]

/-- The explicit tree slot constant (depends only on `d` and `η`). -/
noncomputable def KtrW (d : ℕ) (η : ℝ) : ℝ :=
  max (Ktr d η * multD d (30 * d)) (supTreeC d η).toReal

/-- **The weighted tree slot target.** -/
theorem tree_slot_targetW (P : WTParams) (E : GateEnv P) (hinc : TopIncoherentDecayAtR P) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KtrW P.d P.η ∧ ∀ C : ℝ, 2 * P.C₁ ^ 2 * (1 + cLeib P.d (30 * P.d)) ≤ C →
      ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 → ∀ (X : RegChain), X.wf = true → X.size = 2 * n →
      ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden →
      (∀ b, ¬ LG.garden.IsFlowerParent b) →
      (∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      (X = RegChain.nil ∨ (1 ≤ n ∧ (1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) ∨
        (LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 ∧ IsCoherentTreeAt p q q' X LG)))) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      ∀ (g : Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → GPresented (32 * P.d) g cψ →
      ∀ a : ℕ, (a = q ∨ (a = LG.layer (GNode.root LG.garden.tree 0) ∧ q = p)) →
      Sup (30 * P.d) (timeBoxGt (q : ℝ) q')
        (fun ts k => treeLeavesTop P.L P.γ P.δ p g a LG H (ts 0) (ts 1) k)
        (ENNReal.ofReal (K * cψ ^ treeExp LG a * (C * Real.sqrt P.δ) ^ (X.size) *
          P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) *
          leafSizeProduct LG B)) := by
  obtain ⟨Km, hKm1, hKme, hmain⟩ := tree_slot_target P E
  obtain ⟨Ci, hCi, hCie, hci⟩ := sup_tree P E.hd1 E.hη0
  set Cd := multD P.d (30 * P.d) with hCd
  have hCd1 : 1 ≤ Cd := one_le_multD _ _ E.hd1
  refine ⟨max (Km * Cd) Ci.toReal, le_trans (by nlinarith) (le_max_left _ _),
    by rw [hKme, hCie, hCd]; rfl, fun C hC p n hp hn X hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone hcase H B hctrl g cψ hc1 hg a ha => ?_⟩
  set K := max (Km * Cd) Ci.toReal with hK
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one E.hL1
  have hcost : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hLpos : 0 ≤ P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) :=
    Real.rpow_nonneg hL0.le _
  have hx : 0 ≤ (C * Real.sqrt P.δ) ^ (X.size) := by
    have : 0 ≤ C := by nlinarith [E.hC1, cLeib_nonneg P.d (30 * P.d)]
    positivity
  have hgb : ∀ x, ‖g x‖ ≤ cψ := fun x => GPresented.norm_le hg (by linarith) x
  have hmult : IsMult (30 * P.d) g (Cd * cψ) := isMult_of_gPresented E.hd1 hc1 hg
  have hCc : 1 ≤ Cd * cψ := by nlinarith
  have hKm : Km * Cd ≤ K := le_max_left _ _
  rcases hcase with rfl | ⟨hn1, hcase⟩
  · -- nil chain: one root multiplier
    have h0 := hmain C hC p n hp hn RegChain.nil hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone
      (Or.inl rfl) H B hctrl
    have htree : ∀ j : Fin 1, LG.garden.tree j = TTree.leaf := by
      intro j; fin_cases j; exact hdec.1
    have hall := allRoot_of_leaf LG.garden.tree htree
    set f : Mom P.d → ℂ := fun x => topPsi p g (LG.layer (GNode.root LG.garden.tree 0)) a x with hf
    have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), treeLeavesTop P.L P.γ P.δ p g a LG H (ts 0) (ts 1) k =
        f k * treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k := by
      intro ts k
      unfold treeLeavesTop treeLeaves
      refine kernelLeavesW_const _ _ _ LG H _ _ k _ 0 _ _ fun κ => ?_
      rw [← rowTopWeightR_const]
      unfold rowTopWeightR
      rw [prod_allRoot _ hall, Fin.prod_univ_one, rowParentLayer_root, CohTrunk.coset_root]
      rfl
    set K0 : ℝ := if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then Cd * cψ else 1 with hK0
    have hK00 : 0 < K0 := by rw [hK0]; split_ifs <;> linarith
    have h1 := Sup.mulM h0 hK00 (isMult_topPsi hCc hmult p _ a)
    refine (Sup.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
    rw [← ENNReal.ofReal_mul hK00.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs0 : RegChain.nil.size = 0 := rfl
    rw [hs0, incoherency_nil]
    simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    have hK0' : K0 ≤ Cd * cψ ^ treeExp LG a := by
      rw [hK0]
      split_ifs with hc
      · have hm : GNode.root LG.garden.tree 0 ∈ treeNodes LG a := by
          simp only [treeNodes, Finset.mem_filter, Finset.mem_univ, true_and]
          right; omega
        have := pow_le_pow_right₀ hc1 (Finset.card_pos.mpr ⟨_, hm⟩)
        rw [pow_one] at this
        unfold treeExp
        nlinarith
      · nlinarith [one_le_pow₀ (n := treeExp LG a) hc1]
    calc K0 * (Km * leafSizeProduct LG B) = K0 * Km * leafSizeProduct LG B := by ring
      _ ≤ (Cd * cψ ^ treeExp LG a) * Km * leafSizeProduct LG B := by gcongr
      _ = (Km * Cd) * cψ ^ treeExp LG a * leafSizeProduct LG B := by ring
      _ ≤ K * cψ ^ treeExp LG a * leafSizeProduct LG B := by gcongr
  · have hord : LG.garden.order = X.size := VineEstS5C.P4.W2.decodesTree_order' hdec
    have hexp : 6 * n ≤ treeExp LG a := by
      have := nonroot_le_treeExp LG a
      rw [hord, hsz] at this
      omega
    rcases hcase with hi | ⟨hg0, hXc⟩
    · -- incoherent: INC-TOP's tree clause at the weight layer
      have hap : a ≤ p := by rcases ha with rfl | ⟨rfl, -⟩; exacts [hqp, hlay _]
      have hra : LG.layer (GNode.root LG.garden.tree 0) ≤ a := by rcases ha with rfl | ⟨rfl, -⟩; exacts [hr0, le_rfl]
      have hq'a : q' ≤ a := by
        rcases ha with rfl | ⟨rfl, -⟩
        · exact hqq'
        · obtain ⟨y, hy⟩ : ∃ y : GNode LG.garden.tree, y.1.2 = X.lonePath :=
            ⟨⟨(0, X.lonePath), by
              show X.lonePath ∈ (LG.garden.tree 0).nodes
              rw [hdec.1]; exact Links.lonePath_mem_plug X _ _⟩, rfl⟩
          rw [← hlone y hy]
          have := node_layer_le_root LG y
          have h0 : y.1.1 = 0 := Subsingleton.elim _ _
          rw [h0] at this
          exact this
      have hgate := (hinc p hp n hn (fun _ => g) cψ hc1 (fun _ => hg)).2 X hwf hsz LG hdec hlay a q' hq'a hap hra
        hlone hi H B hctrl
      have hX : ENNReal.ofReal (cψ ^ (4 * n + 1)) *
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (regBound_ne_top _ _ _)) ENNReal.ofReal_ne_top
      have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ => treeLeavesTop P.L P.γ P.δ p g a LG H (ts 0) (ts 1) k :=
        fun k => continuous_treeLeavesTop_time P.L P.γ P.δ p g a LG H hnf hlo k _
          (fun k' => by
            rw [← rowTopWeightR_const]
            exact norm_rowTopWeightR_le p (fun _ => g) LG ![a] cψ hc1 (fun _ => hgb) k')
          (hctrl.summable_coset E.hd1 E.hL1 k)
      have hs := hci a q' _ _ hX hq'a hcont hgate
      have hs1 : Sup (30 * P.d) (timeBoxGt (q : ℝ) q')
          (fun ts k => treeLeavesTop P.L P.γ P.δ p g a LG H (ts 0) (ts 1) k)
          (Ci * (ENNReal.ofReal (cψ ^ (4 * n + 1)) *
            regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
            ENNReal.ofReal (leafSizeProduct LG B))) := by
        by_cases haq : a = q
        · rw [← haq]; exact hs
        · obtain ⟨hal, hqp'⟩ : a = LG.layer (GNode.root LG.garden.tree 0) ∧ q = p := ha.resolve_left haq
          have haq' : a + 1 ≤ q := by omega
          have hcl := Sup.closure_of_continuous hs hcont
          have h2 := Sup.update0 hcl ((a : ℝ) + 1) (B' := timeBoxGt (q : ℝ) q') fun t ht => by
            have e : Function.update t 0 ((a : ℝ) + 1) = ![(a : ℝ) + 1, t 1] := by
              funext i; fin_cases i <;> simp
            rw [e]
            exact mem_closure_timeBoxGt (by exact_mod_cast hq'a) ht.1.2.1 ht.1.2.2
          refine Sup.congr' h2 fun t ht k => ?_
          have hq1 : ((a : ℝ) + 1) ≤ t 0 := by
            have : ((a + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast haq'
            push_cast at this
            linarith [ht.1.1.1]
          simp only [Function.update_self, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
            Function.update_of_ne]
          exact (treeLeavesTop_freeze P.L P.γ P.δ p g a LG H k _ (t 0) (t 1) (by rw [← hal]) hq1).symm
      refine hs1.mono ?_
      have hC0 : 0 ≤ P.C₁ := by linarith [E.hC1]
      have hreg0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) *
          (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) := by
        have := E.hδ0
        positivity
      rw [regBound_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        enn_mul_ofReal hCi _ (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hCc' : P.C₁ ≤ C := by nlinarith [E.hC1, cLeib_nonneg P.d (30 * P.d)]
      have hbd := regBound_le_target P C n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) hn1 E.hC1 hCc'
        E.hδ0 E.hL1 E.hκ
      rw [hsz]
      have hCiK : Ci.toReal ≤ K := le_max_right _ _
      have hcp : cψ ^ (4 * n + 1) ≤ cψ ^ treeExp LG a := pow_le_pow_right₀ hc1 (by omega)
      have hxx : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) := by rw [← hsz]; exact hx
      calc Ci.toReal * (cψ ^ (4 * n + 1) * (P.C₁ * (P.C₁ * P.δ) ^ n *
            P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ))) *
            leafSizeProduct LG B)
          ≤ K * (cψ ^ treeExp LG a * ((C * Real.sqrt P.δ) ^ (2 * n) *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ))) * leafSizeProduct LG B) := by
            gcongr
        _ = _ := by ring
    · -- coherent: COH-TRUNK's tree agreement
      have h0 := hmain C hC p n hp hn X hwf hsz LG hdec hnf hlo hlay q q' hqq' hqp hr0 hlone
        (Or.inr ⟨hn1, Or.inr ⟨hg0, hXc⟩⟩) H B hctrl
      have hsub : topSetR p LG ![a] ⊆ topSetR p LG ![q] := by
        refine topSetR_mono p LG _ _ fun j => ?_
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        rcases ha with h | ⟨h, -⟩
        · left; show a = q; exact h
        · right; show ¬ (_ < p ∧ a = p); omega
      set V : Mom P.d → ℂ := fun x => if topSetR p LG ![a] = topSetR p LG ![q] then
        (if q' < p ∧ q = p then g x else 1) else 1 with hV
      have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), treeLeavesTop P.L P.γ P.δ p g a LG H (ts 0) (ts 1) k =
          V k * treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k := by
        intro ts k
        unfold treeLeavesTop treeLeaves
        refine kernelLeavesW_const _ _ _ LG H _ _ k _ 0 _ _ fun κ => ?_
        have hagr := CohTrunk.rowTopAgreementTree p q q' X LG hqq' hqp hXc g P.L k κ
        have hagr2 := CohTrunk.rowTopAgreementTree p q q' X LG hqq' hqp hXc (fun _ => (2 : ℂ)) P.L k κ
        rw [← rowTopWeightR_const] at hagr hagr2 ⊢
        have hcard : (topSetR p LG ![q]).card ≤ 1 := by
          refine card_topSetR_le_one p LG ![q] (cosetDecoration LG.garden P.L k κ.1) ?_
          rw [hagr2]
          split_ifs <;> simp
        rw [rowTopWeightR_of_subset p (fun _ => g) LG ![q] ![a] hsub hcard, hagr]
      have hVm : IsMult (30 * P.d) V (Cd * cψ) := by
        rw [hV]
        by_cases he : topSetR p LG ![a] = topSetR p LG ![q]
        · simp only [if_pos he]
          by_cases h1 : q' < p ∧ q = p
          · simp only [if_pos h1]; exact hmult
          · simp only [if_neg h1]; exact (isMult_one _).mono hCc
        · simp only [if_neg he]; exact (isMult_one _).mono hCc
      have h1 := Sup.mulM h0 (by linarith : (0 : ℝ) < Cd * cψ) hVm
      refine (Sup.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
      rw [← ENNReal.ofReal_mul (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hcp : cψ ≤ cψ ^ treeExp LG a := by
        calc cψ = cψ ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hc1 (by omega)
      calc Cd * cψ * (Km * (C * Real.sqrt P.δ) ^ X.size *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B)
          = (Km * Cd) * cψ * ((C * Real.sqrt P.δ) ^ X.size *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B) := by
            ring
        _ ≤ K * cψ ^ treeExp LG a * ((C * Real.sqrt P.δ) ^ X.size *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency (X.treeLinks (LG.garden.sig 0)) : ℝ)) * leafSizeProduct LG B) := by
            gcongr
        _ = _ := by ring

end WaveTurbulence.Flower.Stage1WNoVine
