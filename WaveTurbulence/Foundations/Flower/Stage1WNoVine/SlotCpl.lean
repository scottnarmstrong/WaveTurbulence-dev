/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotKer
public import WaveTurbulence.Foundations.Flower.Stage1W.TypeBound
public import WaveTurbulence.Foundations.Flower.CohTrunk.Main
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum2

/-! # STAGE1W-O4: the weighted couple slot target (row O4c)

`couple_slot_targetW`: the frontier-weighted native couple kernel `coupleLeavesTopR p g a b` (per-arm weights,
weight layers `a, b`: the clock layers, or the root layer at an arm whose root is a garden root) is a centred
superposition on the clock box `timeBox q q'`, with main's slot mass times `cψ ^ cplExp` (`cplExp` counts the nodes
that can carry a frontier factor).
- trivial couples: the weight is a product of two root multipliers (SNorm multiplier lemma);
- incoherent couples: the staged `TopIncoherentDecayAtR` (INC-TOP) at the weight layers, then the clocks of the
  garden-root arms are frozen (`coupleLeavesTopR_freeze0/1`);
- coherent couples: COH-TRUNK's `rowTopAgreementCoupleR` makes the weight a single multiplier. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Reg WaveTurbulence.PL2330

/-- The nodes of a regular couple that can carry a frontier factor for the weight layers `a, b`. -/
def cplNodes (LG : LayeredGarden 2) (a b : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun x => x.1.2 ≠ [] ∨ ![a, b] x.1.1 ≠ LG.layer (GNode.root LG.garden.tree x.1.1)

/-- The frontier exponent of a couple slot. -/
def cplExp (LG : LayeredGarden 2) (a b : ℕ) : ℕ := (cplNodes LG a b).card

theorem nonroot_le_cplExp (LG : LayeredGarden 2) (a b : ℕ) :
    3 * LG.garden.order ≤ cplExp LG a b := by
  have h := card_nonroot LG.garden.tree
  unfold cplExp cplNodes
  rw [← show (∑ j, (LG.garden.tree j).order) = LG.garden.order from rfl, ← h]
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact Or.inl hx

/-- Two root factors cost at most `cψ ^ cplExp`. -/
theorem root_factors_le (LG : LayeredGarden 2) (a b p : ℕ) (cψ : ℝ) (hc : 1 ≤ cψ) :
    (if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then cψ else 1) *
      (if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then cψ else 1) ≤ cψ ^ cplExp LG a b := by
  have m0 : LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p → GNode.root LG.garden.tree 0 ∈ cplNodes LG a b := by
    intro h
    simp only [cplNodes, Finset.mem_filter, Finset.mem_univ, true_and]
    right
    show a ≠ LG.layer (GNode.root LG.garden.tree 0)
    omega
  have m1 : LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p → GNode.root LG.garden.tree 1 ∈ cplNodes LG a b := by
    intro h
    simp only [cplNodes, Finset.mem_filter, Finset.mem_univ, true_and]
    right
    show b ≠ LG.layer (GNode.root LG.garden.tree 1)
    omega
  have hne : GNode.root LG.garden.tree 0 ≠ GNode.root LG.garden.tree 1 :=
    fun h => absurd (gnode_root_injective _ h) (by decide)
  unfold cplExp
  split_ifs with h0 h1 h1
  · have hs : ({GNode.root LG.garden.tree 0, GNode.root LG.garden.tree 1} : Finset _) ⊆ cplNodes LG a b := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact m0 h0
      · rw [Finset.mem_singleton.mp hx]; exact m1 h1
    have hc2 := Finset.card_le_card hs
    rw [Finset.card_pair hne] at hc2
    calc cψ * cψ = cψ ^ 2 := by ring
      _ ≤ _ := pow_le_pow_right₀ hc hc2
  · have hc1 := Finset.card_pos.mpr ⟨_, m0 h0⟩
    calc cψ * 1 = cψ ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hc hc1
  · have hc1 := Finset.card_pos.mpr ⟨_, m1 h1⟩
    calc 1 * cψ = cψ ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hc hc1
  · rw [one_mul]; exact one_le_pow₀ hc

/-- The explicit couple slot constant (depends only on `d` and `η`). -/
noncomputable def KcplW (d : ℕ) (η : ℝ) : ℝ :=
  max (Kcpl d η * multD d (30 * d) ^ 2) (cenCplC d η).toReal

/-- **The weighted couple slot target.** -/
theorem couple_slot_targetW (P : WTParams) (E : GateEnv P) (hinc : TopIncoherentDecayAtR P) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KcplW P.d P.η ∧ ∀ C : ℝ, 2 * P.C₁ ^ 2 * (1 + cLeib P.d (30 * P.d)) ≤ C →
      ∀ (p n : ℕ), p < P.D → n ≤ P.N (p + 1) ^ 4 → ∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n →
      ∀ (LG : LayeredGarden 2), Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) →
      ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      (Q = RegCpl.triv ∨ (1 ≤ n ∧ (1 ≤ LG.incoherency Q.links ∨
        (LG.incoherency Q.links = 0 ∧ IsCoherentCoupleAt p q q' Q LG)))) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      ∀ (g : Fin 2 → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
      ∀ a b : ℕ, (a = q ∨ (a = LG.layer (GNode.root LG.garden.tree 0) ∧ q = p)) →
        (b = q' ∨ (b = LG.layer (GNode.root LG.garden.tree 1) ∧ q' = p)) →
      CenSup (30 * P.d) (timeBox (q : ℝ) q')
        (fun ts k => coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k)
        (ENNReal.ofReal (K * cψ ^ cplExp LG a b * (C * Real.sqrt P.δ) ^ (Q.size) *
          P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) * leafSizeProduct LG B)) := by
  obtain ⟨Km, hKm1, hKme, hmain⟩ := couple_slot_target P E
  obtain ⟨Ci, hCi, hCie, hci⟩ := cenSup_couple P E.hd1 E.hη0
  set Cd := multD P.d (30 * P.d) with hCd
  have hCd1 : 1 ≤ Cd := one_le_multD _ _ E.hd1
  refine ⟨max (Km * Cd ^ 2) Ci.toReal, le_trans (by nlinarith) (le_max_left _ _),
    by rw [hKme, hCie, hCd]; rfl, fun C hC p n hp hn Q hwf hsz LG hdec hlay q q' hq hq' hr0 hr1 hcase H B hctrl g cψ hc1 hg a b ha hb => ?_⟩
  set K := max (Km * Cd ^ 2) Ci.toReal with hK
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one E.hL1
  have hcost : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hLpos : 0 ≤ P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) := Real.rpow_nonneg hL0.le _
  have hx : 0 ≤ (C * Real.sqrt P.δ) ^ (Q.size) := by
    have : 0 ≤ C := by nlinarith [E.hC1, cLeib_nonneg P.d (30 * P.d)]
    positivity
  have hgb : ∀ j x, ‖g j x‖ ≤ cψ := fun j x => GPresented.norm_le (hg j) (by linarith) x
  have hmult : ∀ j, IsMult (30 * P.d) (g j) (Cd * cψ) := fun j => isMult_of_gPresented E.hd1 hc1 (hg j)
  have hCc : 1 ≤ Cd * cψ := by nlinarith
  have hX0 : 0 ≤ (C * Real.sqrt P.δ) ^ (Q.size) * P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) *
      leafSizeProduct LG B := by positivity
  have hpow : ∀ e : ℕ, 1 ≤ cψ ^ e := fun e => one_le_pow₀ hc1
  rcases hcase with rfl | ⟨hn1, hcase⟩
  · -- trivial couple: two root multipliers
    have h0 := hmain C hC p n hp hn RegCpl.triv hwf hsz LG hdec hlay q q' hq hq' hr0 hr1 (Or.inl rfl) H B hctrl
    have htree : ∀ j : Fin 2, LG.garden.tree j = TTree.leaf := by
      intro j; fin_cases j
      exacts [hdec.2.1, hdec.2.2.1]
    have hall := allRoot_of_leaf LG.garden.tree htree
    set f0 : Mom P.d → ℂ := fun x => topPsi p (g 0) (LG.layer (GNode.root LG.garden.tree 0)) a x with hf0
    set f1 : Mom P.d → ℂ := fun x => topPsi p (g 1) (LG.layer (GNode.root LG.garden.tree 1)) b x with hf1
    have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k =
        f0 k * (f1 k * coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k) := by
      intro ts k
      rw [← mul_assoc]
      unfold coupleLeavesTopR coupleLeaves
      refine kernelLeavesW_const _ _ _ LG H _ 0 k _ 0 _ _ fun κ => ?_
      unfold rowTopWeightR
      rw [prod_allRoot _ hall, Fin.prod_univ_two, rowParentLayer_root, rowParentLayer_root,
        CohTrunk.coset_root, CohTrunk.coset_root]
      rfl
    set K0 : ℝ := if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then Cd * cψ else 1 with hK0
    set K1 : ℝ := if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then Cd * cψ else 1 with hK1
    have hK01 : 0 < K0 := by rw [hK0]; split_ifs <;> linarith
    have hK11 : 0 < K1 := by rw [hK1]; split_ifs <;> linarith
    have h1 := CenSup.mulM (CenSup.mulM h0 hK11 (isMult_topPsi hCc (hmult 1) p _ b)) hK01
      (isMult_topPsi hCc (hmult 0) p _ a)
    refine (CenSup.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
    rw [← ENNReal.ofReal_mul hK11.le, ← ENNReal.ofReal_mul hK01.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs0 : RegCpl.triv.size = 0 := rfl
    rw [hs0, incoherency_triv]
    simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    have hKK : K0 * K1 ≤ Cd ^ 2 * cψ ^ cplExp LG a b := by
      have hr := root_factors_le LG a b p cψ hc1
      have e0 : K0 ≤ Cd * (if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then cψ else 1) := by
        rw [hK0]; split_ifs <;> nlinarith
      have e1 : K1 ≤ Cd * (if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then cψ else 1) := by
        rw [hK1]; split_ifs <;> nlinarith
      have hpos0 : 0 ≤ (if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then cψ else 1) := by
        split_ifs <;> linarith
      have hpos1 : 0 ≤ (if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then cψ else 1) := by
        split_ifs <;> linarith
      calc K0 * K1 ≤ (Cd * (if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then cψ else 1)) *
            (Cd * (if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then cψ else 1)) :=
            mul_le_mul e0 e1 hK11.le (by positivity)
        _ = Cd ^ 2 * ((if LG.layer (GNode.root LG.garden.tree 0) < p ∧ a = p then cψ else 1) *
            (if LG.layer (GNode.root LG.garden.tree 1) < p ∧ b = p then cψ else 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
    have hKm : Km * Cd ^ 2 ≤ K := le_max_left _ _
    calc K0 * (K1 * (Km * leafSizeProduct LG B)) = (K0 * K1) * Km * leafSizeProduct LG B := by ring
      _ ≤ (Cd ^ 2 * cψ ^ cplExp LG a b) * Km * leafSizeProduct LG B := by gcongr
      _ = (Km * Cd ^ 2) * cψ ^ cplExp LG a b * leafSizeProduct LG B := by ring
      _ ≤ K * cψ ^ cplExp LG a b * leafSizeProduct LG B := by gcongr
  · have hord : LG.garden.order = Q.size := size_eq_order hdec
    have hexp : 6 * n ≤ cplExp LG a b := by
      have := nonroot_le_cplExp LG a b
      rw [hord, hsz] at this
      omega
    rcases hcase with hi | ⟨hg0, hQc⟩
    · -- incoherent: the staged INC-TOP gate at the weight layers, then freeze the garden-root clocks
      have hap : a ≤ p := by rcases ha with rfl | ⟨rfl, -⟩; exacts [hq, hlay _]
      have hbp : b ≤ p := by rcases hb with rfl | ⟨rfl, -⟩; exacts [hq', hlay _]
      have hra : LG.layer (GNode.root LG.garden.tree 0) ≤ a := by rcases ha with rfl | ⟨rfl, -⟩; exacts [hr0, le_rfl]
      have hrb : LG.layer (GNode.root LG.garden.tree 1) ≤ b := by rcases hb with rfl | ⟨rfl, -⟩; exacts [hr1, le_rfl]
      have hgate := (hinc p hp n hn g cψ hc1 hg).1 Q hwf hsz LG hdec hlay a b hap hbp hra hrb hi H B hctrl
      have hX : ENNReal.ofReal (cψ ^ (4 * n + 2)) * regBound P n (LG.incoherency Q.links) *
          ENNReal.ofReal (leafSizeProduct LG B) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (regBound_ne_top _ _ _)) ENNReal.ofReal_ne_top
      have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ => coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k :=
        fun k => continuous_coupleLeavesTopR_time P.L P.γ P.δ p g a b LG H hdec.1.1 k _
          (norm_rowTopWeightR_le p g LG ![a, b] cψ hc1 hgb) (hctrl.summable_coset E.hd1 E.hL1 k)
      have hcs := hci a b _ _ hX hcont hgate
      -- freeze the clock of arm 0
      have hs0 : CenSup (30 * P.d) (timeBox (q : ℝ) b)
          (fun ts k => coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k)
          (Ci * (ENNReal.ofReal (cψ ^ (4 * n + 2)) * regBound P n (LG.incoherency Q.links) *
            ENNReal.ofReal (leafSizeProduct LG B))) := by
        by_cases haq : a = q
        · rw [← haq]; exact hcs
        · obtain ⟨hal, hqp⟩ : a = LG.layer (GNode.root LG.garden.tree 0) ∧ q = p := ha.resolve_left haq
          have haq' : a + 1 ≤ q := by omega
          have h2 := CenSup.update0 hcs ((a : ℝ) + 1) (B' := timeBox (q : ℝ) b) fun t ht => by
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · simp
            · simp
            · simpa using ht.2
          refine CenSup.congr' h2 fun t ht k => ?_
          have hq1 : ((a : ℝ) + 1) ≤ t 0 := by
            have : ((a + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast haq'
            push_cast at this
            linarith [ht.1.1]
          simp only [Function.update_self, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
            Function.update_of_ne]
          exact (coupleLeavesTopR_freeze0 P.L P.γ P.δ p g a b LG H k _ (t 0) (t 1)
            (by rw [← hal]) hq1).symm
      -- freeze the clock of arm 1
      have hs1 : CenSup (30 * P.d) (timeBox (q : ℝ) q')
          (fun ts k => coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k)
          (Ci * (ENNReal.ofReal (cψ ^ (4 * n + 2)) * regBound P n (LG.incoherency Q.links) *
            ENNReal.ofReal (leafSizeProduct LG B))) := by
        by_cases hbq : b = q'
        · rw [← hbq]; exact hs0
        · obtain ⟨hbl, hqp⟩ : b = LG.layer (GNode.root LG.garden.tree 1) ∧ q' = p := hb.resolve_left hbq
          have hbq' : b + 1 ≤ q' := by omega
          have h2 := CenSup.update1 hs0 ((b : ℝ) + 1) (B' := timeBox (q : ℝ) q') fun t ht => by
            refine ⟨?_, ⟨?_, ?_⟩⟩
            · simpa using ht.1
            · simp
            · simp
          refine CenSup.congr' h2 fun t ht k => ?_
          have hq1 : ((b : ℝ) + 1) ≤ t 1 := by
            have : ((b + 1 : ℕ) : ℝ) ≤ q' := by exact_mod_cast hbq'
            push_cast at this
            linarith [ht.2.1]
          simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne]
          exact (coupleLeavesTopR_freeze1 P.L P.γ P.δ p g a b LG H k _ (t 0) (t 1)
            (by rw [← hbl]) hq1).symm
      refine hs1.mono ?_
      have hC0 : 0 ≤ P.C₁ := by linarith [E.hC1]
      have hreg0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n *
          P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (LG.incoherency Q.links : ℝ)) := by
        have := E.hδ0
        positivity
      rw [regBound_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        enn_mul_ofReal hCi _ (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hCc' : P.C₁ ≤ C := by nlinarith [E.hC1, cLeib_nonneg P.d (30 * P.d)]
      have hbd := regBound_le_target P C n (LG.incoherency Q.links) hn1 E.hC1 hCc' E.hδ0 E.hL1 E.hκ
      rw [hsz]
      have hCiK : Ci.toReal ≤ K := le_max_right _ _
      have hcp : cψ ^ (4 * n + 2) ≤ cψ ^ cplExp LG a b := pow_le_pow_right₀ hc1 (by omega)
      have hxx : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) := by rw [← hsz]; exact hx
      calc Ci.toReal * (cψ ^ (4 * n + 2) * (P.C₁ * (P.C₁ * P.δ) ^ n *
            P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (LG.incoherency Q.links : ℝ))) * leafSizeProduct LG B)
          ≤ K * (cψ ^ cplExp LG a b * ((C * Real.sqrt P.δ) ^ (2 * n) *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ))) * leafSizeProduct LG B) := by
            gcongr
        _ = _ := by ring
    · -- coherent: COH-TRUNK's agreement makes the weight one multiplier
      have h0 := hmain C hC p n hp hn Q hwf hsz LG hdec hlay q q' hq hq' hr0 hr1
        (Or.inr ⟨hn1, Or.inr ⟨hg0, hQc⟩⟩) H B hctrl
      have hsub : topSetR p LG ![a, b] ⊆ topSetR p LG ![q, q'] := by
        refine topSetR_mono p LG _ _ (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rcases ha with h | ⟨h, -⟩
          · left; show a = q; exact h
          · right; show ¬ (_ < p ∧ a = p); omega
        · rcases hb with h | ⟨h, -⟩
          · left; show b = q'; exact h
          · right; show ¬ (_ < p ∧ b = p); omega
      set V : Mom P.d → ℂ := fun x => if topSetR p LG ![a, b] = topSetR p LG ![q, q'] then
        (if q' < p ∧ q = p then g 0 x else if q < p ∧ q' = p then g 1 x else 1) else 1 with hV
      have hw : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), coupleLeavesTopR P.L P.γ P.δ p g a b LG H (ts 0) (ts 1) k =
          V k * coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k := by
        intro ts k
        unfold coupleLeavesTopR coupleLeaves
        refine kernelLeavesW_const _ _ _ LG H _ 0 k _ 0 _ _ fun κ => ?_
        have hagr := CohTrunk.rowTopAgreementCoupleR p q q' Q LG hq hq' hQc g P.L k κ
        have hagr2 := CohTrunk.rowTopAgreementCoupleR p q q' Q LG hq hq' hQc (fun _ _ => (2 : ℂ)) P.L k κ
        have hcard : (topSetR p LG ![q, q']).card ≤ 1 := by
          refine card_topSetR_le_one p LG ![q, q'] (cosetDecoration LG.garden P.L k κ.1) ?_
          rw [hagr2]
          split_ifs <;> simp
        rw [rowTopWeightR_of_subset p g LG ![q, q'] ![a, b] hsub hcard, hagr]
      have hVm : IsMult (30 * P.d) V (Cd * cψ) := by
        rw [hV]
        by_cases he : topSetR p LG ![a, b] = topSetR p LG ![q, q']
        · simp only [if_pos he]
          by_cases h1 : q' < p ∧ q = p
          · simp only [if_pos h1]; exact hmult 0
          · by_cases h2 : q < p ∧ q' = p
            · simp only [if_neg h1, if_pos h2]; exact hmult 1
            · simp only [if_neg h1, if_neg h2]; exact (isMult_one _).mono hCc
        · simp only [if_neg he]; exact (isMult_one _).mono hCc
      have h1 := CenSup.mulM h0 (by linarith : (0 : ℝ) < Cd * cψ) hVm
      refine (CenSup.congr' h1 fun ts _ k => (hw ts k).symm).mono ?_
      rw [← ENNReal.ofReal_mul (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hcp : cψ ≤ cψ ^ cplExp LG a b := by
        calc cψ = cψ ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hc1 (by omega)
      have hKmCd : 0 ≤ Km * Cd := mul_nonneg (by linarith) (by linarith)
      have hKm2 : Km * Cd * 1 ≤ Km * Cd * Cd := mul_le_mul_of_nonneg_left hCd1 hKmCd
      have hKm : Km * Cd ≤ K := le_trans (by nlinarith) (le_max_left _ _)
      calc Cd * cψ * (Km * (C * Real.sqrt P.δ) ^ Q.size * P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) *
            leafSizeProduct LG B)
          = (Km * Cd) * cψ * ((C * Real.sqrt P.δ) ^ Q.size * P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) *
            leafSizeProduct LG B) := by ring
        _ ≤ K * cψ ^ cplExp LG a b * ((C * Real.sqrt P.δ) ^ Q.size *
            P.L ^ (-(P.η ^ 8) * (LG.incoherency Q.links : ℝ)) * leafSizeProduct LG B) := by gcongr
        _ = _ := by ring

end WaveTurbulence.Flower.Stage1WNoVine
