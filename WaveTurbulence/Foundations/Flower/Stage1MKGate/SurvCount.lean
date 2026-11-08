/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
public import WaveTurbulence.Foundations.Vine.A.VineSkipSelected
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.Flower.MkMark.SigmaGroup

/-! # B4 STAGE1MK-GATE: the survivor count (finding F-B4-6)

`survivorsMk_length_le`: the marked splice has at most `2 · #Mk` survivors (o75 `N_E ≤ 2 b_V`).

Per marked group `S` (any `MarkedGroupUnits G S Mk`), every survivor is a marked `𝒱`-ingredient or an ingredient
that is no vine of `𝒱` (`surv_spec`); distinct survivors have distinct atom sets (`surv_meet`, a vine has two
distinct joints). At most one survivor is not a vine of `𝒱`: two such are spine members (`surv_spine`) that are both
(CN), hence equal (`Spine.cn_unique`), or both (CL) outside `𝒱`, hence both top ingredients of `S` (there is then no
(CN) ingredient, `cl_mem_vinesV_of_CN`), hence equal (`top_unique`); a (CN) and a (CL) one cannot coexist. So a marked
group has at most `#(marked 𝒱-ingredients) + 1 ≤ 2·#(marked 𝒱-ingredients)` survivors, and the marked
`𝒱`-ingredients of distinct maximal groups are distinct (`maximalGroups_disjoint`, `ing_subset`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset

namespace WaveTurbulence.Flower.Stage1MKGate

variable {w : ℕ}

/-- A vine has at least two atoms. -/
theorem two_le_card_of_isSomeVine {G : Garden w} {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (h : LGSpine.SourceVine.IsSomeVine G.molecule T p q) : 2 ≤ T.card := by
  obtain ⟨X, hX⟩ := h
  have hB := hX.1
  exact Finset.one_lt_card.2 ⟨p, hB.2.1, q, hB.2.2.1, hB.2.2.2.1⟩

/-- The atoms of a (CL) vine are nonempty (they contain the upper joint). -/
theorem CLVine.upper_mem {G : Garden w} (c : CLVine G) : c.upper ∈ c.atoms := by
  obtain ⟨X, hX⟩ := c.isVine
  exact hX.1.2.1

/-- The marked `𝒱`-ingredients of a group. -/
def mkIngr (G : Garden w) (Mk : Set (CLVine G)) (S : Finset (GBranch G.tree)) : Finset (CLVine G) :=
  (Set.toFinite Mk).toFinset.filter fun c => c ∈ vinesV G ∧ IsIngredient G.molecule S c.atoms

section Group
variable {G : Garden w} {S : Finset (GBranch G.tree)} {Mk : Set (CLVine G)}

/-- Survivors of a marked group are pairwise distinct in their atom sets (as list entries). -/
theorem surv_pairwise_fst (U : MarkedGroupUnits G S Mk) : U.surv.Pairwise (fun t t' => t.1 ≠ t'.1) := by
  refine List.Pairwise.imp_of_mem ?_ U.surv_meet
  intro a b ha _ hab he
  have h2 := two_le_card_of_isSomeVine (U.surv_spec a ha).1
  rw [he, Finset.inter_self] at hab
  rw [he] at h2
  omega

theorem surv_fst_nodup (U : MarkedGroupUnits G S Mk) : (U.surv.map Prod.fst).Nodup :=
  List.pairwise_map.2 (surv_pairwise_fst U)

theorem surv_nodup (U : MarkedGroupUnits G S Mk) : U.surv.Nodup :=
  (surv_pairwise_fst U).imp fun h he => h (congrArg Prod.fst he)

/-- Distinct survivors of a marked group have distinct atom sets. -/
theorem surv_fst_ne (U : MarkedGroupUnits G S Mk) {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ U.surv) (ht' : t' ∈ U.surv) (hne : t ≠ t') : t.1 ≠ t'.1 :=
  fun he => hne (List.inj_on_of_nodup_map (surv_fst_nodup U) ht ht' he)

/-- A (CL) vine that is an ingredient of a maximal group `S` but not a vine of `𝒱`: `S` has no (CN) ingredient
and the vine is the top ingredient of `S`. -/
theorem top_of_not_vinesV (hS : S ∈ maximalGroups G.molecule) {c : CLVine G}
    (hi : IsIngredient G.molecule S c.atoms) (hc : c ∉ vinesV G) :
    ¬ (∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T) ∧ IsTopIngredient S c := by
  have hvl : ∃ a b, LGSpine.SourceVine.IsVC G.molecule S a b ∨ LGSpine.SourceVine.IsHVC G.molecule S a b := by
    rcases MkMark.isIngredient_vc_or_hvc hi with ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact ⟨a, b, Or.inl h⟩
    · exact ⟨a, b, Or.inr h⟩
  have hnocn : ¬ (∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T) := fun hcn =>
    hc (VineA.cl_mem_vinesV_of_CN hS hvl hcn c hi)
  refine ⟨hnocn, ?_⟩
  by_contra htop
  apply hc
  obtain ⟨a, b, hvc | hhvc⟩ := hvl
  · by_cases hr : IsRootVC G S
    · exact ⟨S, hS, hi, Or.inr ⟨Or.inr hr, Or.inr htop⟩⟩
    · exact ⟨S, hS, hi, Or.inl ⟨a, b, hvc, hr⟩⟩
  · exact ⟨S, hS, hi, Or.inr ⟨Or.inl ⟨a, b, hhvc⟩, Or.inr htop⟩⟩

/-- **At most one survivor of a marked group is not a vine of `𝒱`**: two such have the same atoms. -/
theorem surv_nonV_fst_eq (hS : S ∈ maximalGroups G.molecule) (U : MarkedGroupUnits G S Mk)
    {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ U.surv) (ht' : t' ∈ U.surv)
    (hn : ∀ c ∈ vinesV G, c.atoms ≠ t.1) (hn' : ∀ c ∈ vinesV G, c.atoms ≠ t'.1) : t.1 = t'.1 := by
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hv, hi, -, hsub, -⟩ := U.surv_spine
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q h => (hv (T, p, q) h).choose_spec.1
  have htL := hsub.subset ht
  have htL' := hsub.subset ht'
  have hvt := hv t htL
  have hvt' := hv t' htL'
  have hit := hi t htL
  have hit' := hi t' htL'
  -- a non-(CN) non-𝒱 survivor gives a (CL) vine outside `𝒱`
  have clcase : ∀ u ∈ L, (∀ c ∈ vinesV G, c.atoms ≠ u.1) → ¬ CNMem G u →
      ∃ c : CLVine G, c.atoms = u.1 ∧ c ∉ vinesV G := by
    intro u hu hnu hcn
    obtain ⟨c, hc, -⟩ := exists_clVine (hv u hu) hcn
    exact ⟨c, hc, fun hcV => hnu c hcV hc⟩
  have cnV : ∀ u ∈ L, CNMem G u → ∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T :=
    fun u hu hcn => ⟨u.1, hi u hu, u.2.1, u.2.2, hv u hu, hcn.1, hcn.2⟩
  by_cases hc1 : CNMem G t <;> by_cases hc2 : CNMem G t'
  · exact congrArg Prod.fst (hs.cn_unique hblk htL htL' hc1 hc2)
  · obtain ⟨c', hc', hc'V⟩ := clcase t' htL' hn' hc2
    exact ((top_of_not_vinesV hS (hc' ▸ hit') hc'V).1 (cnV t htL hc1)).elim
  · obtain ⟨c, hc, hcV⟩ := clcase t htL hn hc1
    exact ((top_of_not_vinesV hS (hc ▸ hit) hcV).1 (cnV t' htL' hc2)).elim
  · obtain ⟨c, hc, hcV⟩ := clcase t htL hn hc1
    obtain ⟨c', hc', hc'V⟩ := clcase t' htL' hn' hc2
    have h1 := (top_of_not_vinesV hS (hc ▸ hit) hcV).2
    have h2 := (top_of_not_vinesV hS (hc' ▸ hit') hc'V).2
    by_contra hne
    exact top_unique h1 h2 (hc ▸ hit) (hc' ▸ hit') (by rw [hc, hc']; exact hne)

/-- **The survivors of one marked group**: at most `2·#(marked 𝒱-ingredients)`. -/
theorem surv_length_le (hS : S ∈ maximalGroups G.molecule) (U : MarkedGroupUnits G S Mk)
    (hmk : markedGroup G Mk S) : U.surv.length ≤ 2 * (mkIngr G Mk S).card := by
  obtain ⟨c₀, hc₀, hc₀V, hc₀I⟩ := hmk
  have hc₀m : c₀ ∈ mkIngr G Mk S := by
    simp only [mkIngr, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hc₀, hc₀V, hc₀I⟩
  let P1 : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → Prop :=
    fun t => ∃ c ∈ Mk, c ∈ vinesV G ∧ c.atoms = t.1
  have hsplit := List.length_eq_countP_add_countP (fun t => decide (P1 t)) (l := U.surv)
  -- marked survivors inject into the marked ingredients
  have h1 : U.surv.countP (fun t => decide (P1 t)) ≤ (mkIngr G Mk S).card := by
    rw [List.countP_eq_length_filter]
    have hnd := (surv_nodup U).filter (fun t => decide (P1 t))
    rw [← List.toFinset_card_of_nodup hnd]
    let f : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → CLVine G :=
      fun t => if h : P1 t then h.choose else c₀
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro t ht
      have ht' := List.mem_toFinset.1 ht
      obtain ⟨htm, hp⟩ := List.mem_filter.1 ht'
      have hp' : P1 t := of_decide_eq_true hp
      simp only [f, hp', ↓reduceDIte]
      obtain ⟨hcMk, hcV, hca⟩ := hp'.choose_spec
      simp only [mkIngr, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact ⟨hcMk, hcV, by rw [hca]; exact (U.surv_spec t htm).2.1⟩
    · intro t ht t' ht' he
      have hm := List.mem_filter.1 (List.mem_toFinset.1 ht)
      have hm' := List.mem_filter.1 (List.mem_toFinset.1 ht')
      have hp : P1 t := of_decide_eq_true hm.2
      have hp' : P1 t' := of_decide_eq_true hm'.2
      simp only [f, hp, hp', ↓reduceDIte] at he
      have e1 := hp.choose_spec.2.2
      have e2 := hp'.choose_spec.2.2
      by_contra hne
      exact surv_fst_ne U hm.1 hm'.1 hne (by rw [← e1, ← e2, he])
  -- at most one survivor is not a vine of `𝒱`
  have h2 : U.surv.countP (fun t => decide ¬ (decide (P1 t)) = true) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    have hpw : (U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true)).Pairwise (fun t t' => t.1 ≠ t'.1) := by
      refine List.Pairwise.imp_of_mem ?_ ((surv_nodup U).sublist List.filter_sublist)
      intro a b ha hb hab
      exact surv_fst_ne U (List.mem_filter.1 ha).1 (List.mem_filter.1 hb).1 hab
    have hnV : ∀ t ∈ U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true), ∀ c ∈ vinesV G, c.atoms ≠ t.1 := by
      intro t ht
      obtain ⟨htm, hnp⟩ := List.mem_filter.1 ht
      have hnp' : ¬ P1 t := by simpa using hnp
      rcases (U.surv_spec t htm).2.2 with hm | hm
      · exact (hnp' hm).elim
      · exact hm
    match hl : U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true), hpw, hnV with
    | [], _, _ => simp
    | [_], _, _ => simp
    | a :: b :: l, hp, hn =>
      have hab := (List.pairwise_cons.1 hp).1 b (by simp)
      have ha : a ∈ U.surv := (List.mem_filter.1 (hl ▸ (by simp : a ∈ a :: b :: l))).1
      have hb : b ∈ U.surv := (List.mem_filter.1 (hl ▸ (by simp : b ∈ a :: b :: l))).1
      exact (hab (surv_nonV_fst_eq hS U ha hb (hn a (by simp)) (hn b (by simp)))).elim
  have hpos : 1 ≤ (mkIngr G Mk S).card := Finset.card_pos.2 ⟨c₀, hc₀m⟩
  omega

end Group

/-- The marked `𝒱`-ingredients of distinct maximal groups are disjoint. -/
theorem mkIngr_disjoint {G : Garden w} (Mk : Set (CLVine G)) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hS' : S' ∈ maximalGroups G.molecule) (hne : S ≠ S') :
    Disjoint (mkIngr G Mk S) (mkIngr G Mk S') := by
  rw [Finset.disjoint_left]
  intro c h h'
  simp only [mkIngr, Finset.mem_filter] at h h'
  have hd := maximalGroups_disjoint (Mole.garden_isMolecule G) hS hS' hne
  exact Finset.disjoint_left.1 hd (ing_subset h.2.2 c.upper_mem) (ing_subset h'.2.2 c.upper_mem)

/-- **The survivor count (F-B4-6)**: the marked splice has at most `2·#Mk` survivors. -/
theorem survivorsMk_length_le (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) :
    (survivorsMk G σ Mk).length ≤ 2 * Mk.ncard := by
  unfold survivorsMk
  rw [List.length_flatMap]
  have hgr : ∀ S ∈ sgGroups G σ, (if markedGroup G Mk S then (if h : Nonempty (MarkedGroupUnits G S Mk) then
      (Classical.choice h).surv else []) else []).length ≤ 2 * (mkIngr G Mk S).card := by
    intro S hS
    have hSm := (mem_sgGroups.1 hS).1
    split_ifs with hmk hne
    · exact surv_length_le hSm _ hmk
    · simp
    · simp
  refine (List.sum_le_sum hgr).trans ?_
  have hnd : (sgGroups G σ).Nodup := by
    unfold sgGroups
    exact (Finset.nodup_toList _).filter _
  rw [List.sum_map_mul_left, ← List.sum_toFinset _ hnd]
  have hdisj : ((sgGroups G σ).toFinset : Set (Finset (GBranch G.tree))).PairwiseDisjoint (mkIngr G Mk) := by
    intro S hS S' hS' hne
    exact mkIngr_disjoint Mk (mem_sgGroups.1 (List.mem_toFinset.1 hS)).1
      (mem_sgGroups.1 (List.mem_toFinset.1 hS')).1 hne
  rw [← Finset.card_biUnion hdisj]
  have hsub : (sgGroups G σ).toFinset.biUnion (mkIngr G Mk) ⊆ (Set.toFinite Mk).toFinset := by
    intro c hc
    obtain ⟨S, -, hc⟩ := Finset.mem_biUnion.1 hc
    exact (Finset.mem_filter.1 hc).1
  have := Finset.card_le_card hsub
  rw [← Set.ncard_eq_toFinset_card Mk (Set.toFinite Mk)] at this
  omega

end WaveTurbulence.Flower.Stage1MKGate
