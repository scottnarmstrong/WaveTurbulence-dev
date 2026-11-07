/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.CodeLayeringCount
public import WaveTurbulence.Foundations.RegStruct.CodeCount
public import WaveTurbulence.Foundations.RegStruct.SourceCoupleCount
public import WaveTurbulence.Foundations.Spine.CoherentObjects
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc1

/-! # P4 count bridge (1): coherent embedded regular couples with parent layers `(q, q')` (TARGET Prop `layerreg2`, L932)

`layerreg2` (C4, `LayerRegDraft.LayerReg2`) counts the layerings induced on a code placed at FIXED addresses of an ambient garden.
A coherent couple `IsCoherentCoupleAt p q q' Q LQ` (TARGET L899) is a standalone layered couple whose layering is the trace of SOME ambient
canonical garden `H` at SOME addresses `(a, b)`.  We relocate C4's argument to the standard addresses `(0,[]), (1,[])` of `LQ`:

* `relocStd a b`: the standard addresses of `LQ` to the addresses of `H` (`(i, r) ↦ addrExt (a or b) r`); it commutes with extension,
  so links and pairs relocate (`cpl_links_map`, `cpl_pairs_map` of ZP-SURJ).
* `determined_of_drops`: an abstract form of C4's `layering_determined` (a layering below its parents, with the leaf-pair rule, is
  determined by its drops on the branching nodes).
* `trace_facts`: the standard trace of a coherent `LQ` satisfies these rules, with the drop budget `≤ ldist q q'` (C4's `cpl_budget`
  in `H`, relocated; incoherency `0` by `CohOn`).
* **`ncard_coherentCouples_le`**: the coherent layered couples of order `2m` with parents `(q, q')` number at most
  `(12^9)^m · 2^{2m} · 2^{ldist q q'}` (codes: `coupleCodeCount_le_pow`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree

set_option linter.unusedSectionVars false

section Reloc
variable {w : ℕ}

/-- The standard addresses of a couple to the addresses `(a, b)` of an ambient garden. -/
def relocStd (a b : Fin w × Path) (z : Fin 2 × Path) : Fin w × Path :=
  addrExt (if z.1 = 0 then a else b) z.2

theorem relocStd_ext (a b : Fin w × Path) (x : Fin 2 × Path) (q : Path) :
    relocStd a b (addrExt x q) = addrExt (relocStd a b x) q := by
  unfold relocStd addrExt
  simp [List.append_assoc]

theorem relocStd_a (a b : Fin w × Path) : relocStd a b ((0 : Fin 2), ([] : Path)) = a := by
  simp [relocStd, addrExt]

theorem relocStd_b (a b : Fin w × Path) : relocStd a b ((1 : Fin 2), ([] : Path)) = b := by
  simp [relocStd, addrExt]

theorem links_relocStd (Q : RegCpl) (a b : Fin w × Path) :
    Q.linksAt a b = (Q.linksAt ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))).map
      (fun l => (relocStd a b l.1, relocStd a b l.2)) := by
  have := WaveTurbulence.ZpSurj.cpl_links_map (fun _ => True) (relocStd a b) (fun _ _ _ => trivial)
    (fun x q _ => relocStd_ext a b x q) Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) trivial trivial
  rwa [relocStd_a, relocStd_b] at this

theorem pairs_relocStd (Q : RegCpl) (a b : Fin w × Path) :
    Q.pairsAt a b = (Q.pairsAt ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))).map
      (fun l => (relocStd a b l.1, relocStd a b l.2)) := by
  have := WaveTurbulence.ZpSurj.cpl_pairs_map (fun _ => True) (relocStd a b) (fun _ _ _ => trivial)
    (fun x q _ => relocStd_ext a b x q) Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) trivial trivial
  rwa [relocStd_a, relocStd_b] at this

theorem mem_pairEndpoints_map_of {L : List ((Fin 2 × Path) × (Fin 2 × Path))} (ρ : Fin 2 × Path → Fin w × Path)
    {z : Fin 2 × Path} (hz : z ∈ pairEndpoints L) : ρ z ∈ pairEndpoints (L.map fun l => (ρ l.1, ρ l.2)) := by
  obtain ⟨l, hl, h⟩ := (mem_pairEndpoints_iff _ _).1 hz
  refine (mem_pairEndpoints_iff _ _).2 ⟨(ρ l.1, ρ l.2), List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
  rcases h with h | h <;> subst h <;> simp

theorem pairEndpoints_map_eq {L : List ((Fin 2 × Path) × (Fin 2 × Path))} (ρ : Fin 2 × Path → Fin w × Path) :
    pairEndpoints (L.map fun l => (ρ l.1, ρ l.2)) = (pairEndpoints L).image ρ := by
  classical
  ext y
  rw [mem_pairEndpoints_iff, Finset.mem_image]
  constructor
  · rintro ⟨l', hl', h⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    rcases h with h | h
    · exact ⟨l.1, (mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩, h.symm⟩
    · exact ⟨l.2, (mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩, h.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_pairEndpoints_iff _ _).1 (mem_pairEndpoints_map_of ρ hz)

theorem relocStd_mem_cplNodes (Q : RegCpl) (a b : Fin w × Path) {z : Fin 2 × Path}
    (hz : z ∈ cplNodes Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))) : relocStd a b z ∈ cplNodes Q a b := by
  unfold cplNodes at hz ⊢
  rcases Finset.mem_union.1 hz with h | h
  · exact Finset.mem_union_left _ (by rw [links_relocStd]; exact mem_pairEndpoints_map_of _ h)
  · exact Finset.mem_union_right _ (by rw [pairs_relocStd]; exact mem_pairEndpoints_map_of _ h)

theorem relocStd_injective {a b : Fin w × Path} (hab : Indep a b) : Function.Injective (relocStd a b) := by
  rintro ⟨i, r⟩ ⟨i', r'⟩ h
  unfold relocStd addrExt at h
  by_cases hi : i = 0 <;> by_cases hi' : i' = 0
  · simp only [hi, hi', if_true, Prod.mk.injEq, List.append_cancel_left_eq, true_and] at h
    rw [hi, hi', h]
  · exfalso
    simp only [hi, hi', if_true, if_false, Prod.mk.injEq] at h
    rcases List.prefix_or_prefix_of_prefix (List.prefix_append a.2 r) (h.2 ▸ List.prefix_append b.2 r') with hp | hp
    · exact hab.1 ⟨h.1, hp⟩
    · exact hab.2 ⟨h.1.symm, hp⟩
  · exfalso
    simp only [hi, hi', if_true, if_false, Prod.mk.injEq] at h
    rcases List.prefix_or_prefix_of_prefix (List.prefix_append b.2 r) (h.2 ▸ List.prefix_append a.2 r') with hp | hp
    · exact hab.2 ⟨h.1, hp⟩
    · exact hab.1 ⟨h.1.symm, hp⟩
  · have e1 : i = 1 := by fin_cases i <;> simp_all
    have e2 : i' = 1 := by fin_cases i' <;> simp_all
    simp only [hi, hi', if_false, Prod.mk.injEq, List.append_cancel_left_eq, true_and] at h
    rw [e1, e2, h]

end Reloc

section Determined
variable {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) (q q' : ℕ)

/-- The rules of a layering of a placed code, read off its values (C4's `witness_facts`, abstractly). -/
structure LayerRules (f : Fin w × Path → ℕ) : Prop where
  below : ∀ z ∈ pairEndpoints (Q.linksAt a b), f z ≤ parF a b q q' f z
  leaf : ∀ qq ∈ Q.pairsAt a b, f qq.1 = min (parF a b q q' f qq.1) (parF a b q q' f qq.2) ∧
    f qq.2 = min (parF a b q q' f qq.1) (parF a b q q' f qq.2)
  off : ∀ z ∉ cplNodes Q a b, f z = 0

/-- **A layering is determined by its drops** (C4's `layering_determined`, from the rules only). -/
theorem determined_of_drops {f f' : Fin w × Path → ℕ} (hf : LayerRules Q a b q q' f) (hf' : LayerRules Q a b q q' f')
    (hd : dropF (pairEndpoints (Q.linksAt a b)) a b q q' f = dropF (pairEndpoints (Q.linksAt a b)) a b q q' f') :
    f = f' := by
  set B := pairEndpoints (Q.linksAt a b)
  have hpar : ∀ z ∈ cplNodes Q a b, (z ≠ a → z ≠ b → f (parentAddr z) = f' (parentAddr z)) →
      parF a b q q' f z = parF a b q q' f' z := by
    intro z _ h
    unfold parF
    by_cases hza : z = a
    · simp [hza]
    · by_cases hzb : z = b
      · simp [hzb]
      · simp only [hza, hzb, ↓reduceIte]; exact h hza hzb
  have e : ∀ {g : Fin w × Path → ℕ}, LayerRules Q a b q q' g → ∀ z ∈ B,
      g z = parF a b q q' g z - dropF B a b q q' g z := by
    intro g hg z hz
    unfold dropF; rw [if_pos hz]
    have := hg.below z hz; omega
  have hbr : ∀ n, ∀ z ∈ B, z.2.length ≤ n → f z = f' z := by
    intro n
    induction n with
    | zero =>
      intro z hz hl
      have hzn := links_sub_nodes hz
      rw [e hf z hz, e hf' z hz, hd]
      congr 1
      apply hpar z hzn
      intro hza hzb
      exfalso
      obtain ⟨-, i, hzi⟩ := parent_mem hzn hza hzb
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this; omega
    | succ n ih =>
      intro z hz hl
      have hzn := links_sub_nodes hz
      rw [e hf z hz, e hf' z hz, hd]
      congr 1
      apply hpar z hzn
      intro hza hzb
      obtain ⟨hpm, i, hzi⟩ := parent_mem hzn hza hzb
      apply ih _ hpm
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this
      simp [parentAddr]; omega
  have hbr' : ∀ z ∈ B, f z = f' z := fun z hz => hbr _ z hz le_rfl
  have hpar' : ∀ z ∈ cplNodes Q a b, parF a b q q' f z = parF a b q q' f' z := fun z hz =>
    hpar z hz fun hza hzb => hbr' _ (parent_mem hz hza hzb).1
  funext z
  by_cases hz : z ∈ cplNodes Q a b
  · rcases Finset.mem_union.1 hz with h | h
    · exact hbr' z h
    · obtain ⟨qq, hq, hzq⟩ := (mem_pairEndpoints_iff _ _).1 h
      have m1 : qq.1 ∈ cplNodes Q a b := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
      have m2 : qq.2 ∈ cplNodes Q a b := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
      rcases hzq with rfl | rfl
      · rw [(hf.leaf qq hq).1, (hf'.leaf qq hq).1, hpar' _ m1, hpar' _ m2]
      · rw [(hf.leaf qq hq).2, (hf'.leaf qq hq).2, hpar' _ m1, hpar' _ m2]
  · rw [hf.off z hz, hf'.off z hz]

end Determined

section Trace

/-- The standard addresses of a couple. -/
abbrev a₀ : Fin 2 × Path := ((0 : Fin 2), ([] : Path))
/-- The standard addresses of a couple. -/
abbrev b₀ : Fin 2 × Path := ((1 : Fin 2), ([] : Path))

theorem incohCount_zero_of_cohOn {w : ℕ} {LG : LayeredGarden w} {L : List ((Fin w × Path) × (Fin w × Path))}
    (h : CohOn LG L) : incohCount LG L = 0 := by
  unfold incohCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro l hl
  simpa using h l hl

/-- **The standard trace of a coherent couple obeys the layering rules, with drop budget `ldist q q'`.** -/
theorem trace_facts {p q q' : ℕ} {Q : RegCpl} {LQ : LayeredGarden 2} (h : IsCoherentCoupleAt p q q' Q LQ) :
    LayerRules Q a₀ b₀ q q' (coupleLayerTrace Q LQ) ∧
      ∑ z ∈ pairEndpoints (Q.linksAt a₀ b₀), dropF (pairEndpoints (Q.linksAt a₀ b₀)) a₀ b₀ q q' (coupleLayerTrace Q LQ) z ≤
        ldist q q' := by
  classical
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hemb, -, -, hcoh, hpa, hpb, hlay⟩ := h
  obtain ⟨hplain, -, hcrit⟩ := hcan
  have hE0 : Embeds LQ.garden Q a₀ b₀ := Embeds.of_decodes hQ
  set f := coupleLayerTrace Q LQ with hfdef
  set ρ := relocStd a b with hρ
  -- the values: `f z = layerAt H (ρ z)` on the nodes
  have hval : ∀ z ∈ cplNodes Q a₀ b₀, f z = layerAt H (ρ z) := by
    intro z hz
    have hn := hE0.mem_nodes hz
    rw [hfdef, coupleLayerTrace, if_pos hz, layerAt_of_mem LQ hn]
    exact hlay ⟨z, hn⟩
  have hmemH : ∀ z ∈ cplNodes Q a₀ b₀, (ρ z).2 ∈ (H.garden.tree (ρ z).1).nodes := fun z hz =>
    hemb.mem_nodes (relocStd_mem_cplNodes Q a b hz)
  -- the parent values: `parF f z = parAt H p (ρ z)` on the nodes
  have hpar : ∀ z ∈ cplNodes Q a₀ b₀, parF a₀ b₀ q q' f z = parAt H p (ρ z) := by
    intro z hz
    unfold parF
    by_cases hza : z = a₀
    · rw [if_pos hza, hza, hρ, relocStd_a, hpa]
    · rw [if_neg hza]
      by_cases hzb : z = b₀
      · rw [if_pos hzb, hzb, hρ, relocStd_b, hpb]
      · rw [if_neg hzb]
        obtain ⟨hpm, i, hzi⟩ := parent_mem hz hza hzb
        rw [hval _ (links_sub_nodes hpm)]
        have hz' : ρ z = addrExt (ρ (parentAddr z)) [i] := by
          rw [hρ, ← relocStd_ext]; exact congrArg _ hzi
        have hn' : (addrExt (ρ (parentAddr z)) [i]).2 ∈ (H.garden.tree (addrExt (ρ (parentAddr z)) [i]).1).nodes := by
          rw [← hz']; exact hmemH z hz
        rw [hz', parAt_child H p i hn']
  refine ⟨⟨fun z hz => ?_, fun qq hq => ?_, fun z hz => ?_⟩, ?_⟩
  · have hzn := links_sub_nodes hz
    rw [hval z hzn, hpar z hzn]
    exact layerAt_le_parAt H p hcrit.1 (hmemH z hzn)
  · have m1 : qq.1 ∈ cplNodes Q a₀ b₀ := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
    have m2 : qq.2 ∈ cplNodes Q a₀ b₀ := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
    have hqH : (ρ qq.1, ρ qq.2) ∈ Q.pairsAt a b := by
      rw [pairs_relocStd]; exact List.mem_map.2 ⟨qq, hq, rfl⟩
    have T := hemb.triv_of_pair hplain hqH
    have L1 := (cpl_coherent hcrit hplain .triv (ρ qq.1) (ρ qq.2) rfl T (by simp [CohOn, RegCpl.linksAt])).1 rfl
    rw [hval _ m1, hval _ m2, hpar _ m1, hpar _ m2]
    exact ⟨L1 _ (mem_cplNodes_triv.2 (Or.inl rfl)), L1 _ (mem_cplNodes_triv.2 (Or.inr rfl))⟩
  · rw [hfdef, coupleLayerTrace, if_neg hz]
  · -- the drop budget, relocated to `H`
    have hB : pairEndpoints (Q.linksAt a b) = (pairEndpoints (Q.linksAt a₀ b₀)).image ρ := by
      rw [links_relocStd, pairEndpoints_map_eq]
    have hbud := cpl_budget hcrit hplain Q a b hwf hemb
    rw [hpa, hpb, incohCount_zero_of_cohOn hcoh, mul_zero, add_zero, hB,
      budget, Finset.sum_image (fun x _ y _ hxy => relocStd_injective hemb.indep hxy)] at hbud
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z hz => ?_)) hbud
    have hzn := links_sub_nodes hz
    unfold dropF dropAt
    rw [if_pos hz, hpar z hzn, hval z hzn]

end Trace

section Count

/-- The coherent layered couples of a code with parent layers `(q, q')`. -/
def coherentCouplesOf (p q q' : ℕ) (Q : RegCpl) : Set (LayeredGarden 2) := {LQ | IsCoherentCoupleAt p q q' Q LQ}

/-- **The layerings of one code** (TARGET `layerreg2`, `g = 0`, standalone form). -/
theorem ncard_coherentCouplesOf_le (p q q' : ℕ) (Q : RegCpl) :
    (coherentCouplesOf p q q' Q).Finite ∧ (coherentCouplesOf p q q' Q).ncard ≤ 2 ^ (Q.size + ldist q q') := by
  classical
  set B := pairEndpoints (Q.linksAt a₀ b₀)
  set T := ldist q q'
  have hmap : ∀ LQ ∈ coherentCouplesOf p q q' Q,
      dropF B a₀ b₀ q q' (coupleLayerTrace Q LQ) ∈ boundedVecs B T := by
    intro LQ hLQ
    refine ⟨fun z hz => by unfold dropF; rw [if_neg hz], ?_⟩
    exact (trace_facts hLQ).2
  have hinj : Set.InjOn (fun LQ => dropF B a₀ b₀ q q' (coupleLayerTrace Q LQ)) (coherentCouplesOf p q q' Q) := by
    intro LQ hLQ LQ' hLQ' hd
    exact coupleLayerTrace_injective_of_decodes hLQ.2.1 hLQ'.2.1
      (determined_of_drops Q a₀ b₀ q q' (trace_facts hLQ).1 (trace_facts hLQ').1 hd)
  have hfin := (boundedVecs_spec B T).1
  refine ⟨Set.Finite.of_injOn hmap hinj hfin, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn _ hmap hinj hfin
  have hBc : B.card ≤ Q.size := by
    have h1 : B.card ≤ 2 * (Q.linksAt a₀ b₀).length := pairEndpoints_card_le _
    have h2 := couple_linksAt_length Q a₀ b₀
    omega
  calc _ ≤ (boundedVecs B T).ncard := hcard
    _ ≤ 2 ^ (B.card + T) := (boundedVecs_spec B T).2
    _ ≤ 2 ^ (Q.size + T) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The coherent layered couples of order `2m` with parent layers `(q, q')`. -/
def coherentCouples (p q q' m : ℕ) : Set (LayeredGarden 2) :=
  ⋃ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m}, coherentCouplesOf p q q' Q.1

/-- **The coherent couples of order `2m` with parents `(q, q')`** number at most `(12^9)^m · 2^{2m + ldist q q'}`. -/
theorem ncard_coherentCouples_le (p q q' m : ℕ) :
    (coherentCouples p q q' m).Finite ∧ (coherentCouples p q q' m).ncard ≤ (12 ^ 9) ^ m * 2 ^ (2 * m + ldist q q') := by
  classical
  let _ := finite_coupleCodes m
  let _ : Fintype {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m} := Fintype.ofFinite _
  refine ⟨Set.finite_iUnion fun Q => (ncard_coherentCouplesOf_le p q q' Q.1).1, ?_⟩
  have h := Set.ncard_iUnion_le_of_fintype (fun Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m} => coherentCouplesOf p q q' Q.1)
  have hsum : (∑ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m}, (coherentCouplesOf p q q' Q.1).ncard) ≤
      coupleCodeCount m * 2 ^ (2 * m + ldist q q') := by
    calc _ ≤ ∑ _Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * m}, 2 ^ (2 * m + ldist q q') := by
          apply Finset.sum_le_sum
          intro Q _
          simpa only [Q.2.2] using (ncard_coherentCouplesOf_le p q q' Q.1).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, coupleCodeCount, Nat.card_eq_fintype_card,
          Nat.cast_id]
  exact h.trans (hsum.trans (Nat.mul_le_mul_right _ (coupleCodeCount_le_pow m)))

end Count

end WaveTurbulence.VineEstS5C.P4
