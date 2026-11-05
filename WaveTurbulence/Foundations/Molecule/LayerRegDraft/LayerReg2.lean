/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Count

/-!
# TARGET Prop `layerreg2`: the number of layerings of an embedded regular couple

See `Count.lean` for the statement and the strategy.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **The layerings induced on an embedded regular couple** (TARGET `layerreg2`): restrictions to the
nodes of `𝒬` (zero elsewhere) of the layers of the layered gardens satisfying the canonicity criterion
`CanonCriterion p` (plain), in which `𝒬` (code `Q`) is embedded at `(a, b)` with parent layers `q, q'`
and incoherency index `g`. -/
def inducedLayerings (p : ℕ) (Q : RegCpl) (a b : Fin w × Path) (q q' g : ℕ) :
    Set (Fin w × Path → ℕ) :=
  {f | ∃ LG : LayeredGarden w, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ Embeds LG.garden Q a b ∧
    parAt LG p a = q ∧ parAt LG p b = q' ∧ incohCount LG (Q.linksAt a b) = g ∧
    ∀ z, f z = if z ∈ cplNodes Q a b then layerAt LG z else 0}

/-- The parent value of an address, read from a layering `f` (`q`, `q'` at the roots). -/
def parF (a b : Fin w × Path) (q q' : ℕ) (f : Fin w × Path → ℕ) (z : Fin w × Path) : ℕ :=
  if z = a then q else if z = b then q' else f (parentAddr z)

/-- The drops of a layering at the addresses of `B`. -/
def dropF (B : Finset (Fin w × Path)) (a b : Fin w × Path) (q q' : ℕ) (f : Fin w × Path → ℕ)
    (z : Fin w × Path) : ℕ :=
  if z ∈ B then parF a b q q' f z - f z else 0

variable {p : ℕ} {Q : RegCpl} {a b : Fin w × Path} {q q' g : ℕ}

theorem links_sub_nodes {z : Fin w × Path} (hz : z ∈ pairEndpoints (Q.linksAt a b)) :
    z ∈ cplNodes Q a b := Finset.mem_union_left _ hz

theorem pairs_sub_nodes {z : Fin w × Path} (hz : z ∈ pairEndpoints (Q.pairsAt a b)) :
    z ∈ cplNodes Q a b := Finset.mem_union_right _ hz

/-- Facts about an induced layering, read through a witness. -/
theorem witness_facts {f : Fin w × Path → ℕ} {LG : LayeredGarden w}
    (hE : Embeds LG.garden Q a b) (ha : parAt LG p a = q) (hb : parAt LG p b = q')
    (hf : ∀ z, f z = if z ∈ cplNodes Q a b then layerAt LG z else 0) :
    (∀ z ∈ cplNodes Q a b, f z = layerAt LG z) ∧
    (∀ z ∈ cplNodes Q a b, parF a b q q' f z = parAt LG p z) := by
  have W1 : ∀ z ∈ cplNodes Q a b, f z = layerAt LG z := fun z hz => by rw [hf z, ite_pos_of hz]
  refine ⟨W1, fun z hz => ?_⟩
  unfold parF
  by_cases hza : z = a
  · rw [ite_pos_of hza, hza, ha]
  · rw [ite_neg_of hza]
    by_cases hzb : z = b
    · rw [ite_pos_of hzb, hzb, hb]
    · rw [ite_neg_of hzb]
      obtain ⟨hpm, i, hzi⟩ := parent_mem hz hza hzb
      rw [W1 _ (links_sub_nodes hpm)]
      have hn := hE.mem_nodes hz
      have hn' : (addrExt (parentAddr z) [i]).2 ∈ (LG.garden.tree (addrExt (parentAddr z) [i]).1).nodes := by
        rw [← hzi]; exact hn
      have := parAt_child LG p i hn'
      rw [← hzi] at this
      exact this.symm

/-- **The layering is determined by its drops** (given `q, q'`). -/
theorem layering_determined {f f' : Fin w × Path → ℕ} (hf : f ∈ inducedLayerings p Q a b q q' g)
    (hf' : f' ∈ inducedLayerings p Q a b q q' g)
    (hd : dropF (pairEndpoints (Q.linksAt a b)) a b q q' f =
      dropF (pairEndpoints (Q.linksAt a b)) a b q q' f') : f = f' := by
  obtain ⟨LG, hcan, hplain, hE, ha, hb, -, hfz⟩ := hf
  obtain ⟨LG', hcan', hplain', hE', ha', hb', -, hfz'⟩ := hf'
  obtain ⟨W1, W2⟩ := witness_facts hE ha hb hfz
  obtain ⟨W1', W2'⟩ := witness_facts hE' ha' hb' hfz'
  set B := pairEndpoints (Q.linksAt a b)
  -- parent values agree where the parents agree
  have hpar : ∀ z ∈ cplNodes Q a b, (z ≠ a → z ≠ b → f (parentAddr z) = f' (parentAddr z)) →
      parF a b q q' f z = parF a b q q' f' z := by
    intro z _ h
    unfold parF
    by_cases hza : z = a
    · simp [hza]
    · by_cases hzb : z = b
      · simp [hzb]
      · simp only [hza, hzb, ↓reduceIte]; exact h hza hzb
  -- branching nodes, by induction on the depth
  have hbr : ∀ n, ∀ z ∈ B, z.2.length ≤ n → f z = f' z := by
    intro n
    induction n with
    | zero =>
      intro z hz hl
      have hzn := links_sub_nodes hz
      have e1 : f z = parF a b q q' f z - dropF B a b q q' f z := by
        unfold dropF; rw [ite_pos_of hz, W2 z hzn, W1 z hzn]
        have := layerAt_le_parAt LG p hcan.1 (hE.mem_nodes hzn); omega
      have e2 : f' z = parF a b q q' f' z - dropF B a b q q' f' z := by
        unfold dropF; rw [ite_pos_of hz, W2' z hzn, W1' z hzn]
        have := layerAt_le_parAt LG' p hcan'.1 (hE'.mem_nodes hzn); omega
      rw [e1, e2, hd]
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
      have e1 : f z = parF a b q q' f z - dropF B a b q q' f z := by
        unfold dropF; rw [ite_pos_of hz, W2 z hzn, W1 z hzn]
        have := layerAt_le_parAt LG p hcan.1 (hE.mem_nodes hzn); omega
      have e2 : f' z = parF a b q q' f' z - dropF B a b q q' f' z := by
        unfold dropF; rw [ite_pos_of hz, W2' z hzn, W1' z hzn]
        have := layerAt_le_parAt LG' p hcan'.1 (hE'.mem_nodes hzn); omega
      rw [e1, e2, hd]
      congr 1
      apply hpar z hzn
      intro hza hzb
      obtain ⟨hpm, i, hzi⟩ := parent_mem hzn hza hzb
      apply ih _ hpm
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this
      simp [parentAddr]; omega
  have hbr' : ∀ z ∈ B, f z = f' z := fun z hz => hbr _ z hz le_rfl
  -- leaves
  have hpar' : ∀ z ∈ cplNodes Q a b, parF a b q q' f z = parF a b q q' f' z := fun z hz =>
    hpar z hz fun hza hzb => hbr' _ (parent_mem hz hza hzb).1
  funext z
  by_cases hz : z ∈ cplNodes Q a b
  · rcases Finset.mem_union.1 hz with h | h
    · exact hbr' z h
    · obtain ⟨qq, hq, hzq⟩ := (mem_pairEndpoints_iff _ _).1 h
      have T := hE.triv_of_pair hplain hq
      have T' := hE'.triv_of_pair hplain' hq
      have L1 := (cpl_coherent hcan hplain .triv qq.1 qq.2 rfl T (by simp [CohOn, RegCpl.linksAt])).1
        rfl
      have L1' := (cpl_coherent hcan' hplain' .triv qq.1 qq.2 rfl T'
        (by simp [CohOn, RegCpl.linksAt])).1 rfl
      have m1 : qq.1 ∈ cplNodes Q a b := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
      have m2 : qq.2 ∈ cplNodes Q a b := pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
      have hz' : z ∈ cplNodes RegCpl.triv qq.1 qq.2 := by
        rw [mem_cplNodes_triv]; exact hzq
      rw [W1 z hz, W1' z hz, L1 z hz', L1' z hz', ← W2 _ m1, ← W2 _ m2, ← W2' _ m1, ← W2' _ m2,
        hpar' _ m1, hpar' _ m2]
  · rw [hfz z, hfz' z, ite_neg_of hz, ite_neg_of hz]

/-- **TARGET Prop `layerreg2` (couples)**: the number of layerings that layered gardens satisfying
the canonicity criterion `CanonCriterion p` induce on an embedded regular couple of order `n(𝒬)` with
parent layers `(q, q')` and incoherency index `g` is at most `(2^{9p})^g · 2^{n(𝒬)} · 2^{|q - q'|}`
(TARGET: `C₂^g C₀^{m + |q - q'|}` with `2m = n(𝒬)`, here `C₀ = 4`, `C₂ = 2^{9p}`). -/
theorem layerreg2 (Q : RegCpl) (hwf : Q.wf = true) (a b : Fin w × Path) (p q q' g : ℕ) :
    (inducedLayerings p Q a b q q' g).ncard ≤ (2 ^ (9 * p)) ^ g * 2 ^ Q.size * 2 ^ ldist q q' := by
  set B := pairEndpoints (Q.linksAt a b)
  set T := ldist q q' + 9 * p * g
  have hmap : ∀ f ∈ inducedLayerings p Q a b q q' g, dropF B a b q q' f ∈ boundedVecs B T := by
    rintro f ⟨LG, hcan, hplain, hE, ha, hb, hg, hfz⟩
    obtain ⟨W1, W2⟩ := witness_facts hE ha hb hfz
    refine ⟨fun z hz => by unfold dropF; rw [ite_neg_of hz], ?_⟩
    have hbud := cpl_budget hcan hplain Q a b hwf hE
    rw [ha, hb, hg] at hbud
    calc ∑ z ∈ B, dropF B a b q q' f z = budget LG p B :=
          Finset.sum_congr rfl fun z hz => by
            unfold dropF dropAt
            rw [ite_pos_of hz, W2 z (links_sub_nodes hz), W1 z (links_sub_nodes hz)]
      _ ≤ T := hbud
  have hinj : Set.InjOn (dropF B a b q q' ·) (inducedLayerings p Q a b q q' g) :=
    fun f hf f' hf' hd => layering_determined hf hf' hd
  have hcard := Set.ncard_le_ncard_of_injOn _ hmap hinj (boundedVecs_spec B T).1
  have hB : B.card ≤ Q.size := by
    have h1 : B.card ≤ 2 * (Q.linksAt a b).length := pairEndpoints_card_le _
    have h2 := couple_linksAt_length Q a b
    omega
  calc (inducedLayerings p Q a b q q' g).ncard ≤ (boundedVecs B T).ncard := hcard
    _ ≤ 2 ^ (B.card + T) := (boundedVecs_spec B T).2
    _ ≤ 2 ^ (Q.size + T) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ (9 * p)) ^ g * 2 ^ Q.size * 2 ^ ldist q q' := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

end WaveTurbulence.Links
