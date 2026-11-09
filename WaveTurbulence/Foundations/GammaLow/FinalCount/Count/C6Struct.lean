/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Basic
public import WaveTurbulence.Foundations.FinalCount.ChainStruct
import Mathlib.Tactic

/-! # Case (6) of Prop 9.6: the atoms and the chains (packet L6-COUNT, Case6TopLow; M2 §4.10)

An even, non-cycle component `𝕄₀` with `V_α = 2`, `V_β = 1` (`c6_atoms`): two `α`-atoms `v₁ ≠ v₂`, one `β`-atom `b`, all
of degree two; every other atom is an `ε`-atom of degree four. Let `K₁` be the chain of `v₁` (operation (c)) and
`R = nonEps ∖ K₁ ⊆ {v₂, b}` the rest. `remaining_cases`: `R = ∅`, or `R` is one chain, or `R = {v₂, b}` with two
singleton chains. `chain_sub_of_meet`: chains meeting are nested (chains are classes). -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The atoms of case (6).** -/
theorem c6_atoms {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd)
    (ha : (alphaAtoms M.atoms cls).card = 2) (hb : (betaAtoms M.atoms cls).card = 1) :
    ∃ v₁ v₂ b, v₁ ∈ M.atoms ∧ v₂ ∈ M.atoms ∧ b ∈ M.atoms ∧ (cls v₁).IsAlpha ∧ (cls v₂).IsAlpha ∧
      (cls b).IsBeta ∧ v₁ ≠ v₂ ∧ v₁ ≠ b ∧ v₂ ≠ b ∧ alphaAtoms M.atoms cls = {v₁, v₂} ∧
      (∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = v₁ ∨ v = v₂ ∨ v = b)) ∧
      M.deg v₁ = 2 ∧ M.deg v₂ = 2 ∧ M.deg b = 2 ∧
      (∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4 ∧ (cls v).IsEps) := by
  classical
  obtain ⟨v₁, v₂, hne12, ha0⟩ := card_eq_two.mp ha
  obtain ⟨b, hb0⟩ := card_eq_one.mp hb
  have h1A : v₁ ∈ alphaAtoms M.atoms cls := by rw [ha0]; simp
  have h2A : v₂ ∈ alphaAtoms M.atoms cls := by rw [ha0]; simp
  have hbB : b ∈ betaAtoms M.atoms cls := by rw [hb0]; exact mem_singleton_self _
  obtain ⟨h11, h12⟩ := mem_filter.mp h1A
  obtain ⟨h21, h22⟩ := mem_filter.mp h2A
  obtain ⟨hb1, hb2⟩ := mem_filter.mp hbB
  have hab : ∀ v, (cls v).IsAlpha → (cls v).IsBeta → False := fun v h1 h2 => by
    cases hc : cls v <;> simp_all [Cls.IsAlpha, Cls.IsBeta]
  have hne1b : v₁ ≠ b := by rintro rfl; exact hab _ h12 hb2
  have hne2b : v₂ ≠ b := by rintro rfl; exact hab _ h22 hb2
  have hchar : ∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = v₁ ∨ v = v₂ ∨ v = b) := by
    intro v hv
    constructor
    · intro hn
      rcases cls_nonEps_cases hn with h | h
      · have : v ∈ alphaAtoms M.atoms cls := mem_filter.mpr ⟨hv, h⟩
        rw [ha0] at this
        rcases mem_insert.mp this with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl (mem_singleton.mp e))
      · have : v ∈ betaAtoms M.atoms cls := mem_filter.mpr ⟨hv, h⟩
        rw [hb0] at this; exact Or.inr (Or.inr (mem_singleton.mp this))
    · rintro (rfl | rfl | rfl)
      · exact alpha_not_eps h12
      · exact alpha_not_eps h22
      · exact beta_not_eps hb2
  have hd2 : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → M.deg v = 2 := by
    intro v hv hn
    have := (hS.classes v hv).mpr hn
    rcases hS.evenDeg hnodd v hv with h | h <;> omega
  refine ⟨v₁, v₂, b, h11, h21, hb1, h12, h22, hb2, hne12, hne1b, hne2b, ha0, hchar,
    hd2 v₁ h11 (alpha_not_eps h12), hd2 v₂ h21 (alpha_not_eps h22), hd2 b hb1 (beta_not_eps hb2), ?_⟩
  intro v hv n1 n2 n3
  have hn : (cls v).IsEps := by
    by_contra hn
    rcases (hchar v hv).mp hn with h | h | h
    · exact n1 h
    · exact n2 h
    · exact n3 h
  have : ¬ M.deg v ≤ 2 := fun h => ((hS.classes v hv).mp h) hn
  refine ⟨?_, hn⟩
  rcases hS.evenDeg hnodd v hv with h | h <;> omega

/-- **Chains are classes**: a chain set meeting the chain set `K` is contained in it. -/
theorem chain_sub_of_meet {M : Molecule V D} {cls : V → Cls} {K K' : Finset V} (hK : IsChainSet M cls K)
    (hK' : IsChainSet M cls K') {x : V} (hx : x ∈ K) (hx' : x ∈ K') : K' ⊆ K := by
  intro y hy
  have key : ∀ a c, Relation.EqvGen (fun a b => a ∈ K' ∧ b ∈ K' ∧ M.Adj a b) a c → (a ∈ K ↔ c ∈ K) := by
    intro a c h
    induction h with
    | rel a c hac =>
      obtain ⟨ha, hc, hadj⟩ := hac
      exact ⟨fun h => hK.2.2.2.1 a h c hadj (hK'.2.2.1 c hc),
        fun h => hK.2.2.2.1 c h a (Mole.adj_symmetric M hadj) (hK'.2.2.1 a ha)⟩
    | refl a => exact Iff.rfl
    | symm a c _ ih => exact ih.symm
    | trans a c e _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key x y (hK'.2.2.2.2 x hx' y hy)).mp hx

/-- A singleton of a non-`ε` atom none of whose neighbours is non-`ε` is a chain set. -/
theorem isChainSet_singleton {M : Molecule V D} {cls : V → Cls} {r : V} (hr : r ∈ M.atoms) (hrn : ¬ (cls r).IsEps)
    (hadj : ∀ w, M.Adj r w → ¬ (cls w).IsEps → w = r) : IsChainSet M cls {r} := by
  refine ⟨⟨r, mem_singleton_self _⟩, by simpa using hr, fun v hv => by rw [mem_singleton.mp hv]; exact hrn, ?_, ?_⟩
  · intro u hu w hw hwn
    rw [mem_singleton.mp hu] at hw
    exact mem_singleton.mpr (hadj w hw hwn)
  · intro u hu w hw
    rw [mem_singleton.mp hu, mem_singleton.mp hw]; exact Relation.EqvGen.refl _

/-- **The remaining chains of case (6)**: with `K₁` the chain of `v₁` and `R = nonEps ∖ K₁`, either `R = ∅`, or `R`
is one chain, or `R = {v₂, b}` with `{v₂}` and `{b}` two chains. -/
theorem remaining_cases {M : Molecule V D} {cls : V → Cls} {v₁ v₂ b : V} {K₁ : Finset V}
    (hK₁ : IsChainSet M cls K₁) (hv₁ : v₁ ∈ K₁) (h2 : v₂ ∈ M.atoms) (hb : b ∈ M.atoms) (hn2 : ¬ (cls v₂).IsEps)
    (hnb : ¬ (cls b).IsEps) (h2b : v₂ ≠ b)
    (hchar : ∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = v₁ ∨ v = v₂ ∨ v = b)) :
    nonEps M.atoms cls \ K₁ = ∅ ∨ IsChainSet M cls (nonEps M.atoms cls \ K₁) ∨
      (nonEps M.atoms cls \ K₁ = {v₂, b} ∧ IsChainSet M cls {v₂} ∧ IsChainSet M cls {b}) := by
  classical
  set R := nonEps M.atoms cls \ K₁ with hR
  have hRsub : ∀ x ∈ R, x = v₂ ∨ x = b := by
    intro x hx
    obtain ⟨hxN, hxK⟩ := mem_sdiff.mp hx
    obtain ⟨hxA, hxn⟩ := mem_filter.mp hxN
    rcases (hchar x hxA).mp hxn with e | e | e
    · exact absurd (e ▸ hv₁) hxK
    · exact Or.inl e
    · exact Or.inr e
  -- the chain of a remaining atom stays in `R`
  have hchainR : ∀ r ∈ R, ∀ K, IsChainSet M cls K → r ∈ K → K ⊆ R := by
    intro r hr K hK hrK x hx
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hK.2.1 hx, hK.2.2.1 x hx⟩, fun hxK₁ => ?_⟩
    have := chain_sub_of_meet hK₁ hK hxK₁ hx hrK
    exact (mem_sdiff.mp hr).2 this
  rcases R.eq_empty_or_nonempty with h0 | ⟨r, hr⟩
  · exact Or.inl h0
  right
  obtain ⟨Kr, hKr, hrKr⟩ := exists_chainSet M cls (hK₁.2.1.trans (by rfl) |> fun _ =>
    (mem_filter.mp (mem_sdiff.mp hr).1).1) (mem_filter.mp (mem_sdiff.mp hr).1).2
  have hKrR := hchainR r hr Kr hKr hrKr
  by_cases hEq : Kr = R
  · left; rw [← hEq]; exact hKr
  · right
    -- `R` has two elements, `Kr` one of them
    have hRpair : R = {v₂, b} := by
      ext x
      constructor
      · intro hx; rcases hRsub x hx with rfl | rfl <;> simp
      · intro hx
        by_contra hxR
        apply hEq
        refine Finset.Subset.antisymm hKrR fun y hy => ?_
        rcases hRsub y hy with rfl | rfl <;> rcases mem_insert.mp hx with e | e
        · exact absurd (e ▸ hy) hxR
        · have e' := mem_singleton.mp e
          rcases hRsub r hr with er | er
          · exact er ▸ hrKr
          · exfalso; apply hxR; rw [e']; exact er ▸ hr
        · rcases hRsub r hr with er | er
          · exfalso; apply hxR; rw [e]; exact er ▸ hr
          · exact er ▸ hrKr
        · exact absurd ((mem_singleton.mp e) ▸ hy) hxR
    refine ⟨hRpair, ?_, ?_⟩
    · -- `{v₂}` is a chain
      have hv₂R : v₂ ∈ R := by rw [hRpair]; simp
      obtain ⟨K2, hK2, hv₂K2⟩ := exists_chainSet M cls h2 hn2
      have hK2R := hchainR v₂ hv₂R K2 hK2 hv₂K2
      have hK2eq : K2 = {v₂} := by
        refine Finset.Subset.antisymm (fun y hy => ?_) (by simpa using hv₂K2)
        rcases hRsub y (hK2R hy) with rfl | rfl
        · simp
        · exfalso
          -- then `K2 = R`, and `Kr ⊆ K2` gives `Kr = R`
          have hK2all : K2 = R := by
            refine Finset.Subset.antisymm hK2R fun z hz => ?_
            rcases hRsub z hz with rfl | rfl
            · exact hv₂K2
            · exact hy
          exact hEq (Finset.Subset.antisymm hKrR (by
            rw [← hK2all]; exact chain_sub_of_meet hKr hK2 hrKr (hK2all ▸ hr)))
      exact hK2eq ▸ hK2
    · have hbR : b ∈ R := by rw [hRpair]; simp
      obtain ⟨K3, hK3, hbK3⟩ := exists_chainSet M cls hb hnb
      have hK3R := hchainR b hbR K3 hK3 hbK3
      have hK3eq : K3 = {b} := by
        refine Finset.Subset.antisymm (fun y hy => ?_) (by simpa using hbK3)
        rcases hRsub y (hK3R hy) with rfl | rfl
        · exfalso
          have hK3all : K3 = R := by
            refine Finset.Subset.antisymm hK3R fun z hz => ?_
            rcases hRsub z hz with rfl | rfl
            · exact hy
            · exact hbK3
          exact hEq (Finset.Subset.antisymm hKrR (by
            rw [← hK3all]; exact chain_sub_of_meet hKr hK3 hrKr (hK3all ▸ hr)))
        · simp
      exact hK3eq ▸ hK3

end

end WaveTurbulence.GammaLow.FinalCount.Count
