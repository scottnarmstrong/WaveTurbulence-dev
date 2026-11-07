/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCFlow
/-! # VINE-COUNT part 7: the square circulation through two adjacent ladder rungs.

For two adjacent rungs `(t,s)`, `(t',s')` of a ladder (rails `p : t -- t'`, `p' : s -- s'` single bonds, rungs
`ρ : t -- s`, `ρ' : t' -- s'`), the circulation `z` supported on these four bonds with `z(p) = z(p') = 1` has zero flow
at every atom and changes the energy `E_t + E_s` by `-2 ι ⟨k_p - k_{p'}, e⟩` when `k ↦ k + z e` (`ι` the incidence of `p` at `t`);
the rung bonds cancel. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Inc
variable (M : Molecule V D)

theorem incidence_cases {e : D} {a b : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) :
    (incidence M a e = 1 ∧ incidence M b e = -1) ∨ (incidence M a e = -1 ∧ incidence M b e = 1) := by
  have h : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) :=
    Sym2.eq_iff.mp he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, ?_⟩ <;> simp [incidence, h1, h2, hab, hab.symm]
  · right
    refine ⟨?_, ?_⟩ <;> simp [incidence, h1, h2, hab, hab.symm]

theorem incidence_other {e : D} {a b v : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) (hva : v ≠ a) (hvb : v ≠ b) :
    incidence M v e = 0 := by
  have h : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) :=
    Sym2.eq_iff.mp he
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [incidence, h1, h2, hva, hvb, hva.symm, hvb.symm]

theorem incidence_sq {e : D} {a b : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) :
    incidence M a e * incidence M a e = 1 := by
  rcases incidence_cases M hab he with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> norm_num

theorem incidence_add {e : D} {a b : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) :
    incidence M a e + incidence M b e = 0 := by
  rcases incidence_cases M hab he with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> norm_num

theorem exists_bond {a b : V} (h : 0 < M.bondsBetween a b) : ∃ e, M.out e = true ∧ M.ends e = s(a, b) := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
  exact ⟨e, (Finset.mem_filter.mp h1).2, h2⟩

theorem bond_unique {a b : V} (h : M.bondsBetween a b = 1) {e e' : D} (he : M.out e = true)
    (he' : M.out e' = true) (h1 : M.ends e = s(a, b)) (h2 : M.ends e' = s(a, b)) : e = e' := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h
  have m1 : e ∈ M.bonds.filter (fun x => M.ends x = s(a, b)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, h1⟩
  have m2 : e' ∈ M.bonds.filter (fun x => M.ends x = s(a, b)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩, h2⟩
  have hz' : (M.bonds.filter (fun x => M.ends x = s(a, b))) = {z} := hz
  rw [hz', Finset.mem_singleton] at m1 m2
  rw [m1, m2]

/-- With a single bond `p : a -- b`, `Directed a b` iff `p` leaves `a`. -/
theorem directed_iff_atom {a b : V} (hab : a ≠ b) (h : M.bondsBetween a b = 1) {p : D} (hp : M.out p = true)
    (hpe : M.ends p = s(a, b)) : M.Directed a b ↔ M.atom p = a := by
  constructor
  · rintro ⟨x, hx1, hx2, hx3⟩
    have hxe : M.ends x = s(a, b) := by unfold Molecule.ends; rw [hx2, hx3]
    have := bond_unique M h hx1 hp hxe hpe
    rw [← this]; exact hx2
  · intro h1
    have h2 : M.atom (M.mate p) = b := by
      have : (M.atom p = a ∧ M.atom (M.mate p) = b) ∨ (M.atom p = b ∧ M.atom (M.mate p) = a) :=
        Sym2.eq_iff.mp hpe
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (h1.symm.trans h) hab
    exact ⟨p, hp, h1, h2⟩

end Inc

/-- Two adjacent rungs `(t,s)`, `(t',s')` of a ladder with their rails and rungs, as bonds of the group `S`. -/
structure Square (M : Molecule V D) (S : Finset V) (t s t' s' : V) where
  p : D
  p' : D
  ρ : D
  ρ' : D
  p_out : M.out p = true
  p'_out : M.out p' = true
  ρ_out : M.out ρ = true
  ρ'_out : M.out ρ' = true
  p_ends : M.ends p = s(t, t')
  p'_ends : M.ends p' = s(s, s')
  ρ_ends : M.ends ρ = s(t, s)
  ρ'_ends : M.ends ρ' = s(t', s')
  hdir : incidence M s p' = - incidence M t p
  hts : t ≠ s
  htt : t ≠ t'
  hts' : t ≠ s'
  hst : s ≠ t'
  hss : s ≠ s'
  ht's' : t' ≠ s'
  ht : t ∈ S
  hs : s ∈ S
  ht' : t' ∈ S
  hs' : s' ∈ S

namespace Square
variable {M : Molecule V D} {S : Finset V} {t s t' s' : V} (Q : Square M S t s t' s')

theorem p_ne_p' : Q.p ≠ Q.p' := fun h => by
  have := Q.p_ends; rw [h, Q.p'_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]
theorem p_ne_ρ : Q.p ≠ Q.ρ := fun h => by
  have := Q.p_ends; rw [h, Q.ρ_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]
theorem p_ne_ρ' : Q.p ≠ Q.ρ' := fun h => by
  have := Q.p_ends; rw [h, Q.ρ'_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]
theorem p'_ne_ρ : Q.p' ≠ Q.ρ := fun h => by
  have := Q.p'_ends; rw [h, Q.ρ_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]
theorem p'_ne_ρ' : Q.p' ≠ Q.ρ' := fun h => by
  have := Q.p'_ends; rw [h, Q.ρ'_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]
theorem ρ_ne_ρ' : Q.ρ ≠ Q.ρ' := fun h => by
  have := Q.ρ_ends; rw [h, Q.ρ'_ends] at this
  rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all [Q.hts, Q.htt, Q.hts', Q.hst, Q.hss, Q.ht's', Q.hts.symm, Q.htt.symm, Q.hts'.symm, Q.hst.symm, Q.hss.symm, Q.ht's'.symm]

theorem mem_bond {e : D} {a b : V} (hout : M.out e = true) (he : M.ends e = s(a, b)) (ha : a ∈ S) (hb : b ∈ S) :
    e ∈ internalBondSet M S := by
  have h : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) :=
    Sym2.eq_iff.mp he
  unfold internalBondSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ ha, h2 ▸ hb⟩
  · exact ⟨h1 ▸ hb, h2 ▸ ha⟩

theorem p_mem : Q.p ∈ internalBondSet M S := mem_bond Q.p_out Q.p_ends Q.ht Q.ht'
theorem p'_mem : Q.p' ∈ internalBondSet M S := mem_bond Q.p'_out Q.p'_ends Q.hs Q.hs'
theorem ρ_mem : Q.ρ ∈ internalBondSet M S := mem_bond Q.ρ_out Q.ρ_ends Q.ht Q.hs
theorem ρ'_mem : Q.ρ' ∈ internalBondSet M S := mem_bond Q.ρ'_out Q.ρ'_ends Q.ht' Q.hs'

/-- The circulation of the square. -/
noncomputable def zfun : D → ℤ := fun e =>
  (if e = Q.p then 1 else 0) + (if e = Q.p' then 1 else 0) +
  (if e = Q.ρ then -(incidence M t Q.p * incidence M t Q.ρ) else 0) +
  (if e = Q.ρ' then incidence M t Q.p * incidence M t' Q.ρ' else 0)

theorem inc_pm {e : D} {a b : V} (hab : a ≠ b) (he : M.ends e = s(a, b)) :
    incidence M a e = 1 ∨ incidence M a e = -1 := by
  rcases incidence_cases M hab he with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem zfun_p : Q.zfun Q.p = 1 := by
  simp [zfun, Q.p_ne_p', Q.p_ne_ρ, Q.p_ne_ρ']
theorem zfun_p' : Q.zfun Q.p' = 1 := by
  simp [zfun, Q.p_ne_p'.symm, Q.p'_ne_ρ, Q.p'_ne_ρ']
theorem zfun_ne {e : D} (h1 : e ≠ Q.p) (h2 : e ≠ Q.p') (h3 : e ≠ Q.ρ) (h4 : e ≠ Q.ρ') : Q.zfun e = 0 := by
  simp [zfun, h1, h2, h3, h4]

theorem zfun_abs (e : D) : |Q.zfun e| ≤ 1 := by
  by_cases h1 : e = Q.p
  · subst h1; rw [zfun_p]; simp
  by_cases h2 : e = Q.p'
  · subst h2; rw [zfun_p']; simp
  by_cases h3 : e = Q.ρ
  · subst h3
    have : Q.zfun Q.ρ = -(incidence M t Q.p * incidence M t Q.ρ) := by
      simp [zfun, Q.p_ne_ρ.symm, Q.p'_ne_ρ.symm, Q.ρ_ne_ρ']
    rw [this]
    rcases inc_pm (M := M) Q.hts Q.ρ_ends with h | h <;> rcases inc_pm (M := M) Q.htt Q.p_ends with h' | h' <;>
      simp [h, h']
  by_cases h4 : e = Q.ρ'
  · subst h4
    have : Q.zfun Q.ρ' = incidence M t Q.p * incidence M t' Q.ρ' := by
      simp [zfun, Q.p_ne_ρ'.symm, Q.p'_ne_ρ'.symm, Q.ρ_ne_ρ'.symm]
    rw [this]
    rcases inc_pm (M := M) Q.ht's' Q.ρ'_ends with h | h <;> rcases inc_pm (M := M) Q.htt Q.p_ends with h' | h' <;>
      simp [h, h']
  rw [zfun_ne Q h1 h2 h3 h4]; simp

theorem zfun_flow (v : V) : ∑ e : Bond M S, incidence M v e.1 * Q.zfun e.1 = 0 := by
  have h1 : ∑ e : Bond M S, incidence M v e.1 * Q.zfun e.1 =
      ∑ e ∈ internalBondSet M S, incidence M v e * Q.zfun e :=
    Finset.sum_coe_sort (internalBondSet M S) (fun e => incidence M v e * Q.zfun e)
  rw [h1]
  unfold zfun
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Q.p_mem, Q.p'_mem, Q.ρ_mem, Q.ρ'_mem, if_true]
  have fι : incidence M t Q.p * incidence M t Q.p = 1 := incidence_sq M Q.htt Q.p_ends
  have fa : incidence M t Q.ρ * incidence M t Q.ρ = 1 := incidence_sq M Q.hts Q.ρ_ends
  have fb : incidence M t' Q.ρ' * incidence M t' Q.ρ' = 1 := incidence_sq M Q.ht's' Q.ρ'_ends
  have f2 : incidence M t' Q.p = -incidence M t Q.p := by
    have := incidence_add M Q.htt Q.p_ends; linarith
  have f3 : incidence M s Q.p' = -incidence M t Q.p := Q.hdir
  have f4 : incidence M s' Q.p' = incidence M t Q.p := by
    have := incidence_add M Q.hss Q.p'_ends; linarith
  have f5 : incidence M s Q.ρ = -incidence M t Q.ρ := by
    have := incidence_add M Q.hts Q.ρ_ends; linarith
  have f6 : incidence M s' Q.ρ' = -incidence M t' Q.ρ' := by
    have := incidence_add M Q.ht's' Q.ρ'_ends; linarith
  by_cases vt : v = t
  · rw [vt, incidence_other M Q.hss Q.p'_ends Q.hts Q.hts', incidence_other M Q.ht's' Q.ρ'_ends Q.htt Q.hts']
    linear_combination (-(incidence M t Q.p)) * fa
  by_cases vs : v = s
  · rw [vs, incidence_other M Q.htt Q.p_ends Q.hts.symm Q.hst, incidence_other M Q.ht's' Q.ρ'_ends Q.hst Q.hss, f3, f5]
    linear_combination (incidence M t Q.p) * fa
  by_cases vt' : v = t'
  · rw [vt', incidence_other M Q.hss Q.p'_ends Q.hst.symm Q.ht's', incidence_other M Q.hts Q.ρ_ends Q.htt.symm Q.hst.symm, f2]
    linear_combination (incidence M t Q.p) * fb
  by_cases vs' : v = s'
  · rw [vs', incidence_other M Q.htt Q.p_ends Q.hts'.symm Q.ht's'.symm, incidence_other M Q.hts Q.ρ_ends Q.hts'.symm Q.hss.symm, f4, f6]
    linear_combination (-(incidence M t Q.p)) * fb
  rw [incidence_other M Q.htt Q.p_ends vt vt', incidence_other M Q.hss Q.p'_ends vs vs',
    incidence_other M Q.hts Q.ρ_ends vt vs, incidence_other M Q.ht's' Q.ρ'_ends vt' vs']
  simp

/-- The energy change of the rung atoms `t, s` under the square circulation: the rungs cancel. -/
theorem energy_shift (k : Bond M S → Mom d) (e0 : Mom d) :
    (energy M S (fun e => k e + (Q.zfun e.1 : ℝ) • e0) t + energy M S (fun e => k e + (Q.zfun e.1 : ℝ) • e0) s) -
      (energy M S k t + energy M S k s) =
    -2 * (incidence M t Q.p : ℝ) * inner ℝ (k ⟨Q.p, Q.p_mem⟩ - k ⟨Q.p', Q.p'_mem⟩) e0 := by
  unfold energy
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hpne : (⟨Q.p, Q.p_mem⟩ : Bond M S) ≠ ⟨Q.p', Q.p'_mem⟩ := fun h => Q.p_ne_p' (congrArg Subtype.val h)
  rw [Finset.sum_eq_add (⟨Q.p, Q.p_mem⟩ : Bond M S) ⟨Q.p', Q.p'_mem⟩ hpne]
  · simp only
    have e1 : incidence M s Q.p = 0 := incidence_other M Q.htt Q.p_ends Q.hts.symm Q.hst
    have e2 : incidence M t Q.p' = 0 := incidence_other M Q.hss Q.p'_ends Q.hts Q.hts'
    have e3 : incidence M s Q.p' = -incidence M t Q.p := Q.hdir
    have z1 : ((Q.zfun Q.p : ℤ) : ℝ) = 1 := by rw [Q.zfun_p]; simp
    have z2 : ((Q.zfun Q.p' : ℤ) : ℝ) = 1 := by rw [Q.zfun_p']; simp
    rw [e1, e2, e3, z1, z2]
    simp only [Int.cast_zero, Int.cast_neg, one_smul, norm_add_sq_real, inner_sub_left]
    push_cast
    ring
  · intro c _ hc
    obtain ⟨h1, h2⟩ := hc
    beta_reduce
    have hc1 : c.1 ≠ Q.p := fun h => h1 (Subtype.ext h)
    have hc2 : c.1 ≠ Q.p' := fun h => h2 (Subtype.ext h)
    by_cases hz : Q.zfun c.1 = 0
    · rw [hz]; simp
    · have : c.1 = Q.ρ ∨ c.1 = Q.ρ' := by
        by_contra hh
        rw [not_or] at hh
        exact hz (Q.zfun_ne hc1 hc2 hh.1 hh.2)
      rcases this with h | h
      · have := incidence_add M Q.hts Q.ρ_ends
        rw [h]
        have h' : (incidence M t Q.ρ : ℝ) + incidence M s Q.ρ = 0 := by exact_mod_cast this
        have h'' : (incidence M s Q.ρ : ℝ) = -incidence M t Q.ρ := by linarith
        rw [h'']; ring
      · rw [h, incidence_other M Q.ht's' Q.ρ'_ends Q.htt Q.hts', incidence_other M Q.ht's' Q.ρ'_ends Q.hst Q.hss]
        simp
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

end Square

end WaveTurbulence.VineCount
