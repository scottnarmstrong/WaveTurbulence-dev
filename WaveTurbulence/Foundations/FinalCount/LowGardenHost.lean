/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGHost2
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN): `HostConn` without the degree-`3` hypothesis.**

`hostConnL_of` is `hostConn_of` (AsmGHost2) with `h3 : ∀ v ∈ M.atoms, 3 ≤ M.deg v` removed.  It was used only to place the cut atom
`x` in the interior of an ordinary three-atom object (a joint has internal degree `2`).  Now: if `x` is a joint of `U = {a, x, b}`
(ordinary: `deg x = degIn x = 2`; hyper: `3`), then `deg x ≤ 3`, and `hyper_interior_bond_other` gives a bond from the interior atom
`m` to the other joint `j'` (the four darts at `m` cannot all go to `x`), which no piece kills; otherwise `x` is interior and
`ordinary_host_conn` / the retained added bond of a hyper object are as before. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.Vine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

section host
variable {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c0 : V → Mom d}
  (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
  {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Object M)}
  (hd22 : ∀ O ∈ C.C2Of L γ η w κ (Un κ), ∀ O' ∈ C.C2Of L γ η w κ (Un κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
  (hsh : ∀ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) →
    DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨ M.IsVine .V O.atoms O.upper O.lower)
  (hUO : C.UnselOK L γ η w κ (Un κ))
include hM hκ hc0 hd22 hsh hUO

/-- **`HostConn`, one decoration, no degree hypothesis.** -/
theorem hostConnL_of (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hC13 : ∀ i, (C.collection i).atoms.card ≠ 3)
    (ps : List (Object M × Quad D)) (U : Object M) (a x b : V)
    (hps : ∀ p ∈ ps, PieceData C Un L γ η w κ p) (hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms))
    (hdisU : ∀ p ∈ ps, Disjoint p.1.atoms U.atoms) (hUc : Collected C (Un κ) L γ η w κ U) (hUat : U.atoms = {a, x, b})
    (hax : a ≠ x) (hxb : x ≠ b) (hab : a ≠ b)
    (hclos : ∀ z, M.atom z = x → M.atom (M.mate z) = a ∨ M.atom (M.mate z) = b) :
    ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) a b := by
  have hcard : U.atoms.card = 3 := by
    rw [hUat, Finset.card_insert_of_notMem (by simp [hax, hab]), Finset.card_pair hxb]
  have hU : U ∈ C.C2Can L γ η w κ (Un κ) := by
    rcases hUc with ⟨i, hi⟩ | h
    · exact absurd (hi ▸ hcard) (hC13 i)
    · exact h
  have hxU : x ∈ U.atoms := by rw [hUat]; simp
  have haU : a ∈ U.atoms := by rw [hUat]; simp
  have hbU : b ∈ U.atoms := by rw [hUat]; simp
  have hallx : ∀ z, M.atom z = x → M.InGroup U.atoms z := by
    intro z hz
    refine ⟨hz ▸ hxU, ?_⟩
    rcases hclos z hz with e | e <;> rw [e]
    · exact haU
    · exact hbU
  have hdegx : M.degIn U.atoms x = M.deg x := degIn_eq_deg_of_all hallx
  have hxM : x ∈ M.atoms := objectAtoms_sub' U hxU
  have hKS : ∀ z, z ∈ (⋃ p ∈ ps, PieceKill p.1 p.2) ↔ z ∈ KillS ps := by
    intro z
    simp only [Set.mem_iUnion, exists_prop]
    rfl
  have hfree : ∀ z, M.atom z ∈ U.atoms → z ∉ (⋃ p ∈ ps, PieceKill p.1 p.2) := by
    intro z hz hk
    rw [hKS] at hk
    exact not_mem_killS_of_atom (fun p hp hzp => Finset.disjoint_left.1 (hdisU p hp) hzp hz) hk
  have huU := object_mem_of_joint U (Or.inl rfl)
  have hlU := object_mem_of_joint U (Or.inr rfl)
  have hul : U.upper ≠ U.lower := (object_oh U).basic.2.2.2.1
  have hmem3 : ∀ v ∈ U.atoms, v = a ∨ v = x ∨ v = b := by
    intro v hv; rw [hUat] at hv; simpa using hv
  -- if `x` is not a joint, the joints are `a`, `b`
  have hjab : x ≠ U.upper → x ≠ U.lower → (U.upper = a ∧ U.lower = b) ∨ (U.upper = b ∧ U.lower = a) := by
    intro h1 h2
    rcases hmem3 _ huU with e1 | e1 | e1 <;> rcases hmem3 _ hlU with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) hul
    · exact absurd e2.symm h2
    · exact Or.inl ⟨e1, e2⟩
    · exact absurd e1.symm h1
    · exact absurd e1.symm h1
    · exact absurd e1.symm h1
    · exact Or.inr ⟨e1, e2⟩
    · exact absurd e2.symm h2
    · exact absurd (e1.trans e2.symm) hul
  have hgood : ∀ z, M.atom z ∈ U.atoms → M.atom (M.mate z) ∈ U.atoms → M.atom z ≠ x → M.atom (M.mate z) ≠ x →
      z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) ∧
        M.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) := by
    intro z h1 h2 h3' h4
    refine ⟨fun hk => hk.elim (hfree z h1) h3', fun hk => hk.elim (hfree _ h2) h4⟩
  by_cases hxj : x = U.upper ∨ x = U.lower
  · -- `x` is a joint (degree `2` for an ordinary object, `3` for a hyper one): a bond from the interior atom to the other joint
    have hdx : M.deg x ≤ 3 := by
      rcases object_shape_cases U with hvc | ⟨R, hR⟩
      · have := object_vc_degIn U hvc hxj
        omega
      · have := object_hyper_degIn U ⟨R, hR⟩ hxj
        omega
    -- the other joint `j'` and the interior atom `m`
    obtain ⟨j', m, hj'ab, hmab, hjm, hm, hatm⟩ : ∃ j' m, (j' = a ∨ j' = b) ∧ (m = a ∨ m = b) ∧ j' ≠ m ∧ U.IsInterior m ∧
        U.atoms = {x, m, j'} := by
      rcases hxj with e | e
      · rcases hmem3 _ hlU with e2 | e2 | e2
        · refine ⟨a, b, Or.inl rfl, Or.inr rfl, hab, ⟨hbU, ?_, ?_⟩, ?_⟩
          · rw [← e]; exact hxb.symm
          · rw [e2]; exact hab.symm
          · rw [hUat]; ext v; simp; tauto
        · exact absurd (e.symm.trans e2.symm) hul
        · refine ⟨b, a, Or.inr rfl, Or.inl rfl, hab.symm, ⟨haU, ?_, ?_⟩, ?_⟩
          · rw [← e]; exact hax
          · rw [e2]; exact hab
          · rw [hUat]; ext v; simp; tauto
      · rcases hmem3 _ huU with e2 | e2 | e2
        · refine ⟨a, b, Or.inl rfl, Or.inr rfl, hab, ⟨hbU, ?_, ?_⟩, ?_⟩
          · rw [e2]; exact hab.symm
          · rw [← e]; exact hxb.symm
          · rw [hUat]; ext v; simp; tauto
        · exact absurd (e2.trans e) hul
        · refine ⟨b, a, Or.inr rfl, Or.inl rfl, hab.symm, ⟨haU, ?_, ?_⟩, ?_⟩
          · rw [e2]; exact hab
          · rw [← e]; exact hax
          · rw [hUat]; ext v; simp; tauto
    obtain ⟨z, hz1, hz2⟩ := hyper_interior_bond_other hnl U hatm hm hdx
    have hmx : m ≠ x := by rcases hmab with rfl | rfl; exacts [hax, hxb.symm]
    have hjx : j' ≠ x := by rcases hj'ab with rfl | rfl; exacts [hax, hxb.symm]
    have hg := hgood z (hz1 ▸ hm.1) (hz2 ▸ (by rw [hatm]; simp)) (hz1 ▸ hmx) (hz2 ▸ hjx)
    have hc := connAvoid_of_bond z hz1 hz2 hg.1 hg.2
    rcases hj'ab with rfl | rfl <;> rcases hmab with rfl | rfl
    · exact absurd rfl hjm
    · exact Relation.EqvGen.symm _ _ hc
    · exact hc
    · exact absurd rfl hjm
  · push Not at hxj
    rcases object_shape_cases U with hvc | ⟨R, hR⟩
    · -- ordinary: `x` is interior
      have hx1 : x ≠ U.upper := hxj.1
      have hx2 : x ≠ U.lower := hxj.2
      have h := ordinary_host_conn hM hκ hc0 hd22 hsh hUO hnl hU hvc ps hps hpw true (fun _ q hq => hdisU q hq)
      have h' : ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) U.upper U.lower := by
        refine connAvoid_mono ?_ h
        rintro z (hk | hk)
        · exact Or.inl ((hKS z).1 hk)
        · right
          simp only [ite_true, Set.mem_ofPred_eq]
          have hk' : M.atom z = x := hk
          rw [hk']; exact ⟨hxU, hx1, hx2⟩
      rcases hjab hx1 hx2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at h'; exact h'
      · rw [e1, e2] at h'; exact Relation.EqvGen.symm _ _ h'
    · have key : ∀ (s t : V), M.atom R.added = s → M.atom (M.mate R.added) = t → s ∈ U.atoms → t ∈ U.atoms → s ≠ x →
          t ≠ x → ConnAvoid M ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) s t := by
        intro s t e1 e2 hs ht hsx htx
        have hg := hgood R.added (by rw [e1]; exact hs) (by rw [e2]; exact ht) (by rw [e1]; exact hsx) (by rw [e2]; exact htx)
        exact connAvoid_of_bond R.added e1 e2 hg.1 hg.2
      rcases hyper_added_ends U (R := R) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hc := key _ _ e1 e2 huU hlU (fun e => hxj.1 e.symm) (fun e => hxj.2 e.symm)
        rcases hjab hxj.1 hxj.2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · rw [f1, f2] at hc; exact hc
        · rw [f1, f2] at hc; exact Relation.EqvGen.symm _ _ hc
      · have hc := key _ _ e1 e2 hlU huU (fun e => hxj.2 e.symm) (fun e => hxj.1 e.symm)
        rcases hjab hxj.1 hxj.2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · rw [f1, f2] at hc; exact Relation.EqvGen.symm _ _ hc
        · rw [f1, f2] at hc; exact hc

end host

end WaveTurbulence.FinalCountAsm
