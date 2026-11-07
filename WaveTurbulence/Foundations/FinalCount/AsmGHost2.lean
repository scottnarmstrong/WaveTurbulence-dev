/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGHost
/-! **FINALCOUNT-ASSEMBLY: `HostConnF` and `HostConn` discharged** (generic molecule, one decoration).

* `hostConnF_of`: a non-first-stage collected piece `p` (all ordinary members of `C₁` are first-stage): if `p` is hyper, its retained
  designated bond joins its joints and is killed by no piece; if `p` is ordinary, it is a member of `C₂` and `ordinary_host_conn`
  applies with `p` among the removed pieces.
* `hostConn_of`: a collected object `U = {a, x, b}` all of whose bonds at `x` go to `a`, `b` is a member of `C₂` (members of `C₁`
  never have three atoms); ordinary `U`: `x` is its interior atom (a joint has internal degree `2 < 3 ≤ deg x`) and
  `ordinary_host_conn` applies with `U` removed; hyper `U`: the designated bond, or, if `x` is a joint (then `deg x = 3`), a bond from
  the interior atom to the other joint (four bonds at the interior atom cannot all go to `x`). -/
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

theorem connAvoid_mono {M : Molecule V D} {Kd Kd' : Set D} (h : Kd' ⊆ Kd) {a b : V} (hc : ConnAvoid M Kd a b) :
    ConnAvoid M Kd' a b := by
  induction hc with
  | rel s t hst =>
    obtain ⟨z, h1, h2, h3, h4⟩ := hst
    exact Relation.EqvGen.rel _ _ ⟨z, h1, h2, fun hz => h3 (h hz), fun hz => h4 (h hz)⟩
  | refl s => exact Relation.EqvGen.refl _
  | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- A bond between `a` and `b`, neither of whose darts is in `Kd`, joins them. -/
theorem connAvoid_of_bond {M : Molecule V D} {Kd : Set D} {a b : V} (z : D) (hz : M.atom z = a)
    (hmz : M.atom (M.mate z) = b) (h1 : z ∉ Kd) (h2 : M.mate z ∉ Kd) : ConnAvoid M Kd a b :=
  Relation.EqvGen.rel _ _ ⟨z, hz, hmz, h1, h2⟩

/-- Darts at atoms outside all pieces are killed by none of them. -/
theorem not_mem_killS_of_atom {M : Molecule V D} {ps : List (Object M × Quad D)} {z : D}
    (h : ∀ p ∈ ps, M.atom z ∉ p.1.atoms) : z ∉ KillS ps := by
  rintro ⟨p, hp, hk⟩
  exact h p hp hk.1

/-- The designated bond of a hyper object is not among its `ContainsDart` darts. -/
theorem hyper_added_not_cd {M : Molecule V D} (O : Object M) {R : SourceVine.HyperLikeRealization M O.atoms O.upper O.lower}
    (hR : O.shape = .hyper R) : ¬ O.ContainsDart R.added ∧ ¬ O.ContainsDart (M.mate R.added) := by
  unfold Object.ContainsDart
  rw [hR]
  exact ⟨fun h => h.1 rfl, fun h => h.2.1 rfl⟩

/-- The designated bond of a hyper piece is not killed by the piece. -/
theorem hyper_added_not_killed {M : Molecule V D} {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Object M)} {L γ η : ℝ}
    {w : Mom d} {κ : D → (Fin d → ℤ)} {p : Object M × Quad D} (hp : PieceData C Un L γ η w κ p)
    {R : SourceVine.HyperLikeRealization M p.1.atoms p.1.upper p.1.lower} (hR : p.1.shape = .hyper R) {z : D}
    (hz : z = R.added ∨ z = M.mate R.added) (hj : M.atom z = p.1.upper ∨ M.atom z = p.1.lower) : z ∉ PieceKill p.1 p.2 := by
  rintro ⟨-, himp⟩
  obtain ⟨-, hCD, -, -⟩ := hp
  have hN := himp hj
  have hn := hyper_added_not_cd p.1 hR
  rcases hz with rfl | rfl
  · rcases hN with e | e | e | e
    · exact hn.1 (e ▸ hCD.1)
    · exact hn.1 (e ▸ hCD.2.1)
    · exact hn.1 (e ▸ hCD.2.2.1)
    · exact hn.1 (e ▸ hCD.2.2.2)
  · rcases hN with e | e | e | e
    · exact hn.2 (e ▸ hCD.1)
    · exact hn.2 (e ▸ hCD.2.1)
    · exact hn.2 (e ▸ hCD.2.2.1)
    · exact hn.2 (e ▸ hCD.2.2.2)

/-- The ends of the designated bond of a hyper object are its joints. -/
theorem hyper_added_ends {M : Molecule V D} (O : Object M) {R : SourceVine.HyperLikeRealization M O.atoms O.upper O.lower} :
    (M.atom R.added = O.upper ∧ M.atom (M.mate R.added) = O.lower) ∨
      (M.atom R.added = O.lower ∧ M.atom (M.mate R.added) = O.upper) := by
  have h := R.ends_eq
  unfold Molecule.ends at h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- `degIn = deg` when every dart at the atom stays in the group. -/
theorem degIn_eq_deg_of_all {M : Molecule V D} {S : Finset V} {v : V} (h : ∀ z, M.atom z = v → M.InGroup S z) : M.degIn S v = M.deg v := by
  unfold Molecule.degIn Molecule.deg
  congr 1
  apply Finset.filter_true_of_mem
  intro z hz
  exact h z ((Finset.mem_filter.1 hz).2)

/-- In a three-atom hyper object with a joint `j` of degree at most `3`, the interior atom has a bond to the other joint `j'`. -/
theorem hyper_interior_bond_other {M : Molecule V D} (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) (U : Object M)
    {j m j' : V} (hat : U.atoms = {j, m, j'}) (hm : U.IsInterior m) (hdj : M.deg j ≤ 3) :
    ∃ z, M.atom z = m ∧ M.atom (M.mate z) = j' := by
  by_contra hcon
  push Not at hcon
  have h4 : M.degIn U.atoms m = 4 := Subpro.degIn_interior_object U hm
  unfold Molecule.degIn at h4
  set T := (M.dartsAt m).filter (fun z => M.InGroup U.atoms z) with hT
  have hmap : ∀ z ∈ T, M.mate z ∈ M.dartsAt j := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
    have hzm : M.atom z = m := (Finset.mem_filter.1 hz1).2
    have hmem := hz2.2
    rw [hat] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rcases hmem with e | e | e
    · exact e
    · exact absurd (hzm.trans e.symm) (hnl z)
    · exact absurd e (hcon z hzm)
  have hinj : Set.InjOn M.mate T := fun a _ b _ h => by
    have := congrArg M.mate h; simpa [M.mate_mate] using this
  have := Finset.card_le_card_of_injOn M.mate hmap hinj
  have hdeg : (M.dartsAt j).card = M.deg j := rfl
  omega

section host
variable {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c0 : V → Mom d}
  (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
  {C : CollData M} {Un : (D → (Fin d → ℤ)) → Set (Object M)}
  (hd22 : ∀ O ∈ C.C2Of L γ η w κ (Un κ), ∀ O' ∈ C.C2Of L γ η w κ (Un κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
  (hsh : ∀ O ∈ C.C2Of L γ η w κ (Un κ), (∃ h, O.shape = .vc h) →
    DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨ M.IsVine .V O.atoms O.upper O.lower)
  (hUO : C.UnselOK L γ η w κ (Un κ))
include hM hκ hc0 hd22 hsh hUO

/-- **`HostConnF`, one decoration.** -/
theorem hostConnF_of (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) {Fst : Set (Object M)}
    (hFst : ∀ i, (∃ h, (C.collection i).shape = .vc h) → C.collection i ∈ Fst)
    (ps : List (Object M × Quad D)) (p : Object M × Quad D) (hps : ∀ q ∈ ps, PieceData C Un L γ η w κ q)
    (hp : PieceData C Un L γ η w κ p) (hpF : p.1 ∉ Fst) (hpw : (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)) :
    ConnAvoid M (KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower := by
  rcases object_shape_cases p.1 with hvc | ⟨R, hR⟩
  · have hU : p.1 ∈ C.C2Can L γ η w κ (Un κ) := by
      rcases hp.1 with ⟨i, hi⟩ | hc
      · exact absurd (hi ▸ hFst i (hi ▸ hvc)) hpF
      · exact hc
    have hq : ∀ q ∈ p :: ps, PieceData C Un L γ η w κ q := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hps q hq
    have h := ordinary_host_conn hM hκ hc0 hd22 hsh hUO hnl hU hvc (p :: ps) hq hpw false (by simp)
    refine connAvoid_mono ?_ h
    rintro z (⟨q, hq, hk⟩ | hk)
    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hk⟩
    · exact Or.inl ⟨p, List.mem_cons_self, hk⟩
  · have hdis : ∀ q ∈ ps, Disjoint p.1.atoms q.1.atoms := (List.pairwise_cons.1 hpw).1
    have hnotq : ∀ z, (M.atom z = p.1.upper ∨ M.atom z = p.1.lower) → ∀ q ∈ ps, M.atom z ∉ q.1.atoms := by
      intro z hz q hq hzq
      have hzp : M.atom z ∈ p.1.atoms := by
        rcases hz with e | e <;> rw [e]
        · exact object_mem_of_joint p.1 (Or.inl rfl)
        · exact object_mem_of_joint p.1 (Or.inr rfl)
      exact Finset.disjoint_left.1 (hdis q hq) hzp hzq
    have hgood : ∀ z, (z = R.added ∨ z = M.mate R.added) → (M.atom z = p.1.upper ∨ M.atom z = p.1.lower) →
        z ∉ KillS ps ∪ PieceKill p.1 p.2 := by
      rintro z hz hj (h | h)
      · exact not_mem_killS_of_atom (hnotq z hj) h
      · exact hyper_added_not_killed hp hR hz hj h
    rcases hyper_added_ends p.1 (R := R) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact connAvoid_of_bond R.added e1 e2 (hgood _ (Or.inl rfl) (Or.inl e1)) (hgood _ (Or.inr rfl) (Or.inr e2))
    · exact Relation.EqvGen.symm _ _ (connAvoid_of_bond R.added e1 e2 (hgood _ (Or.inl rfl) (Or.inr e1))
        (hgood _ (Or.inr rfl) (Or.inl e2)))

/-- **`HostConn`, one decoration.** -/
theorem hostConn_of (hnl : ∀ z, M.atom z ≠ M.atom (M.mate z)) (h3 : ∀ v ∈ M.atoms, 3 ≤ M.deg v)
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
  rcases object_shape_cases U with hvc | ⟨R, hR⟩
  · -- ordinary: `x` is interior
    have hB := object_vc_block U hvc
    have hx1 : x ≠ U.upper := by
      intro e; have := (Mole.block_joint_degrees M hB).1; rw [← e, hdegx] at this; have := h3 x hxM; omega
    have hx2 : x ≠ U.lower := by
      intro e; have := (Mole.block_joint_degrees M hB).2; rw [← e, hdegx] at this; have := h3 x hxM; omega
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
  · have hdj : M.degIn U.atoms U.upper = 3 := object_hyper_degIn U ⟨R, hR⟩ (Or.inl rfl)
    have hdj' : M.degIn U.atoms U.lower = 3 := object_hyper_degIn U ⟨R, hR⟩ (Or.inr rfl)
    have hgood : ∀ z, M.atom z ∈ U.atoms → M.atom (M.mate z) ∈ U.atoms → M.atom z ≠ x → M.atom (M.mate z) ≠ x →
        z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) ∧
          M.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M.atom z = x}) := by
      intro z h1 h2 h3' h4
      refine ⟨fun hk => hk.elim (hfree z h1) h3', fun hk => hk.elim (hfree _ h2) h4⟩
    by_cases hxj : x = U.upper ∨ x = U.lower
    · -- `x` is a joint: a bond from the interior atom to the other joint
      have hdx : M.deg x ≤ 3 := by
        rcases hxj with e | e
        · rw [← hdegx, e, hdj]
        · rw [← hdegx, e, hdj']
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
      have key : ∀ (s t : V), M.atom R.added = s → M.atom (M.mate R.added) = t → s ∈ U.atoms → t ∈ U.atoms → s ≠ x →
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
