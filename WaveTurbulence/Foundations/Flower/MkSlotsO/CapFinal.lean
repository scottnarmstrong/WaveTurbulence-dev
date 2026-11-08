/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapKind

/-! # B3s-HELPER8 / CAP: the cap kind (SlotObl rev 5)

SlotObl rev 5 asks the HasSum only on `genBoxAt ∩ TopCut` (`MkSlotsO.SlotFam1C`, `slotConcl_of_fam1C`). On the STOP
configuration `IsCapPenFree` (`penTerm`, root of the chain pinned at `s`, chain clock free), `TopCut` at the chain's
root branch gives `s ≤ ts j0` (`topCut_rootPin`), where the general slot kernel is the constant of
`CapN.penFree_const`: one mode (`slotFam1C_of_const`), `capPF_concl`, `capKindAt_pf`, `capKind_pf`. With
`capKind_of_penFree`:

**`capKind : ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsCapSlot K)`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-! ### Geometry -/

/-- A nontrivial cap slot is a cap pair. -/
theorem isCapPair_of_capSide {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain}
    {J : Finset (Fin w)} {q : SourcePair S} (K : CapSide D hS J q) : IsCapPair S hS J q := by
  have h : ((nativeCoupleForest D hS q).root K.c).1.1 = (attachedNode D hS K.cleaf.toNode).1.1 :=
    congrArg (fun z : GNode (D.forest hS) => z.1.1) K.root_c
  have hc : (attachedNode D hS K.cleaf.toNode).1.1 = K.cleaf.1.1 := inflatedPosition_index S D.tree _
  rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) K.c with h0 | h1
  · left
    have e : ((nativeCoupleForest D hS q).root 0).1.1 = (q.firstLeaf hS).1.1 :=
      inflatedPosition_index S D.tree (q.firstLeaf hS).toNode
    rw [← e, ← h0, h, hc]
    exact K.cJ
  · right
    have e : ((nativeCoupleForest D hS q).root 1).1.1 = (q.secondLeaf hS).1.1 :=
      inflatedPosition_index S D.tree (q.secondLeaf hS).toNode
    rw [← e, ← h1, h, hc]
    exact K.cJ

/-- **`TopCut` at the chain's root**: on a root-pinning configuration the chain clock is at least the root pin. -/
theorem topCut_rootPin {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) {q : SourcePair a.prime.skeleton}
    (K : CapSide a.prime.data a.prime.prime.1 J q) (hGeo : CapGeo (recLG a) J p)
    (hroot : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X = true) (hst : s ≤ t)
    (ts : Fin 2 → ℝ) (hts : TopCut a J pat t s (.inl q) ts) :
    rootPinVal (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t ≤ ts K.j0 := by
  set Dq := K.Dq (sourceLayer a) (sourceLayer_isLayering a)
  set r1 := CapP.rootT1 K (sourceLayer a) (sourceLayer_isLayering a)
  have hfix := CapP.capFixPat K (sourceLayer a) (sourceLayer_isLayering a) hGeo pat t s 0 r1
  rw [(pinsRoot_fix hroot s t 0 hst).1 r1 rfl] at hfix
  exact hts (Dq.βc r1) _ rfl hfix

/-! ### One mode on the cut box -/

section Fam

variable (P : WTParams) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (q : SourcePair a.prime.skeleton) (x : Fin P.d → ℤ)

/-- **One cap slot family on the cut box from a constant kernel** (one mode `m = 0`). -/
theorem slotFam1C_of_const (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (θ : ℝ) (V : ℂ)
    (hker : ∀ ts ∈ genBoxAt p a J pat t s (.inl q), TopCut a J pat t s (.inl q) ts →
      genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
        (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = V)
    (μ : ℝ≥0∞) (hμ : ENNReal.ofReal (capKcen P.d) * ‖V‖ₑ ≤ μ) :
    SlotFam1C P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ μ := by
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  set B : Set (Fin 2 → ℝ) := {ts | ts ∈ genBoxAt p a J pat t s (.inl q) ∧ TopCut a J pat t s (.inl q) ts}
  set u : ℂ := if V = 0 then 0 else V / (‖V‖ : ℂ) with hu
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hu]
    split_ifs with hV0
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hV0)]
  have hwu : (‖V‖ : ℂ) * u = V := by
    rw [hu]
    split_ifs with hV0
    · rw [hV0]; simp
    · have : (‖V‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hV0)
      field_simp
  obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
    (Classical.choose_spec (cap_centre P.d)).2 θ B
      (fun ts => genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k₀) k₀
      (fun _ : Unit => ‖V‖) (fun _ => 0) (fun _ => u) (fun _ => norm_nonneg _) Summable.of_finite
      (fun _ => hu1) (fun ts hts => by
        have hs := hasSum_single (f := fun l : Unit => ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts) ()
          (fun b' hb' => absurd (Subsingleton.elim b' ()) hb')
        have hv : ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts =
            genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k₀ := by
          rw [fsPhase_zero', mul_one, hwu, hker ts hts.1 hts.2]
        rw [← hv]
        exact hs)
  refine ⟨Unit, inferInstance, fun _ => capKcen P.d * ‖V‖, fun _ => 0, c, amp, hw0', hws', hamp1, hampS,
    fun _ _ => hampc, fun ts hts hcut n hn _ _ => ?_, ?_⟩
  · rw [hn q rfl hq]
    exact hsum' ts ⟨hts, hcut⟩
  · refine (le_of_eq hmass').trans (le_trans ?_ hμ)
    rw [tsum_eq_single () (fun b' hb' => absurd (Subsingleton.elim b' ()) hb'), maxBracketPow_zero, one_mul,
      ofReal_norm]
    exact le_rfl

end Fam

/-! ### The STOP configuration -/

namespace CapN

section Slot

variable {P : WTParams} (hD3 : ProtBoundAt P) (hD6 : ProtAnnBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
  (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (σ kSel : Fin (2 * R) → Option ℕ) (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
  (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {q : SourcePair a.prime.skeleton}
  (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (K : CapSide a.prime.data a.prime.prime.1 J q)
  (x : Fin P.d → ℤ)


include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hplain hRs hb1 hb hRf1 in
/-- **A cap slot in the configuration `CapPenFree`** (rev 5: HasSum on the `TopCut` box). -/
theorem capPF_concl (hpf : CapK.CapPenFree K (sourceLayer a) (sourceLayer_isLayering a) pat t s) :
    SlotConcl P C capKg (p := p) a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x := by
  have hL1 : 1 ≤ P.L := by linarith
  have hq := isCapPair_of_capSide K
  have hspec := CapK.capPenFree_spec K (sourceLayer a) (sourceLayer_isLayering a) pat t s hpf
  obtain ⟨V, hV, hVk⟩ := penFree_const (hD3 := hD3) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1)
    (hδ := hδ) (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan)
    (hsz := hsz) (hGeo := hGeo) (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel)
    (hplain := hplain) (Rs := Rs) (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf)
    (hRf1 := hRf1) (dag := dag) (hq := hq) (K := K) (hpf := hpf)
  have hker : ∀ ts ∈ genBoxAt p a J pat t s (.inl q), TopCut a J pat t s (.inl q) ts →
      genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
        (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = V := by
    intro ts _ hcut
    refine hVk ts ?_
    have h1 := topCut_rootPin a J pat t s K hGeo hpf.1 hst.le ts hcut
    rw [hspec.1] at h1
    simpa [rootPinVal] using h1
  have hm0 : 0 ≤ genSlotMass P C b a J pat t s kSel Rs (.inl q) :=
    genSlotMass_nonneg P (by linarith) hb1 (by linarith) a J pat t s kSel Rs
      (fun j => lt_of_lt_of_le (by linarith) (hRs j)) (.inl q)
  have hKg0 : 0 ≤ capKg P.d P.η := le_trans zero_le_one (one_le_capKg P.d P.η)
  have hLq : 1 ≤ P.L ^ (47 * (P.d : ℝ) + 2) := Real.one_le_rpow hL1 (by positivity)
  have hηq : ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) ≤
      ENNReal.ofReal (capKg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) *
        genSlotMass P C b a J pat t s kSel Rs (.inl q)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    calc capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)
        = capKg P.d P.η * 1 * genSlotMass P C b a J pat t s kSel Rs (.inl q) := by ring
      _ ≤ _ := by gcongr
  exact slotConcl_of_fam1C P C capKg a J pat t s σ kSel Rs h roots Rf dag b (.inl q) x
    (fun _ => slotFam1C_of_const P a J pat t s σ kSel Rs h roots Rf dag q x hq P.η V hker _ hV)
    (fun _ => slotFam1C_of_const P a J pat t s σ kSel Rs h roots Rf dag q x hq (1 / 4) V hker _ (hV.trans hηq))

end Slot

end CapN

/-! ### The kind -/

/-- **The cap obligation at one parameter record on the STOP configuration.** -/
theorem capKindAt_pf {P : WTParams} (hD3 : ProtBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    GenSlotOnAt IsCapPenFree capKg P := by
  intro C hC R p a J pat t s hp hcan hsz _ hGeo hpat _ ht hs kSel hplain σ Rs hRs _ _ _ roots h b hb1 hb Rf hRf _
    dag _ sl _ hQ x
  obtain ⟨q, rfl, K, hpf⟩ := hQ
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  rw [← hrec] at hcan hGeo hpat
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  exact CapN.capPF_concl (hD3 := hD3) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1)
    (hδ := hδ) (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan)
    (hsz := hsz) (hGeo := hGeo) (hpat := hpat) (hps := hs.1) (hst := hs.2) (htp := ht.2) (σ := σ) (kSel := kSel)
    (hplain := hplain) (Rs := Rs) (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb)
    (Rf := Rf) (hRf1 := hRf1) (dag := dag) (K := K) (x := x) (hpf := hpf)

/-- **The cap kind on the STOP configuration**, on the prefix, from D3. -/
theorem capKind_pf : WTPrefix (GenSlotOnAt IsCapPenFree capKg) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := ProtPin.protBoundGate d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact capKindAt_pf (H4 L hL) hd hη.1 (sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁ hδ.1.le

/-- **The cap kind** (B3s-HELPER8's target for the cap pairs; SlotObl rev 5). -/
theorem capKind : ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsCapSlot K) :=
  capKind_of_penFree capKind_pf

end WaveTurbulence.Flower.MkSlotsO
