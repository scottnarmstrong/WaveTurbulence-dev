/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.CodeTrees

/-!
# The B̃ bridge: the garden-defined `B̃_Q` is the code-defined one

DH21 (defcoefb2), (deftildeb) (L919–L923; DH23 L951–L956) define, for a couple `Q`,
`B_Q(t, s, α[𝒩]) = ∫_ℰ ∏_𝔫 e^{ζ_𝔫πiα_𝔫t_𝔫} dt` (`cplB`, over the domain ℰ `cplDom` of the Wave B
garden), and `B̃_Q(t, s, α[𝒩^ch]) = B_Q(t, s, α[𝒩])` when `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` on every link.
Here, for every couple carrier `G` decoded by a B2 code `Q`:

* `cplB_eq_Btilde`: `B_Q(t, s, α) = (toJR Q).Btilde α t s` for `t, s ≥ 0` and `α` satisfying the
  link relation, where `ClassJR.RegCpl.Btilde` is the code-defined `B̃` of DH21 Prop 5.1;
* `maincoef_garden`: DH21 Prop 5.1 for regular couples through gardens: every regular couple has a
  unique well-formed code, its garden `B_Q` is the code-defined `B̃_Q`, and `B̃_Q` has the expansion
  (maincoef1)–(maincoef3). The hypothesis `hstruct` is the named obligation
  `existsUnique_regCpl_decodes` (REG-STRUCT, `B2CharacterizationProofs.lean`, sha256 `f2817fe8…`),
  stated verbatim.

The link relation is stated on ClassJR's copy of the links, `(toJR Q).links`, so that this module
needs only sections 1–3 of the B2 draft; `BridgeB2` restates it with B2's `Q.links`.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

/-! ### The translation keeps well-formedness and size -/

theorem isType2_toJR (Q : RegCpl) : (toJR Q).isType2 = Q.isType2 := by
  cases Q <;> rfl

theorem isNil_toJRc (X : RegChain) : (toJRc X).isNil = X.isNil := by
  cases X <;> rfl

mutual
theorem wf_toJR : ∀ Q : RegCpl, (toJR Q).wf = Q.wf
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [toJR, ClassJR.RegCpl.wf, RegCpl.wf, wf_toJR Q₁, wf_toJR Q₂, wf_toJR Q₃]
  | .type2 Xp Xm Qlp => by
    simp only [toJR, ClassJR.RegCpl.wf, RegCpl.wf, wf_toJRc Xp, wf_toJRc Xm, wf_toJR Qlp,
      isType2_toJR, isNil_toJRc]

theorem wf_toJRc : ∀ X : RegChain, (toJRc X).wf = X.wf
  | .nil => rfl
  | .pair _ Qr Qg inner rest => by
    simp only [toJRc, ClassJR.RegChain.wf, RegChain.wf, wf_toJR Qr, wf_toJR Qg, wf_toJRc inner,
      wf_toJRc rest]
end

mutual
theorem size_toJR : ∀ Q : RegCpl, (toJR Q).size = Q.size
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [toJR, ClassJR.RegCpl.size, RegCpl.size, size_toJR Q₁, size_toJR Q₂, size_toJR Q₃]
  | .type2 Xp Xm Qlp => by
    simp only [toJR, ClassJR.RegCpl.size, RegCpl.size, size_toJRc Xp, size_toJRc Xm, size_toJR Qlp]

theorem size_toJRc : ∀ X : RegChain, (toJRc X).size = X.size
  | .nil => rfl
  | .pair _ Qr Qg inner rest => by
    simp only [toJRc, ClassJR.RegChain.size, RegChain.size, size_toJR Qr, size_toJR Qg,
      size_toJRc inner, size_toJRc rest]
end

/-! ### Node signs of a couple -/

/-- The node signs of a couple carrier (`G.sig = ![1, -1]`) are ClassJR's. -/
theorem nodeSign_couple_eq (v : ClassJR.Addr) :
    ((nodeSign ![1, -1] v : ℤˣ) : ℤ) = ClassJR.nodeSgn v := by
  rcases v with ⟨j, p⟩
  simp only [nodeSign, TTree.pathSign, ClassJR.nodeSgn, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
  fin_cases j <;> simp

theorem nodeSgn_root_plus : ClassJR.nodeSgn ((0 : Fin 2), ([] : TTree.Path)) = 1 := by
  simp [ClassJR.nodeSgn]

theorem nodeSgn_root_minus : ClassJR.nodeSgn ((1 : Fin 2), ([] : TTree.Path)) = -1 := by
  simp [ClassJR.nodeSgn]

theorem treeBeta_eq_betaAt {G : Garden 2} (hG : G.sig = ![1, -1]) (α : ClassJR.Addr → ℝ)
    (j : Fin 2) : treeBeta G α j = betaAt α (j, []) := by
  funext p
  simp only [treeBeta, betaAt, ClassJR.addrExt, List.nil_append, hG, nodeSign_couple_eq]

/-! ### The bridge -/

/-- **The garden-defined `B̃_Q` is the code-defined one** (DH21 (defcoefb2), (deftildeb)): for a
couple carrier `G` decoded by `Q` and phases `α` with `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` on every link,
`B_Q(t, s, α[𝒩]) = B̃_Q(t, s, α[𝒩^ch])` for `t, s ≥ 0`. -/
theorem cplB_eq_Btilde {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) {α : ClassJR.Addr → ℝ}
    (hα : ∀ l ∈ (toJR Q).links, LinkRel α l) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cplB G t s α = (toJR Q).Btilde α t s := by
  obtain ⟨⟨-, hsig⟩, h0, h1, -⟩ := hQ
  rw [cplB_eq G ht hs, treeBeta_eq_betaAt hsig, treeBeta_eq_betaAt hsig, h0, h1]
  exact treesProp α Q _ _ nodeSgn_root_plus nodeSgn_root_minus hα t s

/-! ### The kernel form (Wave B's `kDomain`, `phaseIntegral`) -/

/-- **Wave B's phase integral of a decoded couple is `B̃_Q`**: for a layered couple in layer `0`
decoded by `Q`, `t, s ∈ [0, 1]`, and frequencies `α = δL^{2γ}Ω` satisfying the link relation,
`∫_{kDomain} ∏ e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫} dt = B̃_Q(t, s, δL^{2γ}Ω)`. -/
theorem phaseIntegral_kDomain_eq_Btilde {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (h0 : ∀ a, LG.layer a = 0) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (k : GNode LG.garden.tree → Mom d)
    (hα : ∀ l ∈ (toJR Q).links, LinkRel (alphaOmega L γ δ LG.garden k) l)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) (s₁ s₂ : ℝ) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun b => if b.1.1 = 0 then t else s) s₁) s₂ k =
      (toJR Q).Btilde (alphaOmega L γ δ LG.garden k) t s := by
  have hplain : LG.garden.IsPlain := hQ.1.1
  rw [kDomain_eq_cplDom LG h0 hplain ht.2 hs.2, phaseIntegral_cplDom_eq L γ δ hplain t s s₂ k,
    cplB_eq_Btilde hQ hα ht.1 hs.1]

end WaveTurbulence.MainCoef
