# Statement audit: wt-wke's MAINCOEF-T (DH21 Prop 5.1 for regular trees)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 33b). Findings only; nothing was edited.

**Scope.** `Foundations/ClassJR/HANDOFF-MAINCOEFT.md` and the `MCT*` modules, landed on main in `b5d716f`. I
compared them against DH21 Prop 5.1 (`maincoef`, L936–L944), DH21 Prop 6.10 (L1700–L1712) and DH23's weights
(L955–L969, and L929 for trees).

## Verdict

**PASS.**
- **The exponents and constant are the couple statement's.** `RegChain.maincoefT_DH23` is DH21 Prop 5.1 for a
  regular tree code. It has exactly the DH23 exponents and the `C^{2n+1}`-type constant of the landed couple statement
  `RegCpl.maincoef_DH23`.
- **Only the identity domain differs:** it is `0 ≤ s < t ≤ 1` instead of `[0,1]²`. That is DH21's "for `t > s`" and
  DH23 L929's "For `0 ≤ s < t ≤ 1`".
- **The object is DH21's `Ã_𝒯`.** It is defined by the chain recursion with the lone-leaf condition. Its identity
  with the garden-defined `𝒜*_𝒯` was audited in `BTILDE.md`.
- **Axioms:** standard.

## 1. Inputs

- **Main hashes** (equal to the handoff's): `MCProp51T` `d248b0f0…`, `MCTExp` `21e3a00b…`, `MCTMain` `8a63cb22…`.
- **Probe.** It ran in dev's build, whose `MCProp51T.olean` was built at landing.

## 2. The statement

```lean
theorem RegChain.maincoefT_DH23 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : A1 ≤ A) (X : RegChain)
    (hX : X.wf = true) (ζ : ℤˣ) (x : Addr) :
    MCExpT (1 - η / 8) (η / 4) (1 - η / 2) A (CTη η ^ (2 * X.size + 1)) nodeSgn
      (chosenSet (X.linksAt ζ x)) (X.At ζ x)
```

**The expansion: `MCExpT` against `MCExp`.**
- The two definitions are identical except for the identity domain:
  - `MCExpT`: `∀ α t s, 0 ≤ s → s < t → t ≤ 1 → F = Σ_{Z⊆S} ∏_{z∈Z} PhiZ ζ z (α z) · G_Z`;
  - `MCExp`: the same on `t, s ∈ [0,1]`.
- In both, the components are full `MCRep θ a b A N (S∖Z) (G Z)`: Fourier representations on `[0,1]²` with the
  (maincoef2)/(maincoef2.5) bounds.
- My probe proves `MCExp → MCExpT` in two lines. So `MCExpT` asks only what DH21 6.10 asserts for trees.

**The weights.** The DH23 instance `(θ, a, b) = (1 − η/8, η/4, 1 − η/2)` is the couple statement's, and the DH23
(maincoef2)/(maincoef2.5) exponents: `⟨max λ⟩^{1−η/8}` in the Gevrey bound, `⟨max λ⟩^{η/4}·max⟨α⟩^{1−η/2}` in the
weighted bound.
- DH21's tree weights `(⟨λ₁⟩+⟨λ₂⟩)^{1/4}` are `⟨max⟩` weights up to constants, so the shape is the couple shape.
- Inherited from the JR-OPS deviations: `wL` reads `⟨max⟩` as `(1+|λ₁|+|λ₂|)`, and the Gevrey bound carries
  `A^{|ρ|}`. These are the same as for couples (`JR-OPS.md`).

**The variables, signs and terms.**
- The variables are `chosenSet (X.linksAt ζ x)`: the chosen nodes `𝒩^ch` of the tree's links.
- The signs are `nodeSgn`, for the `Φ = χ_∞/(ζπiα)` factors of (maincoef1).
- There are at most `2^{|𝒩^ch|}` terms, one per `Z`.

**The object.**
- `RegChain.At X ζ x α t s := chainT … α t (fun t' => if s < t' then 1 else 0)`: the (newexp2) chain integral with
  continuation `1{t' > s}`.
- That continuation is DH21 (varat)'s domain `𝒟 = {t_{(ℓ_*)^p} > s; 0 < t_𝔫' < t_𝔫 < t}` (L1700), which is DH23's
  `𝒟*` (defdomaind*).
- `chainAtilde X ζ = (toJRc X).At ζ (rootT ζ)` holds by `rfl`. `treeAstar_eq_Atilde_G` (audited in `BTILDE.md`)
  identifies it with the garden's `𝒜*_𝒯` under the link relation, for `s < t`.

**Hypotheses.** `0 < η ≤ 2` and `A ≥ A1`, as for couples. The pair exponents `θ' = 1 − η/16`, `a' = 5η/16` and
`δ = η/16` are internal: J3's couple expansion holds for every `θ' < 1`.

## 3. Checks (mine)

- **Probe** (dev's build). `#check` of both DH23 statements; `#print` of `MCExpT`, `MCExp` and `RegChain.At`; the
  `MCExp → MCExpT` example compiles.
- **Axioms** of `RegChain.maincoefT_DH23` and `RegChain.maincoefT`: [propext, Classical.choice, Quot.sound].

## 4. Notes (no findings)

- **The garden form** (`maincoefT_garden_DH23`, scratch `btilde/src/BTilde/MaincoefT.lean`) takes
  `existsUnique_regChain_decodesTree`, which is now a frozen B2 anchor (CL-22) with a seal provider. Consumers can
  apply the anchor directly.
- **Variable addresses.** The tree is placed at `rootT ζ` among ClassJR couple addresses. B2's `X.treeLinks ζ` are
  related by `linksAt_rootT` (scratch), as the handoff says. A consumer stated on B2's tree links needs that bridge.
