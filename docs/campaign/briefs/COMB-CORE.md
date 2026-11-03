# Packet D1 COMB-CORE (pre-freeze) — API for trees, gardens, decorations, layerings, embedded objects

Read `COMMON.md` first. Blueprint packet D1 (rows `T.deftree`, `T.defgarden`, `T.defdec`, `T.deflayer`, `T.subobject`):
the start of the campaign's critical path (D1 → D4 → C1 → …; ~170 graph nodes depend on it).

**Situation.** The carriers are being frozen in Wave B: their audited drafts are in
`/home/scott/wt-scratch/waveb-snap-2/WaveB1-Core.lean` (definitions `TTree`, gardens with marked unpaired leaves,
decorations, ε, Ω, layerings, canonical gardens, truncation; audit reports `docs/campaign/orch/audits/WaveB-stage1.md`,
`WaveB-delta-1.md`). The final freeze (with only minor fixes outside Core) is expected soon. Until then work in
**untracked** files under `/home/scott/wt-scratch/comb-core/` that `import` a local copy of the snapshot Core file
(copy it into your scratch dir; never edit the copy's definitions). After the freeze the orchestrator tells you, and you
move your files into `WaveTurbulence/Foundations/Comb/**` (namespace `WaveTurbulence.Comb`) importing the frozen
definitions instead — so keep proofs robust to the move (no reliance on scratch-only names).
Worktree for builds: `/home/scott/WaveTurbulence-worktrees/resonant` (run `lake env lean <scratch file>` from there).

Goals (sorry-free lemmas about the draft definitions; do not end your turn at milestones):
1. Trees: order n, number of leaves = 2n+1, node signs (children of a node of sign ζ have signs (ζ,−ζ,ζ)), ζ(𝒯) =
   ∏(iζ_𝔫), conjugation; finiteness/decidability instances; induction principles convenient for later proofs.
2. Gardens/couples: signature constraints (equal numbers of + and −), the pairing is a fixed-point-free sign-reversing
   involution on (non-marked) leaves, order additivity, components and irreducibility (decidable; components partition
   the trees), multi-couples, conjugates, paired trees (exactly one lone leaf).
3. Decorations: a decoration is determined by its leaf values (and root values); the sum rule ζ_a κ_a = Σ_{ℓ below a}
   ζ_ℓ κ_ℓ; Ω_𝔫 = 2⟨k_{𝔫1} − k_𝔫, k_𝔫 − k_{𝔫3}⟩; ε support (defset); translation invariance; finiteness of decorations with
   leaf values in a bounded set.
4. Layerings: monotonicity along paths, layers of paired leaves, restriction to subtrees.
5. Embedded objects (T L845–L847): sub-couples, sub-paired-trees, replace and collapse operations, with their basic
   order/leaf-count identities.
Done: `READY comb-core`.
