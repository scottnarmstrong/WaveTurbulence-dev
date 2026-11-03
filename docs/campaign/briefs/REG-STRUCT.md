# Packets D4 REG-DEFS + C1 REG-STRUCT (pre-freeze) — regular couples: chains, structure theorem, counting

Read `COMMON.md` first. Critical path (D1 → D4 → C1 → C2 → J…). Blueprint rows `T.defreg`, `T.defregchain`,
`DH21.legalpair`, `DH21.prop34`, `DH21.structure1`, `DH21.structure15`, `GAP.structUniq`, `DH21.countcouple1`,
`T.propstructure`.

The regular-couple definitions are drafted (tier B2 stage 1, audited APPROVED by wt-orch:
`docs/campaign/orch/audits/WaveB2-stage1.md`) in `/home/scott/wt-scratch/waveb2/WaveB2-Regular.lean` (mini-couples,
mini-trees with codes, operations A/B, regular couples/trees, `RegCode` with an injective decoding, links, 𝒩^ch,
dominant objects) on top of the B1 core carriers. They are not frozen yet (B2.1/B2.2 freeze after this packet and C2/C5
validate them). Work in untracked scratch `/home/scott/wt-scratch/reg-struct/` against local copies of
`/home/scott/wt-scratch/waveb-snap-4/` (B1) and `/home/scott/wt-scratch/waveb2-snap-1/` (B2 stage 1; wt-orch's snapshot)
and your COMB-CORE API. Report any defect you find in the B2 definitions (do not change them).

Goals (do not end your turn at milestones):
1. **D4:** legal (non-crossing) pair partitions, regular chains, dominant chains (TARGET L848–L850; DH21 Defs 4.4, 4.6);
   DH21 Prop 4.5 (`legalpair`, L741–L749) and Prop 4.7 (`prop34`, L752–L761).
2. **C1:** DH21 Prop 4.8 (`structure1`, L762–L790), Prop 4.10 (`structure15`), the uniqueness of all structure data
   (`GAP.structUniq`, F12 — the source's "case-by-case argument", DH21 L833, is not written: write it), Cor 4.9 counting
   (#regular couples of order 2m ≤ C₀^m; DH21 map E7: the correct identity is the Catalan convolution), and TARGET
   Prop 4.4 (`propstructure`, L851–L869) for couples and trees.
3. Validate the B2 `RegCode` decoding against these theorems (range = regular couples; injective).
Done: `READY reg-struct`.
