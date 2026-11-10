# Research notes and evidence

> **What these files are.** Every file in this directory was written by an AI session (see "How this was made" in
> the [README](../../README.md#how-this-was-made)). They are of two kinds.
>
> - **Working logs and handoffs of AI agent sessions**: reports a session wrote at the end of its work for the
>   coordinating agent, full of internal names, paths and tool remarks. These are the `*-handoff.md` files
>   (`finalcount-prop94-handoff.md`, `finalcount-prop96-handoff.md`, `finalcount-stage2-handoff.md`,
>   `finalsbest1-ladder-coupling-handoff.md`, `flower-cut2-faces-handoff.md`, `flower-skeleton-handoff.md`,
>   `ladderl1-handoff.md`, `layervine-count-handoff.md`, `lftwist-class-count-handoff.md`, `low-degree-cuts-handoff.md`,
>   `redvine-lower-clock-handoff.md`, `vineest-early-handoff.md`, `vineest-handoff.md`,
>   `vineest-step3-epsilon-handoff.md`), and also `flower-skeleton-obstruction.md` (a stop report),
>   `internal-weights-notes.md` (a route decision), `dh21-lemma73-sign-trace.md` (a trace),
>   `dh23-appendix-b-errata.md` and `dh23-prop102-proof-errata.md` (a session's list of source slips),
>   `target-vine-core-sign-check.md` (a check record), `flowerest1/STATUS.md` (a tracker) and `closure-audit/` (an
>   audit's working report). The errata cite some of them as the record of a specific finding.
> - **Research notes and referee reports**, the evidence the errata cite: the `gamma-le-half-*` notes and referee
>   reports; `dh23-prop96-case4.md` with its scripts and `dh23-prop96-referee.txt`; `case4-gamma-above-half.txt` and
>   its referee report; `kqmainest1-necklace.txt`, `ylem1-investigation.md`, `vine2-m1.txt`, `ghost-triangle-notes.txt`,
>   `remtame-case-i-notes.txt`, `remtame-hinge-notes.txt` with `remtame-hinge-referee/`, `erratum-remtame.md`,
>   `twist-profiles-notes.md` and its referee report, `git20-general-d.md`; for the flower estimate,
>   `flower-design-notes.md` and its referee report, `flower-cutoff-notes.md`, `flower-cut2-notes.md`,
>   `flower-cut2-fiber.md` and its referee report, `flower-cut2-review.md`, and in `flowerest1/` the supplements, the
>   resolution notes (`o…-RESOLUTION.md`, `uclock-RESOLUTION.md`) and the `REFEREE*.md` reports; the independent
>   assessment `astra-flowerest1-report.md`; and the seal audit `seal-layergarden_v2-audit.md`. The notes are working
>   documents too and use the same internal names; the γ ≤ 1/2 notes were edited for readers (below).

This directory holds the notes, referee reports and small scripts that support the entries of
[`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md). They are working documents of the project, copied
verbatim: they use the project's internal names (packets, rulings, scratch paths) and may refer to files that are not
included. The errata file is the reader-facing summary; these files are the evidence behind it. Lean names in these files
refer to the repository at the time of writing; a later clean-up removed some unused helpers, which remain in the git
history at the commits cited.

Absolute local paths in these records were replaced in November 2026 by placeholders: `<scratch>/` (the project's
private working directory), `<repo>/` (a checkout of this repository), `<worktrees>/` (development checkouts),
`<sources>/` (a local copy of the papers' LaTeX sources and maps) and `<tools>/` (private tooling); none of these is
part of the repository. Internal working records they cite (planning and audit records, working notes kept beside the Lean files, and the
agents' instructions) were removed from the repository at publication; those that were on the main branch
remain in its git history.

No Lean code from the project's working directories is copied here. Lean checks that exist only there are marked
"(working note, not included)" in the errata file.

## Copied for the errata list (2026-11-07)

Source paths are relative to the project's private working directory (`<scratch>/`, not included). Each copy is
byte-identical to its source at copy time (sha256 below), except for three edits made in November 2026: the
placeholders for absolute local paths described above; one line of `gamma-le-half-repair-1-notes.md` (the heading of
"What to ask Deng and Hani"), re-worded because it referred to a file that is no longer in the repository; and, in
`dh23-prop96-case4-scripts/cuts.py` and `vinefree.py`, the helper modules are now found in the scripts' own directory
instead of a local path. One copy was renamed: `vineest-early-handoff.md` (first copied under a longer name).

| File | Source | sha256 | Entry |
|---|---|---|---|
| `gamma-le-half-repair-1-notes.md` | `research-gamma-half/NOTES.md` | `e7e876e5393b44448d801c2cdcd2cc285428b04e33a23e20bb5ef50be76405a2` | E1 |
| `gamma-le-half-repair-1-referee.md` | `research-gamma-half-referee/REPORT.md` | `70af76c42cee58d71df5546c9b4b189d04b8489f5d9eb02745d9ee9e029bcfcf` | E1 |
| `gamma-le-half-repair-2-notes.md` | `research-gamma-half-2/NOTES.md` | `ac936aed79e2df39b36a87ab4102ad298e25997024710d02b246d1b1b511e7cc` | E1 |
| `gamma-le-half-repair-2-referee.md` | `research-gamma-half-referee-2/REPORT.md` | `8e7ec6f50c8c48db7567bfe302380e85b3b09d0566658a32b4b2240adc9ded8b` | E1 |
| `gamma-le-half-repair-3-notes.txt` | `research-gamma-half-3/NOTES.txt` | `92a9909ade0c346ac4a54d893a45a674c65e78f8a67a6d814a9161ecd3775967` | E1 |
| `gamma-le-half-repair-3-referee.md` | `research-gamma-half-referee-3/REPORT.md` | `302b2276faae62e0dd6c21d38e876f16317e46addb63101e7dce2c1645412b82` | E1 |
| `dh23-prop96-case4-scripts/necklace.py` | `prop96-case4/necklace.py` | `f70f5bf9341038f73d566e89f3b76e8d572b5ab56edd58389763d85c14de42c4` | E1 |
| `dh23-prop96-case4-scripts/vinefree.py` | `prop96-case4/vinefree.py` | `c00d4ee7a092921a00ec4d621d824e391ae0a9312668939f252106f656c5cddd` | E1 |
| `dh23-prop96-case4-scripts/cuts.py` | `prop96-case4/cuts.py` | `db92d8b970ee1ef92541edca0a06337af296473f595fd9868a83ffb22ce2e4e7` | E1 |
| `dh23-prop96-case4-scripts/count_check.py` | `prop96-case4/count_check.py` | `f375c31d735b7a11a3e5950e52d95e9e8f4f2a00b735d5a31ce70a99c5bbbe28` | E1 |
| `dh23-prop96-case4-scripts/graphs.py` | `prop96-case4/graphs.py` | `477231d0ffac86ce9d220431e0fe76b9f82734b7027c4b374d21461173e113b8` | E1 (helper imported by `vinefree.py`) |
| `dh23-prop96-case4-scripts/out_necklace.txt` | `prop96-case4/out_necklace.txt` | `2f7330dfa9c897b98cd182743e263a8755e7eebd94b35dc375b46bf64666e671` | E1 |
| `dh23-prop96-case4-scripts/out_vinefree.txt` | `prop96-case4/out_vinefree.txt` | `efc2b2d4afb283d880f2f4f59637fc87ef98a2addea83515e65c5422970b6552` | E1 |
| `dh23-prop96-case4-scripts/out_cuts.txt` | `prop96-case4/out_cuts.txt` | `b696f0542769ad521c13e143667099c7161ac6809bdb26194093badb8af4cd19` | E1 |
| `dh23-prop96-case4-scripts/out_count_check.txt` | `prop96-case4/out_count_check.txt` | `d1c7b0224623334f4a25e527f58799b942b946b1b425c021a6bfad7c7e1797b5` | E1 |
| `dh21-lemma73-sign-trace.md` | `wke/F61-sign-trace.md` | `edd8025b0672f043fec3c7d036b2af737ea5e3096070e83982bc36ca08a3ffba` | E2a |
| `dh23-prop102-proof-errata.md` | `appb/ALG-ERRATA.md` | `b612e198bc07a1d2fc126a4c5571ba26f66f9064378aa52e34e12fa52ced6e32` | E2c; minor items m37, m38 |
| `target-vine-core-sign-check.md` | `vineparam-contract/F79-KERNEL-CHECK.md` | `77ffa382811146b60fa68fa1ff2efc4940768f8e29860825f30897a4fb0683ff` | E2d |
| `dh23-appendix-b-errata.md` | `appb/ERRATA.md` | `e01dadd9f124717481917a2f18aca0a21d569e3235146b575c66d822ff3ccf15` | minor item m42 |
| `layervine-count-handoff.md` | `layercnt/HANDOFF.md` | `cff6dff63a522a37e4a8f15e045929d4182837b38564e52a3ebc383c75b78782` | minor item m16 |
| `ladderl1-handoff.md` | `ladder/HANDOFF.md` | `98e84be1906fada3bc235d3c9ddae4ec122ed85b36bc95e558c607c7da41f6c8` | minor items m24, m25 |
| `vineest-early-handoff.md` | `vineest-s3/validation/HANDOFF-previous-sessions.md` | `96c5520b303b83267cf4d62c01ca56df1d8d1e6fc56afadb063378da9db07b18` | minor item m18 |
| `vineest-step3-epsilon-handoff.md` | `degen-vine/HANDOFF.md` | `36e387551f93522c5e63a603b88b05d5cc66580c6226185c71a20cc90904b550` | E4 |
| `finalsbest1-ladder-coupling-handoff.md` | `coarse-spliced/HANDOFF.md` | `65e476609d32114263976795e1ab40f25360d5f8141f81f2b7f1bddfa55d3cde` | E5 |
| `finalcount-stage2-handoff.md` | `finalcount-g3/HANDOFF.md` | `7b1dc352f8fb723c7c7415076765608deeb2f22ac9c13676166d7a46b86ac9a1` | E6, E9, E10, E13 |
| `finalcount-prop94-handoff.md` | `finalcount/HANDOFF.md` | `b75d3deb3c0f2de08210bc6bcbe739878a882b44acee281ea908cdc00b0f5f22` | E7 |
| `finalcount-prop96-handoff.md` | `finalcount-g8/HANDOFF.md` | `3d7cc1ad01ed367c508ea2f350b793e793152e499037e1ab91e7188acbff85a9` | E8, E12 |
| `remtame-case-i-notes.txt` | `research-remtame-i/NOTES.txt` | `e75726ffde26c8d41ca8afcc0f2205625089d428c8a53c19a3de431ae56bf13d` | E11 |
| `remtame-hinge-notes.txt` | `research-damaged/NOTES.txt` | `070086adcfe0405095f4e3ef8223276a3ead826d103007834f50208bf8821322` | E16, E17 |
| `remtame-hinge-referee/ref_hinge.py` | `research-damaged-referee/ref_hinge.py` | `88481c488063fe24f7368bed15ccf07fb47bc51603ffe6cd2dc62bca8bebc071` | E16 |
| `remtame-hinge-referee/ref_hinge.out` | `research-damaged-referee/ref_hinge.out` | `b6b9bae7fd5bbc52fd68f417e57b6e9acc558bde617d44cfc8d5c009fa925f0e` | E16 |
| `remtame-hinge-referee/ref_cluster.py` | `research-damaged-referee/ref_cluster.py` | `76f26e8f947c8df0a426708b62b77340f9d678db267e99dac35e1032d492a3f4` | E16, E17 |
| `remtame-hinge-referee/ref_cluster.out` | `research-damaged-referee/ref_cluster.out` | `4fd83afcf8698166d241a7376e22a0e1a2611226ca5e65204c0213e0d14faacb` | E16, E17 |
| `ghost-triangle-notes.txt` | `research-ghost/NOTES.txt` | `33e4d07c30372fbdff1f6489950f3122e7bd6c146fb5ff335513ddb46c5f2ebb` | E20 |
| `twist-profiles-notes.md` | `research-twistprof/NOTES.md` | `c670ac8467866c9b95448aa7cc8a3fec84e17f592bec05511cbb9b0ee4befb63` | E24 |
| `twist-profiles-referee.md` | `research-twistprof-referee/REPORT.md` | `a9426d080c90ca954707f2651cf01edce70589f5db979ac73e1ad82b65b8d6da` | E24 |
| `vineest-handoff.md` | `vineest-s3/HANDOFF.md` | `b357bd8e4c04e56c0032c19ba64ff4e94e7a3dcf1f94f43b79fd56b73a65476f` | E25 |
| `redvine-lower-clock-handoff.md` | `vine-b/HANDOFF.md` | `246db1920132016a7e69ba08b74454a16cd1b5613fa8a57a84d4c1ee9ea5b005` | E26 |
| `lftwist-class-count-handoff.md` | `represents/HANDOFF.md` | `60f65395c7baaeb66c95ba01e378d856dd3d9b813139213ab3a41abf7ac4527a` | E27 |
| `low-degree-cuts-handoff.md` | `g3-lowdeg/HANDOFF.md` | `f781e4d981bc13803b4fb9ec43c726b1c014cafce75ddd145799b86b51305ae2` | E23, E28 |
| `flower-design-notes.md` | `research-flower/NOTES.md` | `6779f0a65a804e864fcf04b50b50a0fe78fcda5294958ecd083a6c5c3947913c` | E29, E31, E32 |
| `flower-design-referee.md` | `research-flower-referee/REPORT.md` | `976e193659d671ce3be6c29b38840ae3b8bd2f5f1140a46203360c3f451db962` | E29–E33 |
| `flower-skeleton-handoff.md` | `flower-s1/HANDOFF.md` | `95d070280e057ff8e996d9fcc11354caa42979b72a8d718779af01d71ab54ff8` | E29 |
| `flower-skeleton-obstruction.md` | `flower-s1/OBSTRUCTION.md` | `d821c652bc24dd02b4026c7636e0de93dff6271a9606af02615b17ebe50a6dd0` | E30 |
| `flower-cutoff-notes.md` | `research-flowercut/NOTES.md` | `7b8408ada887af32d3b6a2a009d1e81c413e58906cdb5f83b97945101fee9f25` | E33, E34 |
| `flower-cut2-notes.md` | `research-cut2/NOTES.md` | `6ec7a5516923bc17d48c91313ae3fe814cbf13f1b2ec5c6dd0cc4284e7be1a28` | E35 |
| `flower-cut2-review.md` | `research-cut2/probe/independent-review.md` | `7d2a72c32c4487b3635600b00195ace590f4778066fcce2c54f20a619d7a6705` | E35 |
| `flower-cut2-fiber.md` | `research-cut2/fiber/FIBER.md` | `636cb19568122473549cdc930e0eed24d766e7efbf5fa83c3db36c09d9f9c89f` | E35 |
| `flower-cut2-fiber-referee.md` | `research-cut2/fiber-referee/REPORT.md` | `7afa647f8aeb7bdb4c128cd613f455a0c068e780ff329b039b4fc17cc52650e3` | E35 |
| `flower-cut2-faces-handoff.md` | `research-cut2/c2d/HANDOFF.md` | `735c28cbcd8615b68af176a8c838852a83d9ba66c3b4dea9fa2b74925e1ab109` | E35 |

## The flower-estimate completion (copied 2026-11-07, second errata pass)

The written completion of TARGET Prop `flowerest1` for 1/2 < γ < 1, its resolution packets and their independent
referee reports. Snapshots taken between about 15:20 and 15:45 UTC on 2026-11-07; the integrated supplement was still receiving
editorial revisions, so a later version may exist. In November 2026 the links in `SUPPLEMENT-v2.md`,
`o73-RESOLUTION.md` and `o82-RESOLUTION.md` that pointed to the private working directory were pointed at the copies
in this repository. The independent assessment of the printed proof is
`astra-flowerest1-report.md` (source `astra-flowerest1/REPORT.md`, sha256
`fc37a6b443b228e9dbac34a623e4d778c928aec8f63fdf580d12e7b3442b0e1f`). Sources below are relative to `<scratch>/flower-open/`.

| File | Source | sha256 | Entries |
|---|---|---|---|
| `flowerest1/SUPPLEMENT-v1.md` | `SUPPLEMENT-v1.md` | `ddd81fe1238e7c51379a69981b4d10aa68690ced46d0fc1b115200fc0c3774d7` | E29–E39, E43 (the first integrated proof; its OPEN items) |
| `flowerest1/SUPPLEMENT-v2.md` | `SUPPLEMENT-v2.md` | `b1d6d780e9f08fa447d075d14d0d72242b876900ae89b260982120c6b2047511` | E26, E29–E46 (§1 conventions, §12 errata table) |
| `flowerest1/STATUS.md` | `STATUS.md` | `7b1b644f8ebca0275f7fed3b1940fccc007f9e19925539ff832a52d23ba9191d` | tracker of the open items and referee results |
| `flowerest1/o63-RESOLUTION.md` | `o63/RESOLUTION.md` | `a50e0f93d68ac6fab7dfbfd59efb5808a1dc9717b391475c0d29d3cde7ddebc4` | E24 (flower case), E33 |
| `flowerest1/o73-RESOLUTION.md` | `o73/RESOLUTION.md` | `2735f3321bd5cc9eab77f87037e92695083c0a70abad4562a6f8d8ab30285e23` | E30, E35 |
| `flowerest1/o75-RESOLUTION.md` | `o75/RESOLUTION.md` | `47513e351d6a3e0b2dc2bef465e9278e880812f4ab3fa9ad69a6a3528587c96d` | E31, E43 |
| `flowerest1/o82-RESOLUTION.md` | `o82/RESOLUTION.md` | `3c39999c44a733980f99782a72ec593e5e4d61aa197ab2441af1dc956a099eff` | E39 |
| `flowerest1/o83-RESOLUTION.md` | `o83/RESOLUTION.md` | `91b9ed4dfc3d34530ef8b062a04fbbb7ee001f0c8e07be8849ab0906b341b869` | E5, E40, E44 |
| `flowerest1/o102-RESOLUTION.md` | `o102/RESOLUTION.md` | `772bac47097eb4c307b0df4993007857df23c5594a9949e5e03d6cfce4a555ab` | E46 |
| `flowerest1/o104-RESOLUTION.md` | `o104/RESOLUTION.md` | `2d711cbdd4c38275cbc1a6b3659eab9183b414e428bd6bdc561cbd2a05b2c5f2` | E32, E45 |
| `flowerest1/uclock-RESOLUTION.md` | `uclock/RESOLUTION.md` | `8bec1bc9c720d66c269efe0635058133cc754aac76d2e94ffeadff26c107d8ce` | E26 |
| `flowerest1/REFEREE.md` | `ref/REFEREE.md` | `c31ee38a03ddace8d565828f7f467008ee16c64cb6803ba0e70fd539e4d88d6d` | referee of SUPPLEMENT-v1's proved lemmas; E29, E35–E38, E41, E42, E44–E46 |
| `flowerest1/REFEREE-2.md` | `ref/REFEREE-2.md` | `028e5595d92c43ca9981ea71aa8086d90805be90643ef6de9a8c97892407d4e7` | referee of o63, o102, o75; E31, E33, E40, E46 |
| `flowerest1/REFEREE-73.md` | `ref/REFEREE-73.md` | `6b4b64eb1d8467859ba5c21d2312eb45363241a1bfc2459836cd5d8a6c37fd2d` | referee of o73; E30, E35, E45 |
| `flowerest1/REFEREE-82.md` | `ref/REFEREE-82.md` | `4f42eb173da7d7259d78182ad04446f63a14263e4393691e9d229a02f02aba8f` | referee of o82; E39 |
| `flowerest1/REFEREE-83.md` | `ref/REFEREE-83.md` | `56f98c771d0d5e503f9fd5b86fc29e872d2ac724f3ed51859ca6e70df366760a` | referee of o83; E40, E44 |

## The repair for 0 < γ ≤ 1/2 (November 2026)

The four research notes of the γ ≤ 1/2 repair, each with the report of its independent, refute-first referee. Every
verdict was ACCEPT WITH REPAIRS. Each note is the version its referee reviewed, edited for readers: a reader's preface
(what the note proves, how it fits the repair, where it is in Lean) was added, and internal paths and labels were
removed or replaced by descriptive names; the mathematics is unchanged. The referees' repairs (small corrections of
wording, scope or constants) are listed in the reports; they were applied in the Lean formalization, not folded into
the notes. The scripts named in the notes are not included. Overview: [`../GAMMA-LE-HALF.md`](../GAMMA-LE-HALF.md).

| File | Topic | Entries |
|---|---|---|
| [`gamma-le-half-tvine-blueprint-notes.md`](gamma-le-half-tvine-blueprint-notes.md) | the T-vine combinatorics and charts, for all sizes | E1 |
| [`gamma-le-half-tvine-blueprint-referee.md`](gamma-le-half-tvine-blueprint-referee.md) | its referee report | E1 |
| [`gamma-le-half-counting-notes.md`](gamma-le-half-counting-notes.md) | DH23 Props 9.4–9.6 and 10.4(2) for 0 < γ ≤ 1/2 | E1, E47, E48 |
| [`gamma-le-half-counting-referee.md`](gamma-le-half-counting-referee.md) | its referee report | E1, E47, E48 |
| [`gamma-le-half-ghost-step-notes.md`](gamma-le-half-ghost-step-notes.md) | the ghost step for all 0 < γ < 1 | E20 |
| [`gamma-le-half-ghost-step-referee.md`](gamma-le-half-ghost-step-referee.md) | its referee report | E20 |
| [`gamma-le-half-flower-notes.md`](gamma-le-half-flower-notes.md) | the flower estimate re-checked for 0 < γ ≤ 1/2 | E1, E29–E46 |
| [`gamma-le-half-flower-referee.md`](gamma-le-half-flower-referee.md) | its referee report | E1, E29–E46 |

Also copied: `seal-layergarden_v2-audit.md`, the independent seal audit of the Lean proof of `layergarden_v2` on main
(source: an internal audit record of the formalization, not part of the repository;
sha256 `a6e054b1bcc12371009c99db415188c0c1d932bf85d3094b23d045fcd921d025`). Evidence for the Lean claims in E26.

## Already in the repository before 2026-11-07

| File | Entry |
|---|---|
| `dh23-prop96-case4.md` | E1 (the necklace counterexample) |
| `dh23-prop96-referee.txt` | E1 (independent referee) |
| `kqmainest1-necklace.txt` | E1 (F73) |
| `case4-gamma-above-half.txt`, `case4-gamma-above-half-referee.txt` | E1 (F75) |
| `ylem1-investigation.md` | E2b |
| `git20-general-d.md` | E2g |
| `vine2-m1.txt` | E3 |
| `erratum-remtame.md` | E11 (part (a), F48) |

`closure-audit/` holds the read-only closure audit prepared for the project's formalization report, which has not
been published (decisions D14, D15); it is maintained separately.
