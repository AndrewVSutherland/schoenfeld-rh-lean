# Third-party code in this repository

| Path | Source | Licence | Changes |
|---|---|---|---|
| `PrimeNumberTheoremAnd/**/*.lean` (62 modules) | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd @ `a4fb6989b07e9c76b511807ae93e33e25b820e9b` | Apache-2.0 (`PrimeNumberTheoremAnd/LICENSE`, copied from upstream) | none: byte-identical, hashes in `PrimeNumberTheoremAnd/UPSTREAM.md` |
| `SchoenfeldRH/Converse/PsiBigO.lean` | https://github.com/AIOvernight/rh-prime-error @ `c55887da891944dc9f9cc42de53b2216744e746b`, file `RHPrimeError/Converse.lean` | Apache-2.0 (`SchoenfeldRH/Converse/LICENSE`, copied from upstream) | an 11-line provenance comment was prepended; the rest is byte-identical (`tail -n +12 SchoenfeldRH/Converse/PsiBigO.lean` equals the original file) |

The copyright and licence headers of these files are unchanged. `PrimeNumberTheoremAnd/UPSTREAM.md` was written for
this repository; it is not an upstream file.

Lake dependency (not in this repository): Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`)
and its dependencies, as pinned in `lake-manifest.json`.

Everything else in this repository was written for this project and is released under the Apache License 2.0
(`LICENSE`, `NOTICE`).
See README.md, "Provenance", for how it was written.

This repository contains no file from https://github.com/senamakel/erdos-985 (no licence) or
https://github.com/senamakel/schoenfeld-rh (GPL-3.0). The 16 theorem statements and the definition that an earlier
version of this project shared with erdos-985 have been removed; see README.md, "Provenance".
