# Public render delivery diagnostic — PALOMAR-2026-10-30-000014 v1

The registered proof and four archived evidence files verify. The public data
service adds Cloudflare Insights markup to two rendered HTML files, so their
served bytes differ from the published render manifest. All thirteen originals
in the authenticated GitHub rendering artifact match that manifest; eleven
other public responses match directly. The mismatch concerns HTTP delivery of
HTML, not Lean source or kernel evidence.

Manifest tree: `c74e22dcdcc6f47a03b322a7086e3ff0b0259abe6be557a2d0363ee2bf7f4a48`.
Base path: `https://data.palomar-registry.org/renders/PALOMAR-2026-10-30-000014-v1/c74e22dcdcc6f47a03b322a7086e3ff0b0259abe6be557a2d0363ee2bf7f4a48/`.

| File | Expected bytes | Served bytes | Expected SHA-256 | Served SHA-256 |
| --- | ---: | ---: | --- | --- |
| `Challenge/index.html` | 995518 | 995885 | `12e3c93667d42ee6315da3acbca88cb6062f1a249c1ca7aa03980cb119708803` | `fe02d42eefed4b9aee3b3f2782255568ee5dab7525f78a42ac30e0eb9283a4cd` |
| `search/index.html` | 12030 | 12397 | `140520877e6b7442f471c668ffe209523e1ae312b5cae4e691711b7f9f48cb66` | `6c652ed1229157758bf6255eeba3f8842c1faf25e199ba7c34bda3eb78146d14` |

For each file, the only difference is one `static.cloudflareinsights.com` script
and its newline. Removing exactly that insertion **in memory** produces the
original archived bytes; downloaded files were not silently rewritten to pass.
All observations and expected/actual hashes are retained in the machine record.
The original ZIP digest is
`17d964eaabd2a93f60bdec1b30ade35a0c94d588bd6484798ed1d39d23575f1b`.

This is consistent with Cloudflare's documented automatic beacon injection.
Its [official documentation](https://developers.cloudflare.com/web-analytics/faq/)
explains that a `Cache-Control: public, no-transform` response prevents payload
modification and automatic injection. The service maintainer can disable that
injection on immutable render paths or set the appropriate no-transform response
policy, then repeat raw-byte readback against the existing manifest. No source
change, Lean replay or new registration is indicated by this HTML-only finding.
No operator message or service configuration change was sent by this agent.
