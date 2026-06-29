# Atom Boundary Fix Plan

Generated from subagent review (`atom-boundary-subagent-report.json`).

## Summary

- Candidates reviewed: 16
- Confirmed boundary errors: 14
- No action needed: 2 (`ch0:4.2`, `ch8:2.1`)

## Classification

### Swallows next statement (must be moved/duplicated to next atom)

| dcref | atom file | what is swallowed | next atom |
|-------|-----------|-------------------|-----------|
| `ch0:5.3` | `c20e049fba4e.md` | Flow/trajectory exposition leading into Proposition 5.4 | `ch0:5.4` (`453ecde8947b.md`) |
| `ch8:5.3` | `8a57517fee19.md` | Ball model $B^n$ and metric $h_{ij}$ introduction | `ch8:5.4` |
| `ch10:4.9` | `8286f921d5a2.md` | Bibliographic note + unnumbered Toponogov theorem | chapter doc / no atom |

### Includes transitional prose (trim and move to chapter doc)

| dcref | atom file | trim point |
|-------|-----------|------------|
| `ch0:5.5` | `fc5a1bb299dd.md` | After proof of lemma; remove "Topology of manifolds" section |
| `ch4:2.5` | `91101fb52f8d.md` | After $\blacksquare$; remove coordinate-computation passage |
| `ch6:2.1` | `73bbdba0e0a8.md` | After $\square$; remove $H_\eta$ introduction |
| `ch6:2.9` | `1bc6577d8e3a.md` | After $\square$; remove geometric interpretation of sectional curvature |
| `ch7:2.3` | `b293201bcf35.md` | After "class of complete manifolds."; remove distance-function intro |
| `ch8:3.1` | `b1bc4979d87f.md` | After $\square$; remove completeness of $H^n$ paragraph |
| `ch8:4.2` | `ed5c99ea7483.md` | After "Therefore $g$ is an isometry. \\square"; remove space-forms intro |
| `ch8:4.3` | `25c5af8cc0f8.md` | After $\square$; remove program for classifying space forms |
| `ch8:4.5` | `b9cdcdcd003d.md` | After $\square$; remove historical non-Euclidean geometry prose |
| `ch9:2.2` | `d19dfbacb4d5.md` | After $\square$; remove arc-length/energy setup |
| `ch12:3.1` | `167b9abd6797.md` | After $\blacksquare$; remove "From now on..." paragraph |

## No error

- `ch0:4.2` — trailing text is the example's own conclusion.
- `ch8:2.1` — trailing text is the theorem's own post-proof remark.

## Recommended workflow

1. **Verify next-atom overlap** for `ch0:5.3`, `ch8:5.3`, `ch10:4.9` before trimming, to avoid duplicating or losing content.
2. **Trim transitional-prose cases** by cutting the atom body at the reported proof-ending marker.
3. **Move trimmed prose** to the corresponding `docs-src/*.mdx` chapter file (or create/update it on `main`).
4. **Update `atom-boundary-review.md`** to mark fixed items and remove the false positives.
5. **Run validation**: `python3 tools/astrolabe_store.py` or the review-app backend should still pass.

## Risk notes

- `ch10:4.9` swallows an *unnumbered* Toponogov theorem; there is likely no `dcref` for it, so the trimmed text should go to the chapter doc.
- Because atom files are content-addressed, trimming a body changes the hash. Any edges referencing the old hash must be migrated using `AstrolabeStorage.update_record` semantics (already handled by `tools/astrolabe_store.py`).
- `main` does not yet have `docs-src/*.mdx`; the transitional prose can be staged there or held in a temporary chapter doc until the cleanup branch is merged.
