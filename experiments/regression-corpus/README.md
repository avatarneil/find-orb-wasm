# Independent regression corpus

This directory contains **96 distinct objects, 192 core geometries and two temporal supplements**, acquired from NASA/JPL SBDB and Horizons. All 194 cases have complete reference data. Each case supplies five nested inverse problems, giving **970 arc problems**, 7,178 astrometric positions and 1,164 matched state/element pairs. These are independent numerical references for software regression, not measured astrometry or exact physical truth.

The corpus and raw responses are development fixtures. They are not included in the browser `.data` bundle.

## Verify without network access

From the repository root:

```sh
node experiments/regression-corpus/verify.mjs
node --test experiments/regression-corpus/integrity.test.mjs
```

The verifier checks all 414 compressed raw files, decoded envelopes, exact response bytes, query URLs, physical-model headers and generator source hashes. It reconstructs the frozen catalog selection, comet apparition choices and complete normalized corpus from cached responses, requiring byte-identical output. Missing or changed evidence, incomplete acquisition, inconsistent counts and absent sentinel cases fail verification. Offline replay does not overwrite the published corpus.

The ten integrity tests use a temporary copy. They exercise malformed and missing caches, numeric parsing, inconsistent orbit solutions, invalid API signatures, incomplete publication and falsified coverage counts. Failed validation must leave the original corpus unchanged.

To run just the normalization replay:

```sh
node experiments/regression-corpus/fetch.mjs --offline
```

`../regression-suite/` owns engine execution, noise scenarios, prediction metrics and native/WASM comparison gates. Fixture verification does not claim that every solver fit succeeds or that short arcs identify unique orbital elements.

## Frozen selection

`protocol.json` fixes catalog constraints, named stress objects, schedules and object-level splits. `selection.json` records the exact selected catalog rows and was frozen at `2026-09-13T22:05:00.024Z`, before ephemeris acquisition and solver evaluation.

| Stratum | Objects |
| --- | ---: |
| Atiras | 6 |
| Atens | 8 |
| Apollos | 10 |
| Amors | 8 |
| Inner main belt | 4 |
| Main belt, 2.0–2.5 au | 6 |
| Main belt, 2.5–2.82 au | 6 |
| Main belt, 2.82–3.2 au | 6 |
| Outer belt / Hilda region | 6 |
| Jupiter Trojans | 6 |
| Centaurs | 4 |
| Trans-Neptunian objects | 4 |
| Short-period comets | 6 |
| Halley-type comets | 4 |
| Hyperbolic comets | 4 |
| Long-period comets | 4 |
| Low-eccentricity belt objects | 2 |
| Retrograde asteroids | 2 |

Within the declared catalog bounds, selection takes named priorities and then the smallest numeric SPK IDs, excluding previously selected identities. There is no selection by solver performance or successful Horizons acquisition. The Hilda-region label describes a semimajor-axis band; it does not establish resonance.

There are **55 development objects and 41 regression-holdout objects**. Previously examined Ceres, Pallas, Juno, Vesta, Eros, Achilles, Apophis and Bennu remain development/known-regression objects. All epochs, arc lengths and noise realizations of one object share its split. Encke's perihelion supplement inherits Encke's regression-holdout split. Once inspected, holdout results become regression evidence; they are not a reusable untouched sample for choosing new methods.

These strata favor established catalog objects with at least 100 days of data arc and 50 observations. They do not form a population probability sample, a discovery sample or a calibrated survey simulation.

## Observation and forecast schedules

Core anchors are **2026-02-01 00:00 UTC** and **2026-08-01 00:00 UTC**. Each tracklet has four exposures at 0, 20, 40 and 60 minutes.

| Arc ID | Tracklet days relative to anchor | Exposures |
| --- | --- | ---: |
| `one-hour` | 0 | 4 |
| `two-night` | 0, 1 | 8 |
| `three-night` | 0, 1, 2 | 12 |
| `one-week` | 0, 1, 2, 7 | 16 |
| `one-month` | 0, 1, 2, 7, 14, 21, 30 | 28 |

Every arc has independent prediction targets at **+1, +3 and +7 days after its last exposure**. The bank deduplicates common epochs into 37 positions per case. A position used as a forecast for one short arc may be an input to a longer arc; the explicit per-arc index lists define that partition. Repeated arcs and epochs of one object are correlated.

The two predeclared supplements cover Apophis around its April 2029 encounter and Encke around the catalog's nominal 2023 perihelion. The latter uses an approximate UTC anchor derived from SBDB `tp`, then rounded to the API's millisecond input precision. Its original anchor and 0.362 ms adjustment are retained. `acquisition-history.json` preserves the initial Encke response that exposed the need to handle this precision explicitly.

The observer is MPC **500**, the geocenter. These geometries have no ground-station horizon or daylight interpretation. `suite.stationSupplement` points to the seven previously examined F52 observable cases in `../short-arcs/fixtures/observable-corpus.json`; those remain separate station/visibility regression evidence.

## Coordinates, epochs and physical applicability

The [Horizons quantity definitions](https://ssd.jpl.nasa.gov/horizons/manual.html#specific-quantities) define quantity 1 as ICRF astrometric RA/Dec with down-leg light-time correction. The corpus requests decimal degrees at UTC reception epochs. It does not use apparent RA/Dec quantities that add stellar aberration and gravitational deflection.

State vectors are geometric, Sun-centered, IAU76/J2000 ecliptic coordinates in au and au/TDB-day. Each osculating-element table supplies its own Keplerian GM. The ecliptic obliquity relative to ICRF is 84,381.448 arcseconds. `generation-protocol.json` records the exact frame, center, units and correction query fields.

Horizons quantity 30 provides TDB minus UTC; TT minus UTC is pinned to 69.184 seconds for these dates. The code checks that the remaining TDB–TT difference is below 2 ms. UTC and TDB are not silently interchanged. Requested and returned UTC epochs are retained, as are the printed geometric TDB epochs. Epoch matching is bounded by finite API precision: at most 1 ms for observer requests and 2e-9 days for geometric output. The final corpus's largest observed difference is about 40 microseconds. State and element tables must return the same TDB epoch and orbit-solution identifier.

There are **126 gravity-compatible `strict` cases and 68 `model-limited` cases**. The strict designation requires recognized JPL gravitational headers and no declared active extra forces. It remains a comparison against independently realized ephemerides and force models, with a predeclared 0.1 arcsecond forward tolerance. It is not a formal proof of physical equivalence.

Every comet is model-limited for the baseline gravity-only configuration. Explicit SBDB and Horizons nongravitational coefficients, special mission/SPK sources such as Bennu, unknown headers and catalog two-body flags are also retained as applicability reasons. Null catalog coefficients mean unknown/not listed, not zero force. Model-limited cases have no invented absolute truth tolerance; numerical parity and structural solver checks still apply.

Independent state/element checks verify inverse semimajor axis, perihelion, inclination and eccentricity identities, including hyperbolic cases. These checks detect frame, epoch and parsing inconsistencies. They do not establish orbit-fit uniqueness or replace uncertainty calibration.

## Files and acquisition

| File | Role |
| --- | --- |
| `protocol.json`, `selection.json` | Frozen sampling, schedules, object rows and splits |
| `generation-protocol.json` | Query conventions, transport bounds and applicability policy |
| `comet-record-selection.json` | Cached lookup rows and deterministic apparition disambiguation |
| `acquisition-history.json` | Retained preflight response and precision adjustment rationale |
| `corpus.json` | Normalized cases, arc indices, state/element references and source graph |
| `raw/*.json.gz` | Exact API response text, original query, URL, timestamp and hashes |
| `catalog.mjs`, `resolve-comets.mjs`, `fetch.mjs`, `io.mjs` | Acquisition, selection, parsing and replay |
| `verify.mjs`, `integrity.test.mjs` | Offline integrity authority and failure tests |

The normalized corpus is 6,305,506 bytes. Compressed raw evidence totals 2,449,931 bytes, representing 6,778,998 decoded envelope bytes. The corpus SHA-256 is:

```text
66a801d3e4b1207acd07e96bb7a83fdffdcd677412a0c79e34b89f9f021df14e
```

The acquisition tools issue conservative sequential requests, cache successful responses immutably, bound retries to three attempts and fail on transport or parser errors. Only explicit successful API responses reporting unavailable ephemerides become recorded unavailable scientific cases. This frozen corpus has none.

Periodic comet primary IDs sometimes return multiple apparition records. Following the [Horizons small-body selection documentation](https://ssd.jpl.nasa.gov/horizons/manual.html#small-bodies), the resolver chooses the newest numeric `Epoch-yr`, breaking ties by greatest numeric record number, restricted to the exact frozen identity. It preserves the lookup and chosen row, then uses that explicit record for all tables. Record numbers are not permanent identifiers; the archived lookup is essential provenance.

Use the checked-in responses for exact reproduction. A live API rerun can return updated orbital solutions, catalogs or temporary record IDs, so it cannot promise byte-identical references. To extend the dataset, create a new corpus version, freeze its identities and split before solver evaluation, acquire and preserve fresh lookup/ephemeris evidence, then run integrity verification. Do not overwrite this frozen regression baseline with newly downloaded data.

Catalog API and filter conventions are documented by [JPL SBDB Query](https://ssd-api.jpl.nasa.gov/doc/sbdb_query.html) and [SBDB filters](https://ssd-api.jpl.nasa.gov/doc/sbdb_filter.html). Request fields and limitations are documented by the [Horizons API](https://ssd-api.jpl.nasa.gov/doc/horizons.html) and [Horizons manual](https://ssd.jpl.nasa.gov/horizons/manual.html).
