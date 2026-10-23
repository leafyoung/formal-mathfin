"""Architecture gates: every module is part of the library's graph.

The values gates (``test_values.py``) are keyed to the benchmark corpus: they audit what the
corpus cites. On 2026-10-21 a coherence pass found that growth had started to go around the
corpus. A batch of 42 modules came with 7 corpus entries; 38 of the modules were cited by no
entry, and 15 of them imported nothing from the library and were imported by nothing. They
were honest, but the honesty gates could not see them, and they did not connect to anything.
The repair was to build the missing bridges, not to fence the modules off. These tests keep
the library one graph:

* ``test_foundations_imports_only_foundations``: ``Foundations/`` is the layer the pricing
  sections stand on, so it imports nothing above it. A model lives in its market's section;
  a module that joins a foundation to a model lives in ``Bridges/``.
* ``test_every_module_is_connected``: every module has an edge in the import graph. It
  imports a library module, or a library module imports it.
* ``test_every_module_is_used``: every module is imported by another library module or by a
  corpus entry. A result that nothing uses and nothing cites is a claim nobody checks.

``STAGING`` admits a module whose consumer is being built in an open issue. It names the
issue, and it is meant to stay short-lived. It is not a place to park a module that does
not connect: that module needs a bridge.
"""

from __future__ import annotations

import re
from pathlib import Path

from tools.verify.corpus import iter_entries

MATHFIN_DIR = Path("MathFin")
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(MathFin(?:\.[\w']+)+)", re.M)
SNIPPET_IMPORT_RE = re.compile(r"^import\s+(MathFin(?:\.[\w']+)+)", re.M)

# Aggregators: they import everything, so an edge from them shows nothing.
AGGREGATORS = frozenset({"MathFin.AxiomAudit", "MathFin.AxiomAuditGen", "MathFin.Blueprint"})

# module -> open issue whose work adds its consumer. Keep it short-lived.
#
# 2026-10-22: a benchmark-corpus entry was added for every one of the 12 modules originally
# staged here (tracked at issue #3). That alone satisfies `test_every_module_is_used` (corpus
# citations count there) but NOT `test_every_module_is_connected` (import-graph edges only, by
# design — see that test's own code). Four already had a real import edge
# (BinaryBarrierOption/PartialTimeBarrierOption/SoftBarrierOption import a Foundations module;
# CleanPriceAccrued imports MacaulayModified) and were removed from STAGING in the first
# fast-follow. A second fast-follow built a genuine bridge for seven more of the remaining
# eight: SABRImpliedVol now imports ImpliedVolatility (the bracketed stochastic-vol correction
# term, scaled by time-to-exercise, when positive, strictly raises the ATM Black price above the
# bare backbone's, via `bsV_strictMonoOn_sigma`); BondForward is imported by FxForwardParity (CIP is a
# zero-coupon instance of bond-forward replication); KeyRateDuration imports MacaulayModified
# (the partition-of-unity identity specialized to the real modified-duration numerator);
# LoanAmortization imports MacaulayModified too (both amortization schedules price to par via a
# general telescoping identity, proved as a `bondPriceDisc` corollary); BacktestStatistics
# imported Performance.Ratios (the module was later deleted; its relative-drawdown definition,
# not its [0, 1] bounds, now lives in Performance.RelativeDrawdown); StudentTValueAtRisk (whose
# first bridge, to RiskMeasures.Gaussian, was superseded when the module was rebuilt on a real
# Student-t law) imports Foundations.StudentT and RiskMeasures.ExpectedShortfall (VaR and ES of
# the law, through the library's own `valueAtRisk`/`expectedShortfall`). Only BirthdayParadox remains
# staged: it predates the Lean module system (see its own docstring), so no `module`-header file
# can import it — but it CAN import one itself (the restriction is one-directional). Investigated
# 2026-10-22: no Foundations module shares genuine combinatorial/probabilistic structure with the
# discrete birthday-collision computation without inventing a real new result (a Poisson
# approximation of the no-match probability — tying the discrete count to `Real.exp` and the
# Poisson zero-count law in `PoissonPgf`/`PoissonCounting`, not to `StandardNormal` — would be
# genuine, but is new formalization, not a bridge); it stays staged pending that real work, not
# as a place to park a cosmetic import.
_ISSUE_3 = "https://github.com/leafyoung/formal-mathfin/issues/3"
STAGING: dict[str, str] = {
    "MathFin.Foundations.BirthdayParadox": _ISSUE_3,
}


def _module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def _modules() -> dict[str, list[str]]:
    mods = {}
    for path in sorted(MATHFIN_DIR.rglob("*.lean")):
        if path.name.startswith("."):  # tool temp files (`ledger verify --exec`), not modules
            continue
        name = _module_name(path)
        if name in AGGREGATORS or name.startswith("MathFin.Blueprint."):
            continue
        mods[name] = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
    return mods


def _importers(mods: dict[str, list[str]]) -> dict[str, set[str]]:
    importers: dict[str, set[str]] = {m: set() for m in mods}
    for m, imps in mods.items():
        for i in imps:
            if i in importers:
                importers[i].add(m)
    return importers


def _cited_by_corpus() -> set[str]:
    cited = set()
    for _, entry in iter_entries():
        cited.update(SNIPPET_IMPORT_RE.findall(entry["code"]["lean"]))
    return cited


def test_foundations_imports_only_foundations() -> None:
    bad = {
        m: [i for i in imps if not i.startswith("MathFin.Foundations.")]
        for m, imps in _modules().items()
        if m.startswith("MathFin.Foundations.")
    }
    bad = {m: v for m, v in bad.items() if v}
    assert not bad, (
        "Foundations/ imports only Foundations/. Move the module to the section of the model "
        "it uses, or to Bridges/ if it joins a foundation to a model:\n"
        + "\n".join(f"  {m} imports {', '.join(v)}" for m, v in sorted(bad.items()))
    )


def test_every_module_is_connected() -> None:
    mods = _modules()
    importers = _importers(mods)
    islands = sorted(
        m for m, imps in mods.items()
        if m not in STAGING and not any(i in mods for i in imps) and not importers[m]
    )
    assert not islands, (
        "these modules import no library module and no library module imports them. Build "
        "the bridge: a proved lemma tying the module's objects to the library's (one normal "
        "law, `valueAtRisk`, `bsV`, the numéraire, the bond lemma, ...), placed so that one "
        "module imports the other:\n  " + "\n  ".join(islands)
    )


def test_every_module_is_used() -> None:
    mods = _modules()
    importers = _importers(mods)
    cited = _cited_by_corpus()
    unused = sorted(m for m in mods if m not in STAGING and not importers[m] and m not in cited)
    assert not unused, (
        "nothing imports these modules and no corpus entry cites them. Give the headline "
        "result a corpus entry, or let the module that needs it import it:\n  "
        + "\n  ".join(unused)
    )


def test_staging_entries_name_an_issue_and_exist() -> None:
    mods = _modules()
    for m, issue in STAGING.items():
        assert m in mods, f"STAGING lists {m}, which no longer exists"
        assert re.search(r"/issues/\d+$", issue), f"STAGING entry {m} must name an issue URL"
