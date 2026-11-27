# mediLEAN

Medical advice where every recommendation comes with a machine-checked proof
that it follows from explicit medical premises plus the user's confirmed
facts. Lean checks the proofs; errors can only live in the premises or the
facts, both of which are visible and reviewable.

## Why

Formal logic began as an attempt to make reasoning precise, not just
mathematics. Frege's *Begriffsschrift* (1879) was a "concept script" for
thought in general. Russell's type theory, built to repair Frege's system,
led through Church to the type theories that proof assistants like Lean are
built on. The same tools were later turned on ordinary language. Kripke gave
modal logic its possible-worlds semantics, and Montague used type theory and
possible worlds to give English sentences precise meanings.

Today the most visible use of this tradition is in mathematics. Proof
assistants force you to say exactly what you assume and to justify every
step, and LLMs have recently had a lot of success proving theorems in Lean.
But Lean's type theory isn't limited to mathematics or to first-order logic,
and the original ambition was broader.

mediLEAN is an attempt to make LLMs reason more carefully in another
subject, medical advice, by having them work in a formal language. It uses
the modal logics of knowledge, time and obligation. The LLM states its
medical knowledge as explicit premises, and Lean checks that every piece of
advice follows from them. When a proof won't go through, that exposes a gap
in the knowledge instead of letting it be glossed over. Whether the premises
are medically right is still a question for human review.

## Status

The premises currently come from an LLM's own knowledge and nobody has
reviewed them. This is not medical advice.

## Layout

| Folder | Role |
|--------|------|
| `MediLean/Core/` | Fixed logic: modal operators (knowledge, time, obligation), frames, the care scale |
| `MediLean/Theory/` | The premises. **`Premises.lean` holds every assumption**; `Rules.lean` holds consequences proved from them |
| `MediLean/Claims/` | Tests: certified verdicts, test models (including known atypical presentations) and rejected claims, witnesses, checklist minimality |

`DISCOVERY_LOG.md` records every claim posed, what it required, and what we
learned.

## Running

Requires [elan](https://github.com/leanprover/elan) (installs Lean 4.36.0
from `lean-toolchain`).

```bash
lake build              # check every proof
tests/run_all.sh        # layering + build + axiom audit
tests/mutation_test.sh  # corrupt premises, confirm the tests notice
```
