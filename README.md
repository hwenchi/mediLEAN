# mediLEAN

Medical advice where every recommendation comes with a machine-checked proof
that it follows from explicit medical premises plus the user's confirmed
facts. Lean checks the proofs; errors can only live in the premises or the
facts, both of which are visible and reviewable.

## Why

People increasingly ask AI for medical advice, and LLMs answer fluently
whether or not they're right: a wrong answer sounds as confident as a right
one. mediLEAN separates what is proven from what is assumed, so nothing false
can pass as established.

Expert systems like MYCIN reasoned explicitly but stalled on the knowledge
acquisition bottleneck: hand-translating expertise into rules was slow and
brittle. LLMs make that translation cheap. mediLEAN pairs the two: the LLM
drafts premises and searches for proofs, and Lean's kernel accepts only valid
ones. Modal logic gives advice its shape (what's known, what happens over
time, what one should do), and caution is a rule: if a dangerous condition
can't be ruled out, emergency care is obligatory.

The open problems are reviewing the premises, which still needs experts;
calibration, since the logic is yes/no and over-refers; and adoption.

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
