# mediLEAN

Medical advice where every recommendation comes with a machine-checked proof
that it follows from explicit medical premises plus the user's confirmed
facts. Lean checks the proofs; errors can only live in the premises or the
facts, both of which are visible and reviewable.

The premises currently come from an LLM's own knowledge and nobody has
reviewed them. This is not medical advice.

## Layout

| Folder | Role |
|--------|------|
| `MediLean/Core/` | Fixed logic: modal operators (knowledge, time, obligation), frames, the care scale |
| `MediLean/Theory/` | The premises. **`Premises.lean` holds every assumption**; `Rules.lean` holds consequences proved from them |
| `MediLean/Claims/` | Tests: certified verdicts, test models and rejected claims, witnesses, checklist minimality |

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
