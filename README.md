# mediLEAN

An experiment in having an LLM reason about medical advice in Lean, a
formal language whose proofs a computer checks.

## Why

Formal logic began as an attempt to make reasoning precise, not just
mathematics. Frege's *Begriffsschrift* (1879) was a "concept script" for
thought in general. Russell's type theory, developed in response to
foundational problems in Frege's system, helped establish a tradition of
formal systems for reasoning that eventually led to the type theories
underlying proof assistants like Lean. The same tools were later turned on
ordinary language. Kripke gave modal logic its possible-worlds semantics, and
Montague used type theory and possible worlds to give English sentences
precise meanings.

LLMs come from another tradition in language processing: the statistical
one. They are fluent and know a great deal, but their reasoning is not
inherently subject to formal verification. Combining the two has shown
considerable promise in mathematics: LLMs propose proofs, Lean checks them,
and the combination is opening up new possibilities for mathematical
discovery. Lean's type theory isn't limited to mathematics or first-order
logic, so this combination can return to formal logic's broader ambition:
precise reasoning about anything.

mediLEAN applies the same idea to medical advice, using modal logics of
knowledge, time, and obligation. The LLM states its medical knowledge as
explicit premises, and Lean checks that every piece of advice follows from
them. When a proof won't go through, that exposes a gap in the knowledge
instead of letting it be glossed over. Whether the premises are medically
correct remains a question for human review.

## Status

Early and exploratory. The premises come from an LLM's own medical
knowledge, and no clinician has reviewed them. This is not medical advice.

## Layout

| Folder | What's in it |
|--------|--------------|
| `MediLean/Core/` | The fixed logic: operators for knowledge, time and obligation, and the levels of care |
| `MediLean/Theory/` | The medical knowledge. `Premises.lean` holds every assumption; `Rules.lean` holds what's proved from them |
| `MediLean/Claims/` | The tests: advice that must follow, advice that must not, and small example patients, including known atypical presentations |

`DISCOVERY_LOG.md` records each claim we tried, what it required of the
premises, and what we learned.

## Running

Requires [elan](https://github.com/leanprover/elan), which installs the
Lean version in `lean-toolchain`.

```bash
lake build              # check every proof
tests/run_all.sh        # also check the layering, and that no proof uses sorry or classical choice
tests/mutation_test.sh  # break each premise and confirm some test notices
```
