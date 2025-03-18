# Artifact for the ITP submission

## Build

Tested on Coq/Rocq, version `8.20.0` ([installation
instructions](https://rocq-prover.org/releases/8.20.0)). No external libraries
are required. The provided `Makefile` builds and checks the entire project.
Processing the whole project might take a while (about 45 minutes --- we are
working on it!).

```
make
```

## Glossary and submission paper references

In [`Presentation`](theories/Presentation.v) you will find a `Check`-list of
references to all theorems, lemmas, definitions and notations referred in the
paper. Note that some of them have been edited in the submission for
readability; the less obvious simplifications have been proven equivalent in the
[`PresentationCompat`](theories/PresentationCompat.v) module.


