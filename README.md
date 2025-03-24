# Artifact for the ITP submission

This is the Coq project referred in the paper.

## Build

Tested on Coq/Rocq, version `8.20.0` ([installation
instructions](https://rocq-prover.org/releases/8.20.0)). Older Coq versions are
**not** supported. No external libraries are required. The provided `Makefile`
builds and checks the entire project. Processing the whole project might take a
while (about 45 minutes --- we are still working on improving the performance of
our automation!).

```
make proofs
```

Upon success, the `make` command should terminate with the `0` return code and print a
`*** SUCCESS ***` message. The success message follows a log from the
[`Presentation`](theories/Presentation.v) script which iterates through the
lemmas mentioned in the paper.

### Docker

Alternatively, `docker` can be used for consistent build:

```bash
docker build -t dlstalk-coq .

docker run -it --rm dlstalk-coq
```

## Glossary and submission paper references

In the [`Presentation`](theories/Presentation.v) module (also available as
[HTML](html/DlStalk.Presentation.html)) you will find a `Check`-list of
references to all theorems, lemmas, definitions and notations mentioned in the
paper. The file also briefly explains selected technicalities of the
mechanisation. Note that some of them have been edited in the submission for
readability; the less obvious simplifications have been proven equivalent in the
[`PresentationCompat`](theories/PresentationCompat.v) module.


