FROM coqorg/coq:8.20.1-ocaml-4.14.2-flambda

WORKDIR /app
RUN mkdir -p /app && chown -R coq:coq /app

USER coq

COPY --chown=coq:coq . /app

CMD ["make"]
