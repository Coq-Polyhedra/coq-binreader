(lang dune 3.8)

(using coq 0.8)

(wrapped_executables false)

(name coq-binreader)

(generate_opam_files true)

(package
 (name coq-binreader)
 (depends
  (ocaml (>= 4.08.0))
  (coq (and (>= 8.20) (< 8.21)))
  ; coq-bignums uses its own (9.0.0+coqXX) versioning, independent of Coq's.
  ; An upper bound like (< 8.21) would wrongly exclude 9.0.0+coq8.20, so we
  ; only set a lower bound and let coq-bignums' own dependency on
  ; coq (>= 8.20 < 8.21) select the matching build.
  (coq-bignums (>= 8.20)))
)
