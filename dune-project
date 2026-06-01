(lang dune 3.23)

(using menhir 3.0)

(name my_project)

(generate_opam_files true)

(source
 (github username/my_project))

(authors "Your Name")

(maintainers "Your Name")

(package
 (name my_project)
 (synopsis "Compiler/interpreter project")
 (depends
  ocaml
  dune
  menhir
  sedlex
  alcotest))