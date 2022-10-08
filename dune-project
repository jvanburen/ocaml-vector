(lang dune 3.4)

(name vec)

(generate_opam_files false)

(source
 (github jvanburen/ocaml-vector))

(authors "Jacob Van Buren")

(maintainers "Jacob Van Buren")

(package
 (name vec)
 (synopsis "immutable vectors")
 (description "Immutable vectors based on relaxed radix-balanced finger trees")
 (depends ocaml dune)
 (tags (wow cool jvb)))

