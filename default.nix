with import <nixpkgs> {};

mkShell {
  packages = (with coqPackages; [
    coq
    mathcomp
  ]) ++ [
    dune_3 
    opam
    ocaml 
    emacs
  ];
}
