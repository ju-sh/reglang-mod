with import <nixpkgs> {};

let cP = coqPackages.overrideScope' (self: super: {
  mathcomp = super.mathcomp.override { version = "2.1.0"; };
});
in

mkShell {

  packages = (with cP; [
    coq
    hierarchy-builder
    # reglang
  ]) ++ [
    dune_3 
    opam
    ocaml 
    emacs
  ];

}
