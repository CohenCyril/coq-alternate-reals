#! /bin/bash

# --------------------------------------------------------------------
eval $(opam config env)
opam pin -y -v remove coq-mathcomp-finmap
