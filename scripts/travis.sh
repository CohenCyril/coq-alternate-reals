#! /bin/bash

# --------------------------------------------------------------------
set -x
set -e

# --------------------------------------------------------------------
git clone https://github.com/strub/finmap.git

# --------------------------------------------------------------------
sudo add-apt-repository --yes ppa:avsm/ppa
sudo apt-get update -q
sudo apt-get install -q -y opam

# --------------------------------------------------------------------
if [ ! -e "${HOME}/.opam/config" ]; then
  opam init -n -y
  eval $(opam config env)
  opam config var root
  opam remote add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam remote add coq-core-dev  https://coq.inria.fr/opam/core-dev
  opam remote add coq-released  https://coq.inria.fr/opam/released
  opam pin add -y -v coq 8.5.dev
  opam install -y -v coq-mathcomp-ssreflect.dev
  opam install -y -v coq-mathcomp-algebra.dev
  opam install -y -v coq-mathcomp-real_closed.dev
else
  eval $(opam config env)
fi

# --------------------------------------------------------------------
opam pin -y -v add finmap/.
opam list
