FROM ubuntu:16.04

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get -q -y update
RUN apt-get -q -y install m4 rsync git
RUN apt-get -q -y install ocaml-nox
RUN apt-get -q -y --no-install-recommends install opam aspcud
RUN apt-get -q -y clean

RUN adduser --disabled-password --gecos "CI" ci

COPY sudo-ci /etc/sudoers.d/ci
RUN  chmod 440 /etc/sudoers.d/ci

USER    ci
WORKDIR /home/ci

ENV OPAMYES     true
ENV OPAMVERBOSE 2
ENV OPAMJOBS    2

RUN opam init -a
RUN opam remote add coq-extra-dev https://coq.inria.fr/opam/extra-dev
RUN opam remote add coq-core-dev  https://coq.inria.fr/opam/core-dev
RUN opam remote add coq-released  https://coq.inria.fr/opam/released
RUN opam pin add coq 8.5.dev
RUN opam install coq-mathcomp-ssreflect.dev
RUN opam install coq-mathcomp-algebra.dev
RUN opam install coq-mathcomp-real_closed.dev

RUN rm -rf .opam/packages.dev/*
