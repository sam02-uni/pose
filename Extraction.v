From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlIntConv.
From Coq Require Import extraction.ExtrOcamlString.
From POSE Require Import Syntax.
From POSE Require Import Interp.
From POSE Require Import Parse.
From POSE Require Import Prettyprint.
From POSE Require Import Smt.

Extraction Language OCaml.

Extraction "./pose.ml" CObject compute step_at parse step_to_str step_to_smt.
