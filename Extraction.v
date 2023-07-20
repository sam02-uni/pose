From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlIntConv.
From Coq Require Import extraction.ExtrOcamlNativeString.
From POSE Require Import Syntax.
From POSE Require Import SemanticsTypes.
From POSE Require Import Interp.
From POSE Require Import Parse.
From POSE Require Import Prettyprint.
From POSE Require Import Smt.

Extraction Language OCaml.

Extraction "./pose.ml" CObject config_initial step_c compute step_at is_leaf parse step_to_dstr step_to_dsmt.
