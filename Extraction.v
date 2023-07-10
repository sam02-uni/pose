From Coq Require Extraction.
From Coq Require Import extraction.ExtrHaskellBasic.
From Coq Require Import extraction.ExtrHaskellString.
From Coq Require Import extraction.ExtrHaskellNatInteger.
From POSE Require Import Syntax.
From POSE Require Import Interp.

Extraction Language Haskell.

Extraction "./pose.hs" CObject compute step_at.
