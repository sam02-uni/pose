From Coq Require Extraction.
From Coq Require Import extraction.ExtrHaskellBasic.
From Coq Require Import extraction.ExtrHaskellString.
From Coq Require Import extraction.ExtrHaskellNatInteger.
From BOSE Require Import Syntax.
From BOSE Require Import Interp.

Extraction Language Haskell.

Extraction "./bose.hs" CObject compute step_at.
