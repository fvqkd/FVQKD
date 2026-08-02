(* -------------------------------------------------------------------- *)
(* exports.v — Re-export the eur module                                 *)
(* -------------------------------------------------------------------- *)
(* Module: eur.exports                                    *)
(*                                                                       *)
(* One-liner import surface for the EUR module. Downstream              *)
(* consumers use:                                                        *)
(*   From eur Require Import exports.                      *)
(* -------------------------------------------------------------------- *)
From eur Require Export def.
From eur Require Export prop.
From eur Require Export eur.
