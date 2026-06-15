(* -------------------------------------------------------------------- *)
(* -------- *) Require Import PArray Uint63.
From Bignums   Require Import BigN BigZ BigQ.
From BinReader Require Import BinReader.

(* -------------------------------------------------------------------- *)
(* The record must be in scope (by the name used in the descriptor) when
 * LoadData runs: its qualified name is resolved against the live name
 * table. Real users would [Require Import] the module defining it. *)
Record point := mkpoint { px : int; py : BigZ.t }.

(* --------------------------------------------------------------------
 * tests/record.bin is produced independently by scripts/binreader.py from
 * tests/record.json, with descriptor ({point|px:I,py:Z},[{point|px:I,py:Z}])
 * and data:
 *   ( {px=7;  py=-3},  [ {px=1; py=1}; {px=2; py=-2} ] )
 * so the decoded value has type  point * array point.
 * -------------------------------------------------------------------- *)
LoadData "tests/record.bin" As rdata.

Eval compute in rdata.

Definition r  := fst rdata.   (* a bare record       *)
Definition rs := snd rdata.   (* an array of records *)

(* Fields of the bare record. *)
Goal px r = 7%uint63.                          Proof. reflexivity. Qed.
Goal BigZ.eqb (py r) (-3)%bigZ = true.         Proof. vm_compute. reflexivity. Qed.

(* Array-of-records composition: shape and per-element field values. *)
Goal PArray.length rs = 2%uint63.              Proof. reflexivity. Qed.
Goal px (rs.[0]) = 1%uint63.                   Proof. reflexivity. Qed.
Goal px (rs.[1]) = 2%uint63.                   Proof. reflexivity. Qed.
Goal BigZ.eqb (py (rs.[0])) 1%bigZ = true.     Proof. vm_compute. reflexivity. Qed.
Goal BigZ.eqb (py (rs.[1])) (-2)%bigZ = true.  Proof. vm_compute. reflexivity. Qed.
