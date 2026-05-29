(* -------------------------------------------------------------------- *)
(* -------- *) Require Import PArray Uint63.
From Bignums   Require Import BigN BigZ BigQ.
From BinReader Require Import BinReader.

(* -------------------------------------------------------------------- *)
Time LoadData "tests/tests.bin" As data.

(* -------------------------------------------------------------------- *)
Eval compute in data.

(* --------------------------------------------------------------------
 * Value-level checks. The data is decoded from tests/tests.bin, which is
 * produced independently by scripts/binreader.py from tests/tests.json.
 * These assertions pin the decoded values, so the test fails (coqc errors)
 * on any encode/decode mismatch, not merely on a type error. The expected
 * values mirror tests/tests.json:
 *   data : array (array int) * (bigZ * bigN)
 *        = ([| [|1;2;3|]; [|5;6|] |], (z, n))
 *   z = -1038963763560376314237534543
 *   n = <129766-digit integer>  (checked via a decode-sensitive fingerprint)
 * -------------------------------------------------------------------- *)

Definition arrs := fst data.
Definition z    := fst (snd data).
Definition n    := snd (snd data).

(* Shape of the outer/inner arrays. *)
Goal PArray.length arrs = 2%uint63.        Proof. reflexivity. Qed.
Goal PArray.length (arrs.[0]) = 3%uint63.  Proof. reflexivity. Qed.
Goal PArray.length (arrs.[1]) = 2%uint63.  Proof. reflexivity. Qed.

(* Exact int63 contents of the inner arrays. *)
Goal (arrs.[0]).[0] = 1%uint63. Proof. reflexivity. Qed.
Goal (arrs.[0]).[1] = 2%uint63. Proof. reflexivity. Qed.
Goal (arrs.[0]).[2] = 3%uint63. Proof. reflexivity. Qed.
Goal (arrs.[1]).[0] = 5%uint63. Proof. reflexivity. Qed.
Goal (arrs.[1]).[1] = 6%uint63. Proof. reflexivity. Qed.

(* The BigZ component, exact (small enough to spell out). *)
Goal BigZ.eqb z (-1038963763560376314237534543)%bigZ = true.
Proof. vm_compute. reflexivity. Qed.

(* The BigN component is 129766 digits, too large for a literal. Pin it via
 * a modular fingerprint (touches every limb) plus its parity. A wrong-limb
 * decode would change the residue. Reference values from tests.json:
 *   n mod 1000003 = 890696   and   n is even. *)
Goal BigN.eqb (BigN.modulo n 1000003) 890696 = true.
Proof. vm_compute. reflexivity. Qed.

Goal BigN.even n = true.
Proof. vm_compute. reflexivity. Qed.
