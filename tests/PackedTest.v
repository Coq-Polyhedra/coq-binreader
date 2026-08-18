(* -------------------------------------------------------------------- *)
Require Import PArray PrimString Uint63.
From BinReaderTest Require Import DataReady.
From BinReader Require Import BinReader.

Open Scope uint63_scope.
Open Scope array_scope.

(* -------------------------------------------------------------------- *)
LoadDataPacked "tests/tests.bin" As packed.

Definition packed_word (offset : int) : int :=
  let chunk := packed.[0] in
  PrimString.get chunk offset
    lor (PrimString.get chunk (offset + 1) << 8)
    lor (PrimString.get chunk (offset + 2) << 16)
    lor (PrimString.get chunk (offset + 3) << 24)
    lor (PrimString.get chunk (offset + 4) << 32)
    lor (PrimString.get chunk (offset + 5) << 40)
    lor (PrimString.get chunk (offset + 6) << 48)
    lor (PrimString.get chunk (offset + 7) << 56).

Goal PArray.length packed = 1.
Proof. vm_compute. reflexivity. Qed.

Goal PrimString.length packed.[0] = 54944.
Proof. vm_compute. reflexivity. Qed.

(* The unchanged file begins with the pair and array descriptor tags. *)
Goal packed_word 0 = 4.
Proof. vm_compute. reflexivity. Qed.

Goal packed_word 8 = 5.
Proof. vm_compute. reflexivity. Qed.
