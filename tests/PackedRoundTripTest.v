Require Import PArray PrimString Uint63.
From Bignums Require Import BigN BigZ BigQ.
From BinReaderTest Require Import DataReady.
From BinReader Require Import BinReader.

Open Scope array_scope.
Open Scope bool_scope.
Open Scope pstring_scope.
Open Scope uint63_scope.

(** The legacy mixed fixture covers right-associated pairs, two levels of
    arrays, Int63, BigZ, and a 129766-digit BigN. *)
LoadDataPacked "tests/tests.bin" As mixed_bytes.

Definition mixed_schema :=
  Packed.pair
    (Packed.array (Packed.array Packed.int63))
    (Packed.pair Packed.bigZ Packed.bigN).

Definition mixed_shape_and_values : bool :=
  match Packed.decode mixed_schema mixed_bytes with
  | Some (arrays, (integer, natural)) =>
    (PArray.length arrays =? 2)
      && (PArray.length arrays.[0] =? 3)
      && (PArray.length arrays.[1] =? 2)
      && (arrays.[0].[0] =? 1)
      && (arrays.[0].[1] =? 2)
      && (arrays.[0].[2] =? 3)
      && (arrays.[1].[0] =? 5)
      && (arrays.[1].[1] =? 6)
      && (PArray.length arrays.[99] =? 1)
      && (arrays.[99].[0] =? 0)
      && BigZ.eqb integer (-1038963763560376314237534543)%bigZ
      && BigN.eqb (BigN.modulo natural 1000003) 890696
      && BigN.even natural
  | None => false
  end.

Goal mixed_shape_and_values = true.
Proof. vm_compute. reflexivity. Qed.

(** A standalone rational verifies the ordinary nonzero-denominator path. *)
LoadDataPacked "tests/bigq.bin" As rational_bytes.

Definition rational_ok : bool :=
  match Packed.decode Packed.bigQ rational_bytes with
  | Some value => BigQ.eqb value (BigQ.Qq 22%bigZ 7%bigN)
  | None => false
  end.

Goal rational_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** The wire descriptor calls this record [point].  Packed decoding uses the
    statically supplied constructor while still validating that encoded name. *)
Record packed_point := mk_packed_point { point_x : int; point_y : BigZ.t }.

Definition packed_point_fields
    : Packed.fields packed_point (int -> BigZ.t -> packed_point) :=
  Packed.FField Packed.int63
    (Packed.FField Packed.bigZ Packed.FDone).

Definition packed_point_schema : Packed.schema packed_point :=
  Packed.record_schema "point" mk_packed_point packed_point_fields.

LoadDataPacked "tests/record.bin" As points_bytes.

Definition points_schema :=
  Packed.pair packed_point_schema (Packed.array packed_point_schema).

Definition points_ok : bool :=
  match Packed.decode points_schema points_bytes with
  | Some (point, points) =>
    (point_x point =? 7)
      && BigZ.eqb (point_y point) (-3)%bigZ
      && (PArray.length points =? 2)
      && (point_x points.[0] =? 1)
      && BigZ.eqb (point_y points.[0]) 1%bigZ
      && (point_x points.[1] =? 2)
      && BigZ.eqb (point_y points.[1]) (-2)%bigZ
      && (point_x points.[99] =? 0)
      && BigZ.eqb (point_y points.[99]) 0%bigZ
  | None => false
  end.

Goal points_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** This one-megabyte fixture combines an unaligned record name, an array of
    records, a large payload, and a noncanonical observable array default.
    Packed chunk boundaries are exercised exhaustively in PackedSchemasTest. *)
Record boundary_point := mk_boundary_point { boundary_x : int }.

Definition boundary_fields
    : Packed.fields boundary_point (int -> boundary_point) :=
  Packed.FField Packed.int63 Packed.FDone.

Definition boundary_schema : Packed.schema boundary_point :=
  Packed.record_schema "point" mk_boundary_point boundary_fields.

LoadDataPacked "tests/buffer-boundary.bin" As boundary_bytes.

Definition boundary_values_and_default_ok : bool :=
  match Packed.decode (Packed.array boundary_schema) boundary_bytes with
  | Some points =>
    (PArray.length points =? 131073)
      && (boundary_x points.[0] =? 0)
      && (boundary_x points.[65536] =? 65536)
      && (boundary_x points.[131072] =? 131072)
      && (boundary_x points.[999999] =? 424242)
  | None => false
  end.

Goal boundary_values_and_default_ok = true.
Proof. vm_compute. reflexivity. Qed.
