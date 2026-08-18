Require Import NArith PArray PrimString Uint63.
From Bignums Require Import BigN BigZ BigQ.
From BinReaderTest Require Import DataReady.
From BinReader Require Import BinReader.

Open Scope array_scope.
Open Scope bool_scope.
Open Scope pstring_scope.
Open Scope uint63_scope.

LoadDataPacked "tests/packed-int.bin" As int_bytes.
LoadDataPacked "tests/packed-n.bin" As n_bytes.
LoadDataPacked "tests/packed-z.bin" As z_bytes.
LoadDataPacked "tests/packed-q.bin" As q_bytes.
LoadDataPacked "tests/packed-pair.bin" As pair_bytes.
LoadDataPacked "tests/packed-array.bin" As array_bytes.
LoadDataPacked "tests/packed-empty-array.bin" As empty_array_bytes.
LoadDataPacked "tests/packed-n-boundaries.bin" As n_boundaries_bytes.
LoadDataPacked "tests/packed-record.bin" As record_bytes.
LoadDataPacked "tests/packed-empty-record.bin" As empty_record_bytes.
LoadDataPacked "tests/packed-array-too-large.bin" As large_array_bytes.
LoadDataPacked "tests/packed-array-truncated-max.bin" As truncated_max_array_bytes.
LoadDataPacked "tests/packed-bign-huge-count.bin" As huge_n_bytes.

Definition int_result := Packed.decode Packed.int63 int_bytes.

Goal int_result = Some 0x0102030405060708.
Proof. vm_compute. reflexivity. Qed.

Definition incremented_int :=
  Packed.map_schema (fun value => value + 1) Packed.int63.

Goal Packed.decode incremented_int int_bytes = Some 0x0102030405060709.
Proof. vm_compute. reflexivity. Qed.

Definition n_result_ok : bool :=
  match Packed.decode Packed.bigN n_bytes with
  | Some (BigN.N2 (WW (WW limb3 limb2) (WW limb1 limb0))) =>
    (limb0 =? 7) && (limb1 =? 11)
      && (limb2 =? 13) && (limb3 =? 0)
  | _ => false
  end.

Goal n_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition z_result_ok : bool :=
  match Packed.decode Packed.bigZ z_bytes with
  | Some (BigZ.Pos (BigN.N0 magnitude)) => magnitude =? 9
  | _ => false
  end.

Goal z_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition q_result_ok : bool :=
  match Packed.decode Packed.bigQ q_bytes with
  | Some (BigQ.Qq (BigZ.Neg (BigN.N0 numerator))
                  (BigN.N0 denominator)) =>
    (numerator =? 5) && (denominator =? 0)
  | _ => false
  end.

Goal q_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition pair_result_ok : bool :=
  match Packed.decode (Packed.pair Packed.int63 Packed.bigN) pair_bytes with
  | Some (first, BigN.N1 (WW high low)) =>
    (first =? 17) && (low =? 19) && (high =? 23)
  | _ => false
  end.

Goal pair_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition array_result_ok : bool :=
  match Packed.decode (Packed.array Packed.int63) array_bytes with
  | Some values =>
    (PArray.length values =? 2)
      && (values.[0] =? 3)
      && (values.[1] =? 4)
      && (values.[99] =? 42)
  | None => false
  end.

Goal array_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition empty_array_result_ok : bool :=
  match Packed.decode (Packed.array Packed.int63) empty_array_bytes with
  | Some values =>
    (PArray.length values =? 0) && (values.[99] =? 42)
  | None => false
  end.

Goal empty_array_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition n_boundaries_ok : bool :=
  match Packed.decode (Packed.array Packed.bigN) n_boundaries_bytes with
  | Some values =>
    match values.[0], values.[1], values.[2],
          values.[3], values.[4], values.[5] with
    | BigN.N6 _, BigN.N6 _,
      BigN.Nn O _, BigN.Nn O _, BigN.Nn O _, BigN.Nn (S O) _ => true
    | _, _, _, _, _, _ => false
    end
  | None => false
  end.

Goal n_boundaries_ok = true.
Proof. vm_compute. reflexivity. Qed.

Module M.
  Record point := mkpoint { px : int; py : BigZ.t }.
  Inductive empty : Type := mkempty.
End M.

Definition point_fields
    : Packed.fields M.point (int -> BigZ.t -> M.point) :=
  Packed.FField Packed.int63
    (Packed.FField Packed.bigZ Packed.FDone).

Definition point_schema : Packed.schema M.point :=
  Packed.record_schema "M.point" M.mkpoint point_fields.

Definition record_result_ok : bool :=
  match Packed.decode point_schema record_bytes with
  | Some value =>
    (M.px value =? 12)
      && BigZ.eqb (M.py value) (BigZ.Neg (BigN.N0 9))
  | None => false
  end.

Goal record_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition empty_record_schema : Packed.schema M.empty :=
  Packed.record_schema "M.empty" M.mkempty Packed.FDone.

Goal Packed.decode empty_record_schema empty_record_bytes = Some M.mkempty.
Proof. vm_compute. reflexivity. Qed.

(** Helpers for checking framing and arbitrary chunk boundaries. *)
Definition singleton (value : PrimString.string) : Packed.bytes :=
  PArray.make 1 value.

Definition split_once (input : Packed.bytes) (cut : int) : Packed.bytes :=
  let source := input.[0] in
  let result := PArray.make 2 Packed.empty_string in
  let result := result.[0 <- PrimString.sub source 0 cut] in
  result.[1 <- PrimString.sub source cut (PrimString.length source - cut)].

Definition int_decode_ok (input : Packed.bytes) : bool :=
  match Packed.decode Packed.int63 input with
  | Some value => value =? 0x0102030405060708
  | None => false
  end.

Definition split_step (state : int * bool) : int * bool :=
  let '(cut, valid) := state in
  (cut + 1, valid && int_decode_ok (split_once int_bytes cut)).

Definition all_int_splits_ok : bool :=
  snd (N.iter 15%N split_step (1, true)).

Goal all_int_splits_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition one_byte_step
    (state : int * Packed.bytes) : int * Packed.bytes :=
  let '(index, result) := state in
  let source := int_bytes.[0] in
  (index + 1, result.[index <- PrimString.sub source index 1]).

Definition int_one_byte_chunks : Packed.bytes :=
  snd (N.iter 16%N one_byte_step
    (0, PArray.make 16 Packed.empty_string)).

Goal int_decode_ok int_one_byte_chunks = true.
Proof. vm_compute. reflexivity. Qed.

Definition prefix (input : Packed.bytes) (length : int) : Packed.bytes :=
  singleton (PrimString.sub input.[0] 0 length).

Definition truncation_step (state : int * bool) : int * bool :=
  let '(length, valid) := state in
  let rejected :=
    match Packed.decode Packed.int63 (prefix int_bytes length) with
    | None => true
    | Some _ => false
    end
  in
  (length + 1, valid && rejected).

Definition all_int_truncations_rejected : bool :=
  snd (N.iter 16%N truncation_step (0, true)).

Goal all_int_truncations_rejected = true.
Proof. vm_compute. reflexivity. Qed.

Definition replace_byte (input : Packed.bytes) (index value : int)
    : Packed.bytes :=
  let source := input.[0] in
  let before := PrimString.sub source 0 index in
  let changed := PrimString.make 1 value in
  let after := PrimString.sub source (index + 1)
    (PrimString.length source - index - 1) in
  singleton (PrimString.cat before (PrimString.cat changed after)).

Definition high_tag := replace_byte int_bytes 7 128.
Definition high_scalar := replace_byte int_bytes 15 128.
Definition unknown_tag := replace_byte int_bytes 0 7.

Goal Packed.decode Packed.int63 high_tag = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.int63 high_scalar = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.int63 unknown_tag = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.bigN int_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Definition with_trailing_byte : Packed.bytes :=
  singleton (PrimString.cat int_bytes.[0] (PrimString.make 1 0)).

Definition with_trailing_word : Packed.bytes :=
  singleton (PrimString.cat int_bytes.[0] (PrimString.make 8 0)).

Goal Packed.decode Packed.int63 with_trailing_byte = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.int63 with_trailing_word = None.
Proof. vm_compute. reflexivity. Qed.

Definition leading_empty : Packed.bytes :=
  let result := PArray.make 2 Packed.empty_string in
  result.[1 <- int_bytes.[0]].

Definition interior_empty : Packed.bytes :=
  let source := int_bytes.[0] in
  let result := PArray.make 3 Packed.empty_string in
  let result := result.[0 <- PrimString.sub source 0 4] in
  result.[2 <- PrimString.sub source 4 12].

Definition trailing_empty : Packed.bytes :=
  let result := PArray.make 2 Packed.empty_string in
  result.[0 <- int_bytes.[0]].

Goal Packed.decode Packed.int63 leading_empty = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.int63 interior_empty = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.int63 trailing_empty = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode (Packed.array Packed.int63) large_array_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode (Packed.array Packed.int63) truncated_max_array_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.bigN huge_n_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Definition high_n_count := replace_byte n_bytes 15 128.
Definition high_n_limb := replace_byte n_bytes 23 128.
Definition high_z_sign := replace_byte z_bytes 15 128.

Goal Packed.decode Packed.bigN high_n_count = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.bigN high_n_limb = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.bigZ high_z_sign = None.
Proof. vm_compute. reflexivity. Qed.

Definition wrong_pair_child := replace_byte pair_bytes 16 0.

Goal Packed.decode (Packed.pair Packed.int63 Packed.bigN)
       wrong_pair_child = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode (Packed.pair Packed.int63 Packed.bigN)
       (prefix pair_bytes 40) = None.
Proof. vm_compute. reflexivity. Qed.

Definition wrong_array_element := replace_byte array_bytes 8 1.

Goal Packed.decode (Packed.array Packed.int63) wrong_array_element = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode (Packed.array Packed.int63)
       (prefix array_bytes 24) = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode (Packed.array Packed.int63)
       (prefix array_bytes 40) = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode Packed.bigQ (prefix q_bytes 32) = None.
Proof. vm_compute. reflexivity. Qed.

Definition wrong_point_schema : Packed.schema M.point :=
  Packed.record_schema "N.point" M.mkpoint point_fields.

Goal Packed.decode wrong_point_schema record_bytes = None.
Proof. vm_compute. reflexivity. Qed.

Definition wrong_record_count := replace_byte record_bytes 23 1.
Definition wrong_record_field := replace_byte record_bytes 39 3.

Goal Packed.decode point_schema wrong_record_count = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode point_schema wrong_record_field = None.
Proof. vm_compute. reflexivity. Qed.

Goal Packed.decode point_schema (prefix record_bytes 71) = None.
Proof. vm_compute. reflexivity. Qed.

Definition record_split_step (state : int * bool) : int * bool :=
  let '(cut, valid) := state in
  let accepted :=
    match Packed.decode point_schema (split_once record_bytes cut) with
    | Some value => (M.px value =? 12) && BigZ.eqb (M.py value) (-9)%bigZ
    | None => false
    end
  in
  (cut + 1, valid && accepted).

Definition all_record_splits_ok : bool :=
  snd (N.iter 78%N record_split_step (1, true)).

Goal all_record_splits_ok = true.
Proof. vm_compute. reflexivity. Qed.

Definition record_truncation_step (state : int * bool) : int * bool :=
  let '(length, valid) := state in
  let rejected :=
    match Packed.decode point_schema (prefix record_bytes length) with
    | None => true
    | Some _ => false
    end
  in
  (length + 1, valid && rejected).

Definition all_record_truncations_rejected : bool :=
  snd (N.iter 79%N record_truncation_step (0, true)).

Goal all_record_truncations_rejected = true.
Proof. vm_compute. reflexivity. Qed.

Definition record_one_byte_step
    (state : int * Packed.bytes) : int * Packed.bytes :=
  let '(index, result) := state in
  let source := record_bytes.[0] in
  (index + 1, result.[index <- PrimString.sub source index 1]).

Definition record_one_byte_chunks : Packed.bytes :=
  snd (N.iter 79%N record_one_byte_step
    (0, PArray.make 79 Packed.empty_string)).

Definition record_one_byte_chunks_ok : bool :=
  match Packed.decode point_schema record_one_byte_chunks with
  | Some value => (M.px value =? 12) && BigZ.eqb (M.py value) (-9)%bigZ
  | None => false
  end.

Goal record_one_byte_chunks_ok = true.
Proof. vm_compute. reflexivity. Qed.
