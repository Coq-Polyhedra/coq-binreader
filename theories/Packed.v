Require Import DoubleType NArith PArray PrimString Uint63.
From Bignums Require Import BigN BigZ BigQ.

Open Scope array_scope.
Open Scope uint63_scope.

(** A packed certificate is the unchanged binary file split into primitive
    strings by [LoadDataPacked].  The cursor caches the current chunk so the
    common, within-chunk word read does not repeatedly index the outer array. *)
Definition bytes := PArray.array PrimString.string.

Record cursor := Cursor {
  cursor_chunk : int;
  cursor_offset : int;
  cursor_data : PrimString.string
}.

Definition empty_string : PrimString.string := PrimString.make 0 0.

Definition start (input : bytes) : option cursor :=
  let count := PArray.length input in
  if count =? 0 then Some (Cursor 0 0 empty_string)
  else
    let chunk := input.[0] in
    if PrimString.length chunk =? 0 then None
    else Some (Cursor 0 0 chunk).

Definition next_chunk (input : bytes) (index : int) : option cursor :=
  let next := index + 1 in
  let count := PArray.length input in
  if next <? count then
    let chunk := input.[next] in
    if PrimString.length chunk =? 0 then None
    else Some (Cursor next 0 chunk)
  else if next =? count then Some (Cursor next 0 empty_string)
  else None.

Definition at_end (input : bytes) (position : cursor) : bool :=
  (cursor_chunk position =? PArray.length input)
    && (cursor_offset position =? 0).

Definition decoder (A : Type) := bytes -> cursor -> option (A * cursor).

Definition decoder_return {A : Type} (value : A) : decoder A :=
  fun _ position => Some (value, position).

Definition decoder_bind {A B : Type}
    (first : decoder A) (next : A -> decoder B) : decoder B :=
  fun input position =>
    match first input position with
    | Some (value, position') => next value input position'
    | None => None
    end.

Definition decoder_map {A B : Type}
    (convert : A -> B) (source : decoder A) : decoder B :=
  decoder_bind source (fun value => decoder_return (convert value)).

Definition decoder_pair {A B : Type}
    (first : decoder A) (second : decoder B) : decoder (A * B) :=
  decoder_bind first (fun value1 =>
    decoder_bind second (fun value2 =>
      decoder_return (value1, value2))).

(** Convert an int63 to binary [N], stopping at its most significant bit.
    [Uint63.to_Z] always performs 63 recursive steps, which is expensive for
    the many short array lengths occurring in nested certificate layouts. *)
Fixpoint uint63_to_N_aux (fuel : nat) (value : int) : N :=
  if value =? 0 then 0%N
  else
    match fuel with
    | O => 0%N
    | S fuel' =>
      let high := uint63_to_N_aux fuel' (value >> 1) in
      if value land 1 =? 0 then N.double high else N.succ_double high
    end.

Definition uint63_to_N (value : int) : N :=
  uint63_to_N_aux 63%nat value.

(** Consume one byte.  Empty chunks are rejected rather than treated as
    padding; [LoadDataPacked] never emits them in a nonempty file. *)
Definition read_byte (input : bytes) (position : cursor)
    : option (int * cursor) :=
  if cursor_chunk position <? PArray.length input then
    let offset := cursor_offset position in
    let chunk := cursor_data position in
    let length := PrimString.length chunk in
    if offset <? length then
      let value := PrimString.get chunk offset in
      let offset' := offset + 1 in
      if offset' =? length then
        match next_chunk input (cursor_chunk position) with
        | Some position' => Some (value, position')
        | None => None
        end
      else Some (value, Cursor (cursor_chunk position) offset' chunk)
    else None
  else None.

Definition word_of_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 : int) : int :=
  b0
    lor (b1 << 8)
    lor (b2 << 16)
    lor (b3 << 24)
    lor (b4 << 32)
    lor (b5 << 40)
    lor (b6 << 48)
    lor (b7 << 56).

(** Rare path for a word straddling two chunks. *)
Definition read_word_slow (input : bytes) (position : cursor)
    : option (int * cursor) :=
  match read_byte input position with
  | Some (b0, p1) =>
    match read_byte input p1 with
    | Some (b1, p2) =>
      match read_byte input p2 with
      | Some (b2, p3) =>
        match read_byte input p3 with
        | Some (b3, p4) =>
          match read_byte input p4 with
          | Some (b4, p5) =>
            match read_byte input p5 with
            | Some (b5, p6) =>
              match read_byte input p6 with
              | Some (b6, p7) =>
                match read_byte input p7 with
                | Some (b7, p8) =>
                  if b7 <? 128
                  then Some (word_of_bytes b0 b1 b2 b3 b4 b5 b6 b7, p8)
                  else None
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

(** Read a little-endian 63-bit word.  The eighth byte is checked before it
    is shifted: uint63 arithmetic would otherwise silently discard bit 63. *)
Definition read_word (input : bytes) (position : cursor)
    : option (int * cursor) :=
  if cursor_chunk position <? PArray.length input then
    let chunk := cursor_data position in
    let offset := cursor_offset position in
    let length := PrimString.length chunk in
    if offset <=? length then
      let available := length - offset in
      if 8 <=? available then
        let b0 := PrimString.get chunk offset in
        let b1 := PrimString.get chunk (offset + 1) in
        let b2 := PrimString.get chunk (offset + 2) in
        let b3 := PrimString.get chunk (offset + 3) in
        let b4 := PrimString.get chunk (offset + 4) in
        let b5 := PrimString.get chunk (offset + 5) in
        let b6 := PrimString.get chunk (offset + 6) in
        let b7 := PrimString.get chunk (offset + 7) in
        if b7 <? 128 then
          let offset' := offset + 8 in
          let value := word_of_bytes b0 b1 b2 b3 b4 b5 b6 b7 in
          if offset' =? length then
            match next_chunk input (cursor_chunk position) with
            | Some position' => Some (value, position')
            | None => None
            end
          else Some (value, Cursor (cursor_chunk position) offset' chunk)
        else None
      else read_word_slow input position
    else None
  else None.

Definition expect_word (expected : int) : decoder unit :=
  fun input position =>
    match read_word input position with
    | Some (actual, position') =>
      if actual =? expected then Some (tt, position') else None
    | None => None
    end.

(** Compare an encoded length-prefixed byte string with a statically known
    primitive string, without allocating a copy of the encoded name. *)
Definition string_step (input : bytes) (expected : PrimString.string)
    (state : option (int * cursor)) : option (int * cursor) :=
  match state with
  | Some (index, position) =>
    match read_byte input position with
    | Some (actual, position') =>
      if actual =? PrimString.get expected index
      then Some (index + 1, position')
      else None
    | None => None
    end
  | None => None
  end.

Definition expect_string (expected : PrimString.string) : decoder unit :=
  fun input position =>
    match read_word input position with
    | Some (length, position') =>
      if length =? PrimString.length expected then
        let count := uint63_to_N length in
        match N.iter count (string_step input expected) (Some (0, position')) with
        | Some (_, position'') => Some (tt, position'')
        | None => None
        end
      else None
    | None => None
    end.

(** The expected descriptor is statically typed by [schema] below.  It is
    checked directly against the stream; no dynamic untyped value is built. *)
Inductive descriptor : Type :=
| DInt63
| DBigN
| DBigZ
| DBigQ
| DPair (first second : descriptor)
| DArray (element : descriptor)
| DRecord (name : PrimString.string) (fields : descriptors)
with descriptors : Type :=
| DNil
| DCons (field : descriptor) (fields : descriptors).

Fixpoint expect_descriptor (expected : descriptor) (input : bytes)
    (position : cursor) : option cursor :=
  match expected with
  | DInt63 =>
    match expect_word 0 input position with
    | Some (_, position') => Some position'
    | None => None
    end
  | DBigN =>
    match expect_word 1 input position with
    | Some (_, position') => Some position'
    | None => None
    end
  | DBigZ =>
    match expect_word 2 input position with
    | Some (_, position') => Some position'
    | None => None
    end
  | DBigQ =>
    match expect_word 3 input position with
    | Some (_, position') => Some position'
    | None => None
    end
  | DPair first second =>
    match expect_word 4 input position with
    | Some (_, position1) =>
      match expect_descriptor first input position1 with
      | Some position2 => expect_descriptor second input position2
      | None => None
      end
    | None => None
    end
  | DArray element =>
    match expect_word 5 input position with
    | Some (_, position1) => expect_descriptor element input position1
    | None => None
    end
  | DRecord name fields =>
    match expect_word 6 input position with
    | Some (_, position1) =>
      match expect_string name input position1 with
      | Some (_, position2) =>
        match read_word input position2 with
        | Some (count, position3) =>
          expect_descriptors fields count input position3
        | None => None
        end
      | None => None
      end
    | None => None
    end
  end
with expect_descriptors (expected : descriptors) (count : int)
    (input : bytes) (position : cursor) : option cursor :=
  match expected with
  | DNil => if count =? 0 then Some position else None
  | DCons field fields =>
    if count =? 0 then None
    else
      match expect_descriptor field input position with
      | Some position' =>
        expect_descriptors fields (count - 1) input position'
      | None => None
      end
  end.

(** A leaf decoder used by the balanced BigN tree builder.  The remaining
    count is the number of 63-bit limbs, not the number of tree leaves. *)
Definition tree_leaf (W : Set) :=
  bytes -> int -> cursor -> option (W * (int * cursor)).

Definition read_limb : tree_leaf int :=
  fun input remaining position =>
    if remaining =? 0 then Some (0, (0, position))
    else
      match read_word input position with
      | Some (value, position') =>
        Some (value, (remaining - 1, position'))
      | None => None
      end.

(** Build a [word W height] by reading the low subtree before the high
    subtree, exactly as the OCaml loader does.  A wholly unused subtree is
    represented by its compact [W0] constructor. *)
Fixpoint read_tree (W : Set) (zero : W) (leaf : tree_leaf W)
    (height : nat) :
    bytes -> int -> cursor -> option (word W height * (int * cursor)) :=
  match height as height'
        return bytes -> int -> cursor ->
          option (word W height' * (int * cursor)) with
  | O => fun input remaining position =>
    if remaining =? 0
    then Some (zero, (remaining, position))
    else leaf input remaining position
  | S height' => fun input remaining position =>
    if remaining =? 0 then Some (W0, (remaining, position))
    else
      match read_tree W zero leaf height' input remaining position with
      | Some (low, (remaining1, position1)) =>
        match read_tree W zero leaf height' input remaining1 position1 with
        | Some (high, (remaining2, position2)) =>
          Some (WW high low, (remaining2, position2))
        | None => None
        end
      | None => None
      end
  end.

Definition read_w6 : tree_leaf BigN.w6 :=
  fun input remaining position =>
    read_tree int 0 read_limb 6%nat input remaining position.

(** [ceil_log2 n], with fixed fuel because an int63 needs at most 63
    halvings.  [(n >> 1) + (n land 1)] avoids overflow at [2^63-1]. *)
Fixpoint ceil_log2_aux (fuel : nat) (value : int) : option nat :=
  if value <=? 1 then Some O
  else
    match fuel with
    | O => None
    | S fuel' =>
      let half := (value >> 1) + (value land 1) in
      match ceil_log2_aux fuel' half with
      | Some height => Some (S height)
      | None => None
      end
    end.

Definition read_bigN : decoder BigN.t :=
  fun input position =>
    match read_word input position with
    | Some (limbs, position') =>
      match ceil_log2_aux 63%nat limbs with
      | Some O =>
        match read_tree int 0 read_limb 0%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N0 value, position'')
          else None
        | None => None
        end
      | Some (S O) =>
        match read_tree int 0 read_limb 1%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N1 value, position'')
          else None
        | None => None
        end
      | Some (S (S O)) =>
        match read_tree int 0 read_limb 2%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N2 value, position'')
          else None
        | None => None
        end
      | Some (S (S (S O))) =>
        match read_tree int 0 read_limb 3%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N3 value, position'')
          else None
        | None => None
        end
      | Some (S (S (S (S O)))) =>
        match read_tree int 0 read_limb 4%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N4 value, position'')
          else None
        | None => None
        end
      | Some (S (S (S (S (S O))))) =>
        match read_tree int 0 read_limb 5%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N5 value, position'')
          else None
        | None => None
        end
      | Some (S (S (S (S (S (S O)))))) =>
        match read_tree int 0 read_limb 6%nat input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.N6 value, position'')
          else None
        | None => None
        end
      | Some (S (S (S (S (S (S (S height))))))) =>
        match read_tree BigN.w6 W0 read_w6 (S height)
                input limbs position' with
        | Some (value, (remaining, position'')) =>
          if remaining =? 0
          then Some (BigN.Nn height value, position'')
          else None
        | None => None
        end
      | None => None
      end
    | None => None
    end.

Definition read_bigZ : decoder BigZ.t :=
  fun input position =>
    match read_word input position with
    | Some (sign, position') =>
      match read_bigN input position' with
      | Some (magnitude, position'') =>
        if sign =? 0
        then Some (BigZ.Neg magnitude, position'')
        else Some (BigZ.Pos magnitude, position'')
      | None => None
      end
    | None => None
    end.

Definition read_bigQ : decoder BigQ.t :=
  decoder_bind read_bigZ (fun numerator =>
    decoder_bind read_bigN (fun denominator =>
      decoder_return (BigQ.Qq numerator denominator))).

Record array_state (A : Type) := ArrayState {
  array_index : int;
  array_value : PArray.array A;
  array_position : cursor
}.

Arguments ArrayState {A} _ _ _.

Definition array_step {A : Type} (element : decoder A) (input : bytes)
    (state : array_state A) : option (array_state A) :=
  match element input (array_position A state) with
  | Some (value, position') =>
    Some (ArrayState
      (array_index A state + 1)
      ((array_value A state).[array_index A state <- value])
      position')
  | None => None
  end.

(** Repeat [array_step] in a binary divide-and-conquer traversal.  Unlike
    [N.iter] over an option state, this returns immediately after a malformed
    element instead of executing the remaining iterations on [None]. *)
Fixpoint array_fill_positive {A : Type} (element : decoder A) (input : bytes)
    (count : positive) (state : array_state A) : option (array_state A) :=
  match count with
  | xH => array_step element input state
  | xO count' =>
    match array_fill_positive element input count' state with
    | Some state' => array_fill_positive element input count' state'
    | None => None
    end
  | xI count' =>
    match array_fill_positive element input count' state with
    | Some state' =>
      match array_fill_positive element input count' state' with
      | Some state'' => array_step element input state''
      | None => None
      end
    | None => None
    end
  end.

Definition array_fill {A : Type} (element : decoder A) (input : bytes)
    (count : N) (state : array_state A) : option (array_state A) :=
  match count with
  | N0 => Some state
  | Npos count' => array_fill_positive element input count' state
  end.

Definition read_array {A : Type} (element : decoder A)
    : decoder (PArray.array A) :=
  fun input position =>
    match read_word input position with
    | Some (length, position1) =>
      if length <=? PArray.max_length then
        match element input position1 with
        | Some (default, position2) =>
          let value := PArray.make length default in
          if PArray.length value =? length then
            let count := uint63_to_N length in
            match array_fill element input count
                    (ArrayState 0 value position2) with
            | Some state =>
              Some (array_value A state, array_position A state)
            | None => None
            end
          else None
        | None => None
        end
      else None
    | None => None
    end.

Record schema (A : Type) := Schema {
  schema_descriptor : descriptor;
  schema_value : decoder A
}.

Arguments Schema {A} _ _.
Arguments schema_descriptor {A} _.
Arguments schema_value {A} _.

Definition int63 : schema int := Schema DInt63 read_word.
Definition bigN : schema BigN.t := Schema DBigN read_bigN.
Definition bigZ : schema BigZ.t := Schema DBigZ read_bigZ.
Definition bigQ : schema BigQ.t := Schema DBigQ read_bigQ.

Definition map_schema {A B : Type} (convert : A -> B)
    (source : schema A) : schema B :=
  Schema (schema_descriptor source)
    (decoder_map convert (schema_value source)).

Definition pair {A B : Type} (first : schema A) (second : schema B)
    : schema (A * B) :=
  Schema (DPair (schema_descriptor first) (schema_descriptor second))
    (decoder_pair (schema_value first) (schema_value second)).

Definition array {A : Type} (element : schema A)
    : schema (PArray.array A) :=
  Schema (DArray (schema_descriptor element))
    (read_array (schema_value element)).

(** A typed sequence of record fields.  [fields R F] describes how to turn
    a curried constructor of type [F] into a value of type [R].  Values are
    applied as they are decoded, so arrays of records do not allocate a
    temporary heterogeneous tuple for every element. *)
Inductive fields (R : Type) : Type -> Type :=
| FDone : fields R R
| FField : forall A F, schema A -> fields R F -> fields R (A -> F).

Arguments FDone {R}.
Arguments FField {R A F} _ _.

Fixpoint field_descriptors {R F : Type} (specification : fields R F)
    : descriptors :=
  match specification with
  | FDone => DNil
  | FField field rest =>
    DCons (schema_descriptor field) (field_descriptors rest)
  end.

Fixpoint read_fields {R F : Type} (specification : fields R F)
    : F -> decoder R :=
  match specification in fields _ F'
        return F' -> decoder R with
  | FDone => fun value => decoder_return value
  | @FField _ A F' field rest => fun constructor =>
    decoder_bind (schema_value field) (fun value =>
      read_fields rest (constructor value))
  end.

Definition record_with {R : Type} (name : PrimString.string)
    (field_types : descriptors) (read_value : decoder R) : schema R :=
  Schema (DRecord name field_types) read_value.

Definition record_schema {R F : Type} (name : PrimString.string)
    (constructor : F) (specification : fields R F) : schema R :=
  record_with name (field_descriptors specification)
    (read_fields specification constructor).

(** Validate the expected descriptor, decode one value, and require exact
    end-of-file.  This is the entry point intended for checker definitions. *)
Definition decode {A : Type} (expected : schema A) (input : bytes)
    : option A :=
  match start input with
  | Some position0 =>
    match expect_descriptor (schema_descriptor expected) input position0 with
    | Some position1 =>
      match schema_value expected input position1 with
      | Some (value, position2) =>
        if at_end input position2 then Some value else None
      | None => None
      end
    | None => None
    end
  | None => None
  end.
