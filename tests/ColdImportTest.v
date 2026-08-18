(* [DataReady] is empty: it orders the fixture generation without importing
   any of BinReader's logical dependencies. *)
From BinReaderTest Require Import DataReady.

(* Importing the plugin must not depend on clients having loaded [Uint63]
   first.  Coq may dynlink the plugin before replaying the wrapper library's
   own [Require] commands. *)
From BinReader Require Import BinReader.

LoadData "tests/tests.bin" As cold_legacy_data.
LoadDataPacked "tests/packed-int.bin" As cold_packed_data.

Goal True.
Proof. exact I. Qed.
