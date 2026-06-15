(* -------------------------------------------------------------------- *)
let () = assert (Sys.int_size = 63)

(* -------------------------------------------------------------------- *)
exception Malformed_data

(* -------------------------------------------------------------------- *)
type descr =
  | Int63
  | BigN
  | BigZ
  | BigQ
  | Pair of descr * descr
  | Array of descr
  | Record of string * descr list  (* qualified name + field descriptors *)

(* -------------------------------------------------------------------- *)
module BigNums : sig
  module N : sig
    val inlined : int

    val ctor : int -> string
  end
end = struct
  module C = Coqlib

  module N = struct
    let inlined : int = 7

    let ctor_name (i : int) =
      assert (0 <= i);
      "N" ^ if i < inlined then string_of_int i else "n"


    let ctor (i : int) = "bignums.N." ^ ctor_name i
  end

  let make_dir (components : string list) : Names.DirPath.t =
    Names.DirPath.make (List.rev_map Names.Id.of_string components)


  let () =
    let mp = [ "Coq"; "Numbers"; "Cyclic"; "Abstract"; "DoubleType" ] in
    let mp = Names.MPfile (make_dir mp) in
    let ty = Names.MutInd.make2 mp (Names.Label.make "zn2z"), 0 in

    C.register_ref "num.double.type" (Names.GlobRef.IndRef ty);
    C.register_ref "num.double.w0" (Names.GlobRef.ConstructRef (ty, 1));
    C.register_ref "num.double.ww" (Names.GlobRef.ConstructRef (ty, 2))


  let () =
    let mp = [ "Bignums"; "BigN"; "BigN" ] in
    let mp = Names.MPfile (make_dir mp) in
    let mp = Names.MPdot (mp, Names.Label.make "BigN") in
    let ind = Names.MutInd.make2 mp (Names.Label.make "t'"), 0 in
    let ty = Names.Constant.make2 mp (Names.Label.make "t") in

    for i = 0 to N.inlined do
      C.register_ref (N.ctor i) (Names.GlobRef.ConstructRef (ind, i + 1))
    done;
    C.register_ref "bignums.N.type" (Names.GlobRef.ConstRef ty)


  let () =
    let mp = [ "Bignums"; "BigZ"; "BigZ" ] in
    let mp = Names.MPfile (make_dir mp) in
    let mp = Names.MPdot (mp, Names.Label.make "BigZ") in
    let ind = Names.MutInd.make2 mp (Names.Label.make "t_"), 0 in
    let ty = Names.Constant.make2 mp (Names.Label.make "t") in

    C.register_ref "bignums.Z.pos" (Names.GlobRef.ConstructRef (ind, 1));
    C.register_ref "bignums.Z.neg" (Names.GlobRef.ConstructRef (ind, 2));
    C.register_ref "bignums.Z.type" (Names.GlobRef.ConstRef ty)


  let () =
    let mp = [ "Bignums"; "BigQ"; "BigQ" ] in
    let mp = Names.MPfile (make_dir mp) in
    let mp = Names.MPdot (mp, Names.Label.make "BigQ") in
    let ind = Names.MutInd.make2 mp (Names.Label.make "t_"), 0 in
    let ty = Names.Constant.make2 mp (Names.Label.make "t") in

    C.register_ref "bignums.Q.z" (Names.GlobRef.ConstructRef (ind, 1));
    C.register_ref "bignums.Q.q" (Names.GlobRef.ConstructRef (ind, 2));
    C.register_ref "bignums.Q.type" (Names.GlobRef.ConstRef ty)


  let () =
    let mp = Names.MPfile (make_dir [ "Coq"; "Array"; "PArray" ]) in
    let ty = Names.Constant.make2 mp (Names.Label.make "array") in

    C.register_ref "parray.type" (Names.GlobRef.ConstRef ty)
end

(* -------------------------------------------------------------------- *)
module Reader : sig
  type reader = in_channel

  val of_descr : reader -> descr -> Constr.t

  val descr_of_reader : reader -> descr

  val of_reader : reader -> descr * Constr.t * Constr.types
end = struct
  (* A sequence of little-endian 8-byte words, each fitting in a 63-bit int. *)
  type reader = in_channel

  let get_int63 (reader : reader) : int =
    let buf = Bytes.create 8 in
    try
      Stdlib.really_input reader buf 0 8;
      Int64.to_int (Bytes.get_int64_le buf 0)
    with
    | End_of_file -> raise Malformed_data


  (* A length word, then that many raw bytes (read directly, not as words). *)
  let get_string (reader : reader) : string =
    let len = get_int63 reader in
    if len < 0 then raise Malformed_data;
    let buf = Bytes.create len in
    (try Stdlib.really_input reader buf 0 len with
     | End_of_file -> raise Malformed_data);
    Bytes.to_string buf


  external fls : Uint63.t -> int = "fls_63"

  let c0 = Coqlib.lib_ref "num.nat.O"

  let cS = Coqlib.lib_ref "num.nat.S"

  let mk0 = Constr.mkRef (c0, UVars.Instance.empty)

  let mkS (arg : Constr.constr) =
    Constr.mkApp (Constr.mkRef (cS, UVars.Instance.empty), [| arg |])


  let nat_of_int : int -> Constr.t =
    let rec doit acc n = if n <= 0 then acc else doit (mkS acc) (n - 1) in
    fun n -> doit mk0 n


  let bigN_of_reader =
    let w0 = Constr.mkRef (Coqlib.lib_ref "num.double.w0", UVars.Instance.empty) in
    let ww = Constr.mkRef (Coqlib.lib_ref "num.double.ww", UVars.Instance.empty) in
    let int63 = Constr.mkRef (Coqlib.lib_ref "num.int63.type", UVars.Instance.empty) in
    let double = Constr.mkRef (Coqlib.lib_ref "num.double.type", UVars.Instance.empty) in
    let ctors =
      Array.init (BigNums.N.inlined + 1) (fun i ->
        let ctor = BigNums.N.ctor i in
        Constr.mkRef (Coqlib.lib_ref ctor, UVars.Instance.empty))
    in

    let rec mkword (n : int) =
      if n <= 0 then int63 else Constr.mkApp (double, [| mkword (n - 1) |])
    in

    let doit (reader : reader) : Constr.t =
      let length = ref (get_int63 reader) in
      let height = if !length = 0 then 0 else fls (Uint63.of_int (!length - 1)) in

      let get () : Uint63.t =
        let aout =
          if !length <= 0
          then 0
          else begin
            decr length;
            get_int63 reader
          end
        in
        Uint63.of_int aout
      in

      let rec doit (height : int) : Constr.t =
        if height <= 0
        then Constr.mkInt (get ())
        else if !length <= 0
        then Constr.mkApp (w0, [| mkword (height - 1) |])
        else (
          let lopart = doit (height - 1) in
          let hipart = doit (height - 1) in
          Constr.mkApp (ww, [| mkword (height - 1); hipart; lopart |]))
      in

      let aout = doit height in
      let ctor = ctors.(min height BigNums.N.inlined) in
      let args : Constr.t array =
        if height < BigNums.N.inlined
        then [| aout |]
        else [| nat_of_int (height - BigNums.N.inlined); aout |]
      in
      Constr.mkApp (ctor, args)
    in

    fun reader -> doit reader


  let bigZ_of_reader =
    let pos = Constr.mkRef (Coqlib.lib_ref "bignums.Z.pos", UVars.Instance.empty) in
    let neg = Constr.mkRef (Coqlib.lib_ref "bignums.Z.neg", UVars.Instance.empty) in

    let doit (reader : reader) =
      let is_nneg = get_int63 reader <> 0 in
      let bign = bigN_of_reader reader in
      let ctor = if is_nneg then pos else neg in
      Constr.mkApp (ctor, [| bign |])
    in

    fun reader -> doit reader


  let bigQ_of_reader =
    let q = Constr.mkRef (Coqlib.lib_ref "bignums.Q.q", UVars.Instance.empty) in

    let doit (reader : reader) =
      let num = bigZ_of_reader reader in
      let den = bigN_of_reader reader in
      Constr.mkApp (q, [| num; den |])
    in

    fun reader -> doit reader


  (* Resolve a record type's qualified name to its inductive and constructor
     arity. Requires a single-constructor, non-parameterized, monomorphic
     record. Memoized by name. *)
  let ind_of_name : string -> Names.inductive * int =
    let cache : (string, Names.inductive * int) Hashtbl.t = Hashtbl.create 17 in
    fun (name : string) ->
      match Hashtbl.find_opt cache name with
      | Some res -> res
      | None ->
        let fail msg =
          CErrors.user_err Pp.(str "binreader: " ++ str name ++ str ": " ++ str msg)
        in
        let gref =
          try Nametab.locate (Libnames.qualid_of_string name) with
          | Not_found -> fail "unknown reference"
        in
        let ind =
          match gref with
          | Names.GlobRef.IndRef ind -> ind
          | _ -> fail "not an inductive type"
        in
        let mib, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        if Array.length oib.Declarations.mind_consnames <> 1 then
          fail "not a single-constructor record";
        if mib.Declarations.mind_nparams <> 0 then
          fail "parameterized records are not supported";
        (match mib.Declarations.mind_universes with
         | Declarations.Monomorphic -> ()
         | Declarations.Polymorphic _ ->
           fail "universe-polymorphic records are not supported");
        let res = (ind, oib.Declarations.mind_consnrealargs.(0)) in
        Hashtbl.add cache name res;
        res


  let of_descr_ty =
    let int63 = Constr.mkRef (Coqlib.lib_ref "num.int63.type", UVars.Instance.empty) in
    let bigN = Constr.mkRef (Coqlib.lib_ref "bignums.N.type", UVars.Instance.empty) in
    let bigZ = Constr.mkRef (Coqlib.lib_ref "bignums.Z.type", UVars.Instance.empty) in
    let bigQ = Constr.mkRef (Coqlib.lib_ref "bignums.Q.type", UVars.Instance.empty) in
    let prod = Constr.mkRef (Coqlib.lib_ref "core.prod.type", UVars.Instance.empty) in
    let array =
      Constr.mkRef
        (Coqlib.lib_ref "parray.type", UVars.Instance.of_array ([||], [| Univ.Level.set |]))
    in

    let rec doit (descr : descr) =
      match descr with
      | Int63 -> int63
      | BigN -> bigN
      | BigZ -> bigZ
      | BigQ -> bigQ
      | Pair (d1, d2) -> Constr.mkApp (prod, [| doit d1; doit d2 |])
      | Array d -> Constr.mkApp (array, [| doit d |])
      | Record (name, _) ->
        let ind, _ = ind_of_name name in
        Constr.mkRef (Names.GlobRef.IndRef ind, UVars.Instance.empty)
    in
    fun descr -> doit descr


  let of_descr (reader : reader) =
    let pair = Constr.mkRef (Coqlib.lib_ref "core.prod.intro", UVars.Instance.empty) in

    let rec of_descr (descr : descr) : Constr.t =
      match descr with
      | Int63 -> of_int63 ()
      | BigN -> of_bigN ()
      | BigZ -> of_bigZ ()
      | BigQ -> of_bigQ ()
      | Pair (d1, d2) -> of_pair d1 d2
      | Array d -> of_array d
      | Record (name, fields) -> of_record name fields
    and of_int63 () : Constr.t = Constr.mkInt (Uint63.of_int (get_int63 reader))
    and of_bigN () : Constr.t = bigN_of_reader reader
    and of_bigZ () : Constr.t = bigZ_of_reader reader
    and of_bigQ () : Constr.t = bigQ_of_reader reader
    and of_pair (descr1 : descr) (descr2 : descr) : Constr.t =
      let v1 = of_descr descr1 in
      let v2 = of_descr descr2 in
      let t1 = of_descr_ty descr1 in
      let t2 = of_descr_ty descr2 in
      Constr.mkApp (pair, [| t1; t2; v1; v2 |])
    and of_array (descr : descr) : Constr.t =
      let length = get_int63 reader in

      if length > Sys.max_array_length then raise Malformed_data;

      let ty = of_descr_ty descr in
      let default = of_descr descr in
      let data = Array.init length (fun _ -> of_descr descr) in
      let u = UVars.Instance.of_array ([||], [| Univ.Level.set |]) in
      Constr.mkArray (u, data, default, ty)
    and of_record (name : string) (fields : descr list) : Constr.t =
      let ind, arity = ind_of_name name in
      if arity <> List.length fields then
        CErrors.user_err
          Pp.(str "binreader: " ++ str name ++ str ": expected "
              ++ int arity ++ str " field(s), descriptor provides "
              ++ int (List.length fields));
      (* Decode fields left to right (the stream is read in order). *)
      let rec read = function
        | [] -> []
        | d :: ds -> let v = of_descr d in v :: read ds
      in
      let args = Array.of_list (read fields) in
      let ctor =
        Constr.mkRef (Names.GlobRef.ConstructRef (ind, 1), UVars.Instance.empty)
      in
      Constr.mkApp (ctor, args)
    in

    fun descr -> of_descr descr


  let descr_of_reader (reader : reader) : descr =
    let rec doit () : descr =
      match get_int63 reader with
      | 0x00 -> Int63
      | 0x01 -> BigN
      | 0x02 -> BigZ
      | 0x03 -> BigQ
      | 0x04 ->
        let d1 = doit () in
        let d2 = doit () in
        Pair (d1, d2)
      | 0x05 -> Array (doit ())
      | 0x06 ->
        let name = get_string reader in
        let nfields = get_int63 reader in
        if nfields < 0 then raise Malformed_data;
        (* Read the field descriptors in order. *)
        let rec read n = if n <= 0 then [] else let d = doit () in d :: read (n - 1) in
        Record (name, read nfields)
      | _ -> raise Malformed_data
    in
    doit ()


  let of_reader (reader : reader) : descr * Constr.t * Constr.types =
    let descr = descr_of_reader reader in
    let term = of_descr reader descr in
    let ty = of_descr_ty descr in
    descr, term, ty
end

(* -------------------------------------------------------------------- *)
let load_data_from_file (filename : string) =
  let stream = open_in_bin filename in

  let aout =
    try Reader.of_reader stream with
    | e ->
      close_in stream;
      raise e
  in
  close_in stream;
  aout


(* -------------------------------------------------------------------- *)
let load_and_define_data_from_file (filename : string) (x : Names.Id.t) =
  let _, c, ty = load_data_from_file filename in

  let (_ : Names.Constant.t) =
    Declare.declare_constant
      ~name:x
      ~kind:Decls.(IsDefinition Definition)
      (Declare.DefinitionEntry (Declare.definition_entry ~types:ty c))
  in
  ()
