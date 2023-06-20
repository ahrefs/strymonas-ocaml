#use "topfind";;
#require "strymonas";;
(* #directory ".";; *)
#load "tt.cmo";;
open Tt

let pr fmt = Printf.ksprintf print_endline fmt
let print_list l = List.iter (Printf.printf "%d ") l; print_newline ()
let show_code code =
  (* BUG format_code doesn't close all boxes so format to string and print that *)
  format_code Format.str_formatter @@ close_code code;
  print_endline @@ Format.flush_str_formatter ()

module Merge(C:module type of Cde_ex) = struct
  include Stream_cooked_fn.Make(C)
  let my_merge (t1,t2) = Raw.merge_raw (fun a b -> C.(a < b)) (of_arr t1) (of_arr t2)
end

let a () =
  let module C = Backends.C in
  let open Merge(C) in
  let test x = my_merge x |> sum_int in
  C.print_two_array "test" Format.std_formatter (C.tint, C.tint) test

let b () =
  let module C = Backends.MetaOCamlExt in
  let open Merge(C) in
  let to_list l = l |> fold (fun l x -> C.cons x l) (C.nil ()) |> C.cde_app1 .<List.rev>. in
  let test_fn = C.two_arg_fun (fun x -> my_merge x |> to_list) in
  let fn = Runcode.run test_fn in
  let a = [|1;3;10;11|] in
  let b = [|2;4;5;12;13|] in
  pr "\napplying";
  show_code test_fn;
  pr "to";
  print_list @@ Array.to_list a;
  print_list @@ Array.to_list b;
  print_string "result: ";
  print_list @@ fn (a,b)

(*
let _var () =
  let empty = of_arr @@ C.inj .<[||]>. in
  let sum_ l = List.fold_left (fun acc coef -> .<coef + .~acc>.) .<0>. l in
  let sum_ l =
    let rec loop acc l =
      match l with
      | [] -> acc
(*       | x::t -> loop t (fun acc -> k (acc + x)) *)
(*       k (fun acc -> .<fun v -> .~(loop .<v * x + .~acc>. t) >. *)
      | x :: t -> .<fun v -> .~(loop .<v * x + .~acc>. t) >.
    in
    loop .<0>. l
  in
(*
  let sum_ l =
    let rec loop l k : int -> 'a =
      match l with
      | [] -> k Fun.id
(*       | x::t -> loop l .< fun v -> .~(k .< v * x + 13 >.) >. *)
      k (fun acc -> .<fun v -> .~(loop .<v * x + .~acc>. t) >.
    in
    loop l
  in
*)
(*
  sum_ [1;2;3] => fun a -> fun b -> (fun c k -> k (3*c) (fun a -> 1*a) + 2*b + 3*c))
  sum_ [] = fun k -> k 0
  sum_ [1] = fun x -> (fun k -> k (1*x + 0))
  sum_ [1;2] = fun y -> fun x -> k (1*x + k (2*y + 0))
*)
(*   show_code @@ sum_ [1;2;3;4]; *)
  let f = sum_ [1;2;3;4] in
  show_code f;
  ()
*)

let lift_elements l = List.map (fun x -> .<x>.) l
let docstream a = let l = ref (Array.to_list a) in DocStream.create (fun () -> match !l with [] -> None | h::t -> l := t; Some h)
let doc_ids = List.map (fun d -> d.Doc.doc_id)
let docs1 = Array.init 10 (fun i -> Doc.{ doc_id = i*4; score = float_of_int i })
let docs2 = Array.init 10 (fun i -> Doc.{ doc_id = 10+i*2; score = float_of_int i })
let docs3 = Array.init 10 (fun i -> Doc.{ doc_id = 5+i*3; score = float_of_int i })

let () =
  let module C = Backends.MetaOCamlExt in
  let open Stream_cooked_fn.Make(C) in
  let (gtf)  : float code -> float code -> bool code = fun x y -> .< .~x  > .~y >. in
  let (gt)  : float cde -> float cde -> bool cde = fun x y -> C.lift2 Stdlib.( >) C.bool gtf x y in
  let to_list l = l |> fold (fun l x -> C.cons x l) (C.nil ()) |> C.cde_app1 .<List.rev>. in
  let of_docs docs : Doc.t cstream =
    let docs = C.dyn docs in
    Raw.infinite (fun k ->
      C.inj @@ letl (.<let v = Option.get @@ DocStream.peek .~docs in DocStream.junk .~docs; v >.) (C.injdyn k)
    )
    |> Raw.(guard (GExp (C.inj .< DocStream.peek .~docs <> None >.)))
  in
  let score doc = let doc = C.dyn doc in C.inj .< .~doc.Doc.score >. in
(*
  let test limit = C.one_arg_fun (fun s -> of_docs s |> filter (fun doc -> C.(gt (score doc) (float limit))) |> to_list) in
  let test2 = C.one_arg_fun (fun s -> of_arr s |> filter (fun doc -> C.(gt (score doc) (float 5.))) |> to_list) in
  show_code (test 5.);
  show_code test2;
  print_list @@ doc_ids @@ Array.to_list docs1;
  print_list @@ doc_ids @@ Runcode.run (test 5.) @@ docstream docs1;
  print_list @@ doc_ids @@ Runcode.run test2 @@ docs1;
*)
(*
  let do_merge2 = C.two_arg_fun @@ fun (t1, t2) ->
    Raw.merge_raw (fun a b -> C.inj .< .~(C.dyn a).Doc.doc_id < .~(C.dyn b).Doc.doc_id >.)
      (of_arr t1 |> filter (C.cde_app1 .<fun t -> t.Doc.score < 6. >.))
      (of_docs t2 |> filter (fun doc -> C.(gt (score doc) (float 4.))))
    |> to_list
  in
  show_code do_merge2;
  print_list @@ doc_ids @@ Array.to_list docs1;
  print_list @@ doc_ids @@ Array.to_list docs2;
  print_list @@ doc_ids @@ Array.to_list docs3;
  print_list @@ doc_ids @@ Runcode.run do_merge2 (docs1, docstream docs2);
*)
  let do_merge : float code list -> DocStream.t code list -> 'a = fun limits l ->
    let l = List.map2 (fun limit docs -> (of_docs @@ C.inj docs) |> filter (C.cde_app1 .<fun t -> t.Doc.score > .~limit>.)) limits l in
    match l with
    | [] -> .<[]>.
    | h::t ->
    List.fold_left (fun acc docs ->
        Raw.merge_raw (fun a b -> C.inj .< .~(C.dyn a).Doc.doc_id < .~(C.dyn b).Doc.doc_id >.)
        acc
        docs) h t |> to_list |> C.dyn
  in
(*
  print_endline "";
  print_list @@ doc_ids @@ Runcode.run @@ do_merge (lift_elements [1.;3.;5.]) (lift_elements @@ List.map docstream [docs1; docs2; docs3]);
  let do_merge3 = .<fun (la,a) (lb,b) (lc,c) -> .~(do_merge [.<la>.;.<lb>.;.<lc>.] [.<a>.;.<b>.;.<c>.]) >. in
  show_code do_merge3;
  print_list @@ doc_ids @@ Runcode.run do_merge3 (1., docstream docs1) (3., docstream docs2) (5., docstream docs3);
*)
  let do_must = C.two_arg_fun @@ fun (t1, t2) ->
    Raw.merge_map_raw (fun a -> a) (fun b -> b)
      (C.cde_app2 .<fun a b ->
        if a.Doc.doc_id = b.Doc.doc_id then true, true, a
        else if a.doc_id < b.doc_id then true, false, a
        else false, true, b>.)
      (of_docs t1)
      (of_docs t2)
    |> to_list
  in
  show_code do_must;
  print_list @@ doc_ids @@ Array.to_list docs1;
  print_list @@ doc_ids @@ Array.to_list docs2;
  print_list @@ doc_ids @@ Runcode.run do_must (docstream docs1, docstream docs2);
  ()
