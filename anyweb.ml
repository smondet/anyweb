(*B {ignore} B*)
(*
Copyright (C) 2003 Nicolas Cannasse (two functions from
 ExtString.ml: find and split)
Copyright (C) 2011 Sebastien Mondet (everything else)

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version,
with the special exception on linking described in file LICENSE.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)
(*B {end} B*)
(*B
{header|
  {title|The {b|anyweb} Hack}
  {authors|{link http://seb.mondet.org|Sebastien Mondet}}
  {subtitle|Literate Programming With Anything You May Find}
}
  
{section 1|Compile}

It is simple:
{code}
ocamlc unix.cma anyweb.ml -o anyweb
{end}

{section 1|Running Examples}

This document comes from {t|anyweb}'s source {i|piped}
to {link http://bracetax.berlios.de/ |bracetax}:
{code}
anyweb camlbrtxhtml anyweb.ml | \
    brtx -doc -o index.html  -title "The anyweb Source" -link-css anyweb.css
{end}
if you are curious, here is {link ./anyweb_no_css.html|a version without CSS}
(i.e. with {t|-link-css anyweb.css}).
{p}
The same way we can make {link ./anyweb.pdf |a PDF}:
{code}
anyweb camlbrtxlatex anyweb.ml | \
    brtx -latex -doc -o anyweb.tex  -title "The anyweb Source"
pdflatex anyweb
{end}

This other example {i|documents}
{link https://github.com/smondet/anyweb/blob/master/subset_notes.v
|a Coq {t|.v} file}:
{code}
anyweb coqbrtxhtml subset_notes.v | \
    brtx -o coq_example.html -doc -link-css anyweb.css 
anyweb coqbrtxlatex subset_notes.v | \
    brtx -latex -o coq_example.tex -doc -use-package coqdoc
pdflatex coq_example
{end}
The results are some pieces of
{link coq_example.html|HTML} and
{link coq_example.pdf|PDF}.
(these are some notes taken while {i|doing} {link http://adam.chlipala.net/cpdt/
|CPDT}{~}{...} which is worth reading!).

{section 1|The Code}

We do not print the code for:
{code}
val split : string -> string -> string * string
val line_opt : in_channel -> string option
val feed : cmd:string -> input:string -> string
{end}
which can be found
{link http://ocaml-extlib.googlecode.com/svn/trunk/extlib/extString.ml
|in ExtLib} and
{link http://martin.jambon.free.fr/toolbox.html |Camlmix's toolbox}.


{ignore endignorecode}
B*)

open Printf

(* Extlib's *)
let find str sub =
  let sublen = String.length sub in
  if sublen = 0 then
    0
  else
    let found = ref 0 in
    let len = String.length str in
    try
      for i = 0 to len - sublen do
	let j = ref 0 in
	while String.unsafe_get str (i + !j) = String.unsafe_get sub !j do
	  incr j;
	  if !j = sublen then begin found := i; raise Exit; end;
	done;
      done;
      failwith "Invalid string"
    with
      Exit -> !found

let split str sep =
  let p = find str sep in
  let len = String.length sep in
  let slen = String.length str in
  String.sub str 0 p, String.sub str (p + len) (slen - p - len)
        

let find_opt a b = try Some (find a b) with e -> None
let split_opt s i = try Some (split s i) with e -> None
let line_opt i = try Some ((input_line i) ^ "\n") with e -> None

(* From the camlmix toolbox: *)
let kfeed f command data =
  let (ic, oc) as channels = Unix.open_process command in
  output_string oc data;
  close_out oc;
  let exn = ref None in
  begin 
    try
      while true do
        f (input_char ic)
      done
    with
    | End_of_file -> ()
    | e -> exn := Some e
  end;
  begin match Unix.close_process channels with
  | Unix.WEXITED 0 -> ()
  | _ -> invalid_arg ("feed_command: " ^ command)
  end;
  (match !exn with Some e -> raise e | None -> ())
let bfeed buf command data = kfeed (Buffer.add_char buf) command data
    
let feed ~cmd ~input = 
  let buf = Buffer.create (2 * String.length input) in
  bfeed buf cmd input;
  Buffer.contents buf

(*B {endignorecode}

{section 2|The environment}

 B*)

type environment = {
  start_token : string;
  on_begin : out_channel -> unit;
  on_text: out_channel -> string -> unit;
  on_change : out_channel -> unit;
  end_token : string;
  on_end : out_channel -> unit;
  contains : string list;
}
let environment
    ?(on_begin = fun o -> ())
    ?(on_text = output_string)
    ?(on_change = fun o -> ())
    ?(on_end = fun o -> ())
    start_token end_token contains =
  { on_begin; on_text; on_change; on_end;
    start_token; end_token; contains }    

(*B {section 2|The transformation} B*)

let split_first s l current =
  List.fold_left
    (fun m k -> 
      match m, k with
      | None, x -> x
      | x, None -> x
      | Some (_, _, mb, _), Some (_, _, kb, _) ->
        if String.length mb <= String.length kb then m else k)
    None
    ((match split_opt s current.end_token with 
      None -> None | Some (b, a) -> Some (true, current, b, a)) ::
        (List.map (fun env ->
          match split_opt s env.start_token with
          | None -> None
          | Some (b, a) -> Some (false, env, b, a)) l))


let transform environments in_chan out_chan =
  let rec loop stack current_text =
    match stack with
    | env :: l ->
      let inside = List.map (fun x -> List.assoc x environments) env.contains in
      begin match split_first current_text inside env with
      | Some (true, s, before, after) -> (* unstack *)
        env.on_text out_chan before;
        env.on_end out_chan;
        loop l after
      | Some (false, s, before, after) -> (* stack *)
        env.on_text out_chan before;
        env.on_change out_chan;
        s.on_begin out_chan;
        loop (s :: stack) after
      | None ->
        env.on_text out_chan current_text;
        begin match line_opt in_chan with
        | Some line ->
          loop stack line
        | None -> env.on_end out_chan; ()
        end
      end
    | [] ->
      failwith 
        (sprintf "Unstacked too much, do not know what to do now: %S" 
           current_text)
  in
  let toplevel = (snd (List.hd environments)) in
  toplevel.on_begin out_chan;
  loop [ toplevel ] "";
  ()
    
(*B {section 2|Available environments}

First, a {i|complicated} one, used for testing:
 B*)

let test_environments = [
  "brackets",
  environment
    ~on_begin:(fun o -> output_string o "(START_BRACKETS)")
    ~on_text:(fun o s -> output_string o (String.uppercase s))
    ~on_end:(fun o -> output_string o "(END_BRACKETS)")
    "[[" "]]" [ "braces" ];
  "braces",
  environment
    ~on_begin:(fun o -> output_string o "(START_BRACES)")
    ~on_text:(fun o s -> output_string o (String.uppercase s))
    ~on_end:(fun o -> output_string o "(END_BRACES)")
    "{{" "}}" [ "LTGTs"; "parens" ];
  "LTGTs",
  environment
    ~on_begin:(fun o -> output_string o "(START_LTGTs)")
    ~on_text:(fun o s -> output_string o (String.uppercase s))
    ~on_end:(fun o -> output_string o "(END_LTGTs)")
    "<<" ">>" [];
  "parens", 
  environment
    ~on_begin:(fun o -> output_string o "(START_PARENS)")
    ~on_text:(fun o s -> output_string o (String.uppercase s))
    ~on_end:(fun o -> output_string o "(END_PARENS)")
    "(((" ")))" [ "brackets" ];
]

(*B  {p}
A function to create two functions: one which which stores in a
buffer, and another one which gives the contents of the buffer to the
argument and clears the {i|internal} buffer.
 B*)
let bufferise_and_do f =
  let buffer = Buffer.create 42 in
  ((fun o s -> Buffer.add_string buffer s),
   (fun o ->
     let stuff_done = f (Buffer.contents buffer) in
     output_string o stuff_done;
     Buffer.clear buffer))
(*B  {p}

This function name is self-explanatory:
 B*)
let is_whitespace s =
  try
    String.iter (function
      | ' ' | '\n' | '\r' | '\t' -> ()
      | c -> raise Exit) s;
    true
  with Exit -> false

(*B {p}
 The few tricks needed now here are:
  {begin list}
  {*} The {t|coqdoc} command line: we use {t|cat} to dump {t|stdin} to
  a file, and then we call {t|coqdoc}.
  {*} We have to write things like {i|{t|"(*" ^ "B"}} or {i|{t|"B" ^ "*)"}} to
  allow {t|anyweb} to run on its own source.
  {end}
This gives the {t|coqbrtx} transformer:
  B*)

let coqbrtx fmt = 
  let coqdoc =
    sprintf
      "cat > /tmp/ttt.v ; coqdoc -s --parse-comments --stdout \
        --body-only --no-index %s /tmp/ttt.v"
      (match fmt with `html -> "--html" | `latex -> "--latex") in 
  [
    "coq",  
    (let on_text, on_end =
       bufferise_and_do (fun input ->
         if is_whitespace input then "# Removed whitespace\n"
         else
           "{bypass endanywebbypass}" ^ (feed ~cmd:coqdoc ~input)
           ^ "{endanywebbypass}") in
     environment ~on_text ~on_end ~on_change:on_end
       "[coq[" "]coq]" [ "bracetax" ]);
    "bracetax", environment ("(*" ^ "B") ("B" ^ "*)") [ "coq" ];
  ]

(*B {p}
And similarly the {t|camlbrtx} one:  B*)
let camlbrtx fmt = [
  "caml",  
  (let on_text, on_end =
     let cmd = 
       sprintf "source-highlight -s caml -f %s" 
         (match fmt with `html -> "xhtml" | `latex -> "latex") in
     bufferise_and_do (fun input ->
       if is_whitespace input then "# Removed whitespace\n"
       else
         "{bypass endanywebcode}" ^ (feed ~cmd ~input) ^ "{endany" ^ "webcode}") in
   environment  ~on_text ~on_end ~on_change:on_end
     ("[ca" ^ "ml[") ("]ca" ^ "ml]") [ "bracetax" ]);
  "bracetax", environment ("(*" ^ "B") ("B" ^ "*)") [ "caml" ];
]

(*B {section 2|The {q|main} function} B*)
  
let () =
  let lang = 
    try match Sys.argv.(1) with
    | "coqbrtxhtml" -> coqbrtx `html
    | "coqbrtxlatex" -> coqbrtx `latex
    | "camlbrtxhtml" -> camlbrtx `html
    | "camlbrtxlatex" -> camlbrtx `latex
    | _ -> test_environments
    with e -> test_environments in
  let i = try open_in Sys.argv.(2) with e -> stdin in
  let o = try open_out Sys.argv.(3) with e -> stdout in
  transform lang i o;
  close_in i; close_out o

(*B 
{section 1|To-Do List}

{begin list}
{*} command-line-forged transformers
{end} 


 B*)

