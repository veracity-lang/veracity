open Lexing

type pos = int * int (* Line number and column *)

type t = string * pos * pos

let line_of_pos (l, _ : pos) = l

let col_of_pos (_, c : pos) = c

let mk_pos line col : pos = (line, col)

let file_of_range (f, _, _ : t) = f

let start_of_range (_, s, _ : t) = s

let end_of_range (_, _, e : t) = e

let mk_range f s e : t = (f, s, e)

let valid_pos (l, c : pos) = l >= 0 && c >= 0

let merge_range (f, s1, e1 as r1 : t) (f', s2, e2 as r2 : t) =
  if f <> f'
  then
    failwith
    @@ Printf.sprintf "merge_range called on different files: %s and %s" f f'
  else if not (valid_pos s1)
  then r2
  else if not (valid_pos s2)
  then r1
  else mk_range f (min s1 s2) (max e1 e2)


(*let string_of_range (f, (sl, sc), (el, ec) : t) =
  Printf.sprintf "%s:[%d.%d-%d.%d]" f sl sc el ec*)
let string_of_range (f, (sl, sc), (el, ec) : t) =
  Printf.sprintf "%s:[%d.%d-%d.%d]" f (sl+1) (sc+1) (el+1) (ec+1)

let ml_string_of_range (f, (sl, sc), (el, ec) : t) =
  Printf.sprintf "(\"%s\", (%d, %d), (%d, %d))" f sl sc el ec


let norange : t = ("__internal", (0, 0), (0, 0))

(* Creates a Range.pos from the Lexing.position data *)
let pos_of_lexpos (p : position) : pos =
  mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol)


let mk_lex_range (p1 : position) (p2 : position) : t =
  mk_range p1.pos_fname (pos_of_lexpos p1) (pos_of_lexpos p2)


(* Expose the lexer state as a Range.t value *)
let lex_range lexbuf : t =
  mk_lex_range (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)
