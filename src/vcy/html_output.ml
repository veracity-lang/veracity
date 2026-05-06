let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let html_escape s =
  let buf = Buffer.create (String.length s + 16) in
  String.iter (function
    | '<' -> Buffer.add_string buf "&lt;"
    | '>' -> Buffer.add_string buf "&gt;"
    | '&' -> Buffer.add_string buf "&amp;"
    | '"' -> Buffer.add_string buf "&quot;"
    | c   -> Buffer.add_char   buf c
  ) s;
  Buffer.contents buf

(* Parse "file:[sl.sc-el.ec]" → (sl, el) line range, ignoring columns. *)
let parse_line_range s =
  try
    let bracket = String.index s '[' in
    let dot1    = String.index_from s (bracket + 1) '.' in
    let dash    = String.index_from s (dot1 + 1)    '-' in
    let dot2    = String.index_from s (dash + 1)    '.' in
    let close   = String.index_from s (dot2 + 1)    ']' in
    let sl = int_of_string (String.sub s (bracket+1) (dot1 - bracket - 1)) in
    let el = int_of_string (String.sub s (dash+1)    (dot2 - dash   - 1)) in
    ignore close;
    Some (sl, el)
  with _ -> None

(* Run dot -Tsvg on a .dot file; return the SVG string or None. *)
let dot_to_svg dot_path =
  let svg_path = Filename.remove_extension dot_path ^ ".svg" in
  let cmd = Printf.sprintf "dot -Tsvg %s -o %s 2>/dev/null"
              (Filename.quote dot_path) (Filename.quote svg_path) in
  if Sys.command cmd = 0 then
    (try Some (read_file svg_path) with _ -> None)
  else None

(* Collect all SVGs from .dot files in a directory. *)
let svgs_of_subdir subdir =
  try
    let entries = Sys.readdir subdir |> Array.to_list in
    let dots = entries
      |> List.filter (fun f -> Filename.extension f = ".dot")
      |> List.sort String.compare
      |> List.map (fun f -> Filename.concat subdir f)
    in
    List.filter_map dot_to_svg dots
  with _ -> []

(* Run perl examine.pl inside a subdir to generate servois2_examine.html. *)
let run_examine_pl subdir =
  let pl = Filename.concat subdir "examine.pl" in
  if Sys.file_exists pl then begin
    let cmd = Printf.sprintf "cd %s && perl examine.pl >/dev/null 2>&1"
                (Filename.quote subdir) in
    ignore (Sys.command cmd)
  end

let css = {|<style>
*{box-sizing:border-box}
body{margin:0;padding:20px 24px;background:#1e1e1e;color:#d4d4d4;
     font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}
h1{color:#569cd6;margin:0 0 4px}
.meta{color:#888;font-size:.85em;margin-bottom:18px}
.meta code{color:#9cdcfe;background:#2d2d2d;padding:1px 5px;border-radius:3px}
table.src{border-collapse:collapse;width:100%;font-family:'Consolas','Monaco',monospace;
          font-size:.85em;background:#252526;border-radius:6px;overflow:hidden}
table.src td{padding:1px 8px;white-space:pre;vertical-align:top}
.ln{color:#555;user-select:none;text-align:right;border-right:1px solid #333;
    padding-right:10px;min-width:44px}
.code{color:#d4d4d4}
tr.cm{background:#132236;cursor:pointer}
tr.cm:hover{background:#1b3a5e}
tr.cm .ln{color:#4ec9b0}
tr.cm .code{color:#9cdcfe}
.badge{display:inline-block;background:#0e639c;color:#fff;font-size:.72em;
       border-radius:3px;padding:0 5px;margin-left:10px;vertical-align:middle}
/* modal */
.backdrop{display:none;position:fixed;inset:0;background:rgba(0,0,0,.65);z-index:100}
.modal{display:none;position:fixed;top:50%;left:50%;
       transform:translate(-50%,-50%);z-index:101;
       background:#252526;border:1px solid #3c3c3c;border-radius:8px;
       padding:24px;max-width:92vw;max-height:88vh;overflow-y:auto;min-width:500px}
.modal h2{margin-top:0;color:#569cd6;font-size:1.1em}
.mloc{color:#888;font-size:.82em;margin-bottom:8px}
.mcond{background:#1a1a1a;border:1px solid #333;border-radius:4px;
       padding:10px 14px;font-family:monospace;color:#4ec9b0;
       word-break:break-all;margin-bottom:14px}
.diagrams svg{max-width:100%;height:auto;display:block;background:#fff;
              border:1px solid #ccc;border-radius:4px;margin:6px 0}
.nodiag{color:#666;font-style:italic;font-size:.9em}
.mlinks{margin-top:14px;font-size:.9em}
.mlinks a{color:#4ec9b0;text-decoration:none}
.mlinks a:hover{text-decoration:underline}
.closebtn{float:right;cursor:pointer;font-size:1.5em;color:#666;line-height:1}
.closebtn:hover{color:#d4d4d4}
</style>|}

let js = {|<script>
function openModal(n){
  document.getElementById('bd').style.display='block';
  document.getElementById('m'+n).style.display='block';
}
function closeModal(n){
  document.getElementById('bd').style.display='none';
  document.getElementById('m'+n).style.display='none';
}
document.addEventListener('keydown',function(e){
  if(e.key==='Escape'){
    document.getElementById('bd').style.display='none';
    document.querySelectorAll('.modal').forEach(function(m){m.style.display='none';});
  }
});
</script>|}

let create_session_dir () =
  (* Filename.temp_file gives us a unique name; remove the dummy file,
     create a directory instead. *)
  let base = Filename.temp_file ~temp_dir:"/tmp" "veracity_" "" in
  Sys.remove base;
  Unix.mkdir base 0o755;
  base

let generate ~source_file ~session_dir ~records =
  (* 1. Run perl examine.pl in each commute subdir to produce examine.html *)
  List.iter (fun (r : Util.commute_record) -> run_examine_pl r.subdir) records;

  (* 2. Read source *)
  let source_text =
    try read_file source_file
    with _ ->
      Printf.eprintf "html_output: cannot read %s\n" source_file; ""
  in
  let source_lines = String.split_on_char '\n' source_text in

  (* 3. Build a map: line number → list of commute indices covering it *)
  let line_map : (int, int list) Hashtbl.t = Hashtbl.create 32 in
  List.iteri (fun i (r : Util.commute_record) ->
    match parse_line_range r.loc_str with
    | None -> ()
    | Some (sl, el) ->
      for l = sl to el do
        let cur = try Hashtbl.find line_map l with Not_found -> [] in
        if not (List.mem i cur) then
          Hashtbl.replace line_map l (cur @ [i])
      done
  ) records;

  (* 4. Build source table HTML *)
  let src_buf = Buffer.create 8192 in
  Buffer.add_string src_buf "<table class=\"src\">\n";
  List.iteri (fun i line ->
    let lineno   = i + 1 in
    let commutes = try Hashtbl.find line_map lineno with Not_found -> [] in
    match commutes with
    | [] ->
      Buffer.add_string src_buf
        (Printf.sprintf "<tr><td class=\"ln\">%d</td><td class=\"code\">%s</td></tr>\n"
           lineno (html_escape line))
    | cid :: _ ->
      let is_first = match parse_line_range (List.nth records cid).loc_str with
        | Some (sl, _) -> sl = lineno | None -> false in
      let badge = if is_first then
        Printf.sprintf "<span class=\"badge\">&#128269; commute %d</span>" cid
        else "" in
      Buffer.add_string src_buf
        (Printf.sprintf
           "<tr class=\"cm\" onclick=\"openModal(%d)\"><td class=\"ln\">%d</td>\
            <td class=\"code\">%s%s</td></tr>\n"
           cid lineno (html_escape line) badge)
  ) source_lines;
  Buffer.add_string src_buf "</table>\n";

  (* 5. Build modals *)
  let modal_buf = Buffer.create 8192 in
  List.iteri (fun i (r : Util.commute_record) ->
    let svgs = svgs_of_subdir r.subdir in
    let diag_html = match svgs with
      | [] -> "<p class=\"nodiag\">No diagrams (graphviz not available or no satisfying model found).</p>"
      | _  -> String.concat "\n" svgs
    in
    let examine_rel  = Printf.sprintf "commute_%04d/servois2_examine.html" i in
    let examine_full = Filename.concat session_dir examine_rel in
    let examine_link =
      if Sys.file_exists examine_full then
        Printf.sprintf "<a href=\"%s\">Open Servois2 query viewer &rarr;</a>" examine_rel
      else
        "<span style=\"color:#555\">Servois2 query viewer not available \
         (run <code>perl examine.pl</code> in the commute subdirectory)</span>"
    in
    Buffer.add_string modal_buf
      (Printf.sprintf {|<div class="modal" id="m%d">
  <span class="closebtn" onclick="closeModal(%d)">&times;</span>
  <h2>Commute Block %d</h2>
  <div class="mloc">%s</div>
  <div class="mcond">%s</div>
  <div class="diagrams">%s</div>
  <div class="mlinks">%s</div>
</div>
|} i i i (html_escape r.loc_str) (html_escape r.condition) diag_html examine_link)
  ) records;

  (* 6. Assemble the full page *)
  let html = Printf.sprintf {|<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Veracity: %s</title>
%s
</head>
<body>
<h1>Veracity Analysis</h1>
<div class="meta">
  Source: <strong>%s</strong><br>
  Session: <code>%s</code>
</div>
%s
%s
<div class="backdrop" id="bd" onclick="
  this.style.display='none';
  document.querySelectorAll('.modal').forEach(function(m){m.style.display='none';});
"></div>
%s
</body>
</html>|}
    (Filename.basename source_file)
    css
    (html_escape source_file)
    (html_escape session_dir)
    (Buffer.contents src_buf)
    (Buffer.contents modal_buf)
    js
  in

  let out_path = Filename.concat session_dir "index.html" in
  let oc = open_out out_path in
  output_string oc html;
  close_out oc;
  out_path
