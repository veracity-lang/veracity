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

(* Collect all SVGs from a directory: pre-built .svg files first,
   then .dot files converted via graphviz. *)
let svgs_of_subdir subdir =
  try
    let entries = Sys.readdir subdir |> Array.to_list |> List.sort String.compare in
    (* Pre-built SVGs and HTML fragments (e.g. the variable table) are
       included in sorted order — "heap_diagram.svg" before "heap_table.html". *)
    let prebuilt = entries
      |> List.filter (fun f ->
           let ext = Filename.extension f in
           (ext = ".svg" || ext = ".html") && f <> "index.html")
      |> List.filter_map (fun f ->
           try Some (read_file (Filename.concat subdir f)) with _ -> None)
    in
    let dot_svgs = entries
      |> List.filter (fun f -> Filename.extension f = ".dot")
      |> List.map (fun f -> Filename.concat subdir f)
      |> List.filter_map dot_to_svg
    in
    prebuilt @ dot_svgs
  with _ -> []


let css = {|<style>
*{box-sizing:border-box}
body{margin:0;padding:20px 24px;background:#1e1e1e;color:#d4d4d4;
     font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}
h1{color:#569cd6;margin:0 0 4px}
.meta{color:#888;font-size:.85em;margin-bottom:18px}
.meta code{color:#9cdcfe;background:#2d2d2d;padding:1px 5px;border-radius:3px}
.layout{display:flex;gap:20px;align-items:flex-start}
.src-panel{flex:1 1 auto;min-width:0;overflow-x:auto}
table.src{border-collapse:collapse;width:100%;font-family:'Consolas','Monaco',monospace;
          font-size:.85em;background:#252526;border-radius:6px;overflow:hidden}
table.src td{padding:1px 8px;white-space:pre;vertical-align:top}
.ln{color:#555;user-select:none;text-align:right;border-right:1px solid #333;
    padding-right:10px;min-width:44px}
.code{color:#d4d4d4}
tr.cm{background:#132236;cursor:pointer}
tr.cm:hover{background:#1b3a5e}
tr.cm.active{background:#1f3f6e}
tr.cm .ln{color:#4ec9b0}
tr.cm .code{color:#9cdcfe}
.badge{display:inline-block;background:#0e639c;color:#fff;font-size:.72em;
       border-radius:3px;padding:0 5px;margin-left:10px;vertical-align:middle}
/* side diagram panel */
.diag-panel{display:none;flex:0 0 60%;position:sticky;top:20px;
            background:#252526;border:1px solid #3c3c3c;border-radius:8px;
            padding:20px;max-height:calc(100vh - 40px);overflow-y:auto}
.diag-panel h2{margin-top:0;color:#569cd6;font-size:1.1em}
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

let js_prefix = {|<script>
var _activeRow = null;
function openModal(n){
  var panel = document.getElementById('diag-panel');
  var content = document.getElementById('diag-content');
  var d = commuteData[n];
  content.innerHTML =
    '<span class="closebtn" onclick="closePanel()">&times;</span>' +
    '<h2>Commute Block ' + n + '</h2>' +
    '<div class="mloc">' + d.loc + '</div>' +
    '<div class="mcond">' + d.cond + '</div>' +
    '<div class="diagrams">' + d.diagrams + '</div>' +
    '<div class="mlinks">' + d.link + '</div>';
  panel.style.display = 'block';
  if(_activeRow){ _activeRow.classList.remove('active'); }
  var rows = document.querySelectorAll('tr.cm');
  rows.forEach(function(r){ if(r.getAttribute('data-cid')==String(n)){ _activeRow=r; r.classList.add('active'); } });
}
function closePanel(){
  document.getElementById('diag-panel').style.display='none';
  if(_activeRow){ _activeRow.classList.remove('active'); _activeRow=null; }
}
document.addEventListener('keydown',function(e){
  if(e.key==='Escape') closePanel();
});
|}

let js_suffix = {|</script>|}

let create_session_dir () =
  (* Filename.temp_file gives us a unique name; remove the dummy file,
     create a directory instead. *)
  let base = Filename.temp_file ~temp_dir:"/tmp" "veracity_" "" in
  Sys.remove base;
  Unix.mkdir base 0o755;
  base

let generate ~source_file ~session_dir ~records =
  (* 1. Read source *)
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
           "<tr class=\"cm\" data-cid=\"%d\" onclick=\"openModal(%d)\"><td class=\"ln\">%d</td>\
            <td class=\"code\">%s%s</td></tr>\n"
           cid cid lineno (html_escape line) badge)
  ) source_lines;
  Buffer.add_string src_buf "</table>\n";

  (* 5. Build JS commute data object *)
  let js_buf = Buffer.create 8192 in
  Buffer.add_string js_buf "var commuteData = {\n";
  List.iteri (fun i (r : Util.commute_record) ->
    let svgs = svgs_of_subdir r.subdir in
    let diag_html = match svgs with
      | [] -> "<p class=\\\"nodiag\\\">No diagrams (graphviz not available or no satisfying model found).</p>"
      | _  -> String.concat "\\n" (List.map (fun s ->
            (* escape backslashes then quotes for JS string *)
            s |> Str.global_replace (Str.regexp_string "\\") "\\\\"
              |> Str.global_replace (Str.regexp_string "\"") "\\\""
              |> Str.global_replace (Str.regexp_string "\n") "\\n"
          ) svgs)
    in
    let examine_rel  = Printf.sprintf "commute_%04d/index.html" i in
    let examine_full = Filename.concat session_dir examine_rel in
    let examine_link =
      if Sys.file_exists examine_full then
        Printf.sprintf "<a href=\\\"%s\\\">Open Servois2 query viewer &rarr;</a>" examine_rel
      else
        "<span style=\\\"color:#555\\\">Servois2 query viewer not available</span>"
    in
    let js_escape s =
      s |> Str.global_replace (Str.regexp_string "\\") "\\\\"
        |> Str.global_replace (Str.regexp_string "\"") "\\\""
        |> Str.global_replace (Str.regexp_string "\n") "\\n"
    in
    Buffer.add_string js_buf
      (Printf.sprintf "  %d:{loc:\"%s\",cond:\"%s\",diagrams:\"%s\",link:\"%s\"},\n"
         i (js_escape r.loc_str) (js_escape r.condition) diag_html examine_link)
  ) records;
  Buffer.add_string js_buf "};\n";

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
<div class="layout">
  <div class="src-panel">
%s
  </div>
  <div class="diag-panel" id="diag-panel">
    <div id="diag-content"></div>
  </div>
</div>
%s
%s
%s
</body>
</html>|}
    (Filename.basename source_file)
    css
    (html_escape source_file)
    (html_escape session_dir)
    (Buffer.contents src_buf)
    js_prefix
    (Buffer.contents js_buf)
    js_suffix
  in

  let out_path = Filename.concat session_dir "index.html" in
  let oc = open_out out_path in
  output_string oc html;
  close_out oc;
  out_path
