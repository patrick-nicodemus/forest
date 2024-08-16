let script = {|<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css" integrity="sha384-nB0miv6/jRmo5UMMR1wu3Gz6NLsoTkbqJghGIsx//Rlm+ZU03BU6SQNC66uf4l5+" crossorigin="anonymous">
<!-- The loading of KaTeX is deferred to speed up page rendering -->
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js" integrity="sha384-7zkQWkzuo3B5mTepMUcHkMB5jZaolc2xDwL6VFqjFALcbeS9Ggm/Yr2r3Dy4lfFg" crossorigin="anonymous"></script>
<!-- To automatically render math in text elements, include the auto-render extension: -->
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js" integrity="sha384-43gviWU0YVjaDtb/GhzOouOXtZMP/7XUzwPTstBeZFe/+rCMvRwr4yROQP43s0Xk" crossorigin="anonymous"
        onload="renderMathInElement(document.body);"></script>
<script src="render_math_katex.js"></script>|};;


let inject_js source_root_dir target_root_dir rel_file_path =
  let print_out_channel out_channel s =
    Out_channel.output_string out_channel s;
    Out_channel.output_string out_channel "\n"
  in
    
  let regex = Re.str "</head>" |> Re.compile in
  let rec search_end_head in_ch out_ch : unit =
    match In_channel.input_line in_ch with
    | Some (line : string) ->
      if Re.execp regex line then
         let line' = Re.replace_string regex ~by:(script ^ "</head>\n") line in
         print_out_channel out_ch line'
      else
        (print_out_channel out_ch line;
         search_end_head in_ch out_ch)
    | None -> failwith "Expected the regex to succeed."
  in 
  let rec f in_ch out_ch =
    match In_channel.input_line in_ch with
    | Some l -> print_out_channel out_ch l; f in_ch out_ch
    | None -> ()
  in
  let in_ch = In_channel.open_text (Filename.concat source_root_dir rel_file_path) in
  let out_ch  = Out_channel.open_text (Filename.concat target_root_dir rel_file_path) in
  search_end_head in_ch out_ch;
  f in_ch out_ch;
;;  


let dir_is_empty dir =
  Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are
    contained in [dir]. Each file is a path starting with [dir]. *)
let dir_contents dir =
  let rec loop result = function
    | f::fs when Sys.is_directory f ->
          Sys.readdir f
          |> Array.to_list
          |> List.map (Filename.concat f)
          |> List.append fs
          |> loop result
    | f::fs -> loop (f::result) fs
    | []    -> result
  in
  loop [] [dir];;

let over_all =
  let source_root_dir = "./coq/_build/default/MyTheory.html/" in
  let target_root_dir = "./assets/MyTheory.html" in
  let s = source_root_dir in
  let ls = String.length s in
  let dir_contents = dir_contents s in
  let rel_file_path t =
     let lt = String.length t in
     let k = lt - ls in
     String.sub t ls k
  in
  List.iter (fun filename ->
      let r = (rel_file_path filename) in
      if (Filename.check_suffix r ".html") then
      inject_js source_root_dir target_root_dir r
    ) dir_contents

(* let () = *)
(*   try Unix.unlink "./assets/MyTheory.html/coqdoc.css" with _ -> (); *)
(*   Unix.link "./assets/pat_coqdoc.css" "./assets/MyTheory.html/coqdoc.css"; *)
(*   try Unix.unlink "./assets/MyTheory.html/render_math_katex.js" with _ -> (); *)
(*   Unix.link "./assets/render_math_katex.js" "./assets/MyTheory.html/render_math_katex.js" *)
  
