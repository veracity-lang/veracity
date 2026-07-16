open Unix
open OUnit2
open Vcy
open Util

let args = [| ""; ""; ""; ""; ""; ""; "" |]
let program_dir = "../../../../programs/"

let run_vcy_file fname given_args user_input = 
    args.(1) <- "interp";
    args.(2) <- fname;
    List.iteri (fun i arg -> args.(i+3) <- arg) given_args;
    let pout, pin = open_process_args "../run.exe" args in
    output_string pin user_input; flush pin;
    String.concat "\n" @@ read_all_in pout

let run_vcy_file_error fname given_args user_input = 
    args.(1) <- "interp";
    args.(2) <- fname;
    List.iteri (fun i arg -> args.(i+3) <- arg) given_args;
    let pout, pin, perr = open_process_args_full "../run.exe" args [||] in
    output_string pin user_input; flush pin;
    String.concat "\n" @@ read_all_in perr

let make_test_vcy_file_with_input prog_name given_args exp_output user_input _ = 
    assert_equal ~printer:(fun s -> s) exp_output (run_vcy_file (program_dir ^ prog_name) given_args user_input)

let make_test_vcy_file prog_name given_args exp_output = 
    make_test_vcy_file_with_input prog_name given_args exp_output ""

let make_test_vcy_file_error prog_name given_args exp_output _ = 
    assert_equal ~printer:(fun s -> s) exp_output (run_vcy_file_error (program_dir ^ prog_name) given_args "")

let make_test_vcy_file_nondet fname given_args acceptable_outputs = 
    let out = run_vcy_file fname given_args "" in
    let rec check_validity acceptable_outputs =
        begin match acceptable_outputs with
        | [] -> assert_failure "Test did not match any given output."
        | s :: ss -> 
            begin try assert_equal ~printer:(fun s -> s) s out with
                Failure _ -> check_validity ss end end in
    check_validity acceptable_outputs

let suite = 
    "Vercity Programs" >::: [
      "array1.vcy" >:: make_test_vcy_file "array1.vcy" ["1"; "2"; "3"] (program_dir ^ "array1.vcy\n1\n2\n3\n\nReturn: 0")
    ; "array2.vcy" >:: make_test_vcy_file "array2.vcy" ["10"] "The 10th Fibonacci number is 34.\nReturn: 0"
    ; "array3.vcy" >:: make_test_vcy_file "array3.vcy" ["foo"; "bar"; "BAZ"] "../../../../progrAms/ArrAy3.vcy\nfoo\nbAr\nBaZ\n\nReturn: 0"
    
    ; "basic1.vcy" >:: make_test_vcy_file "basic1.vcy" [] "Return: 13"
    ; "basic2.vcy" >:: make_test_vcy_file "basic2.vcy" [] "Return: 16"
    ; "basic3.vcy" >:: make_test_vcy_file "basic3.vcy" [] "Return: 13"
    ; "basic4.vcy" >:: make_test_vcy_file "basic4.vcy" [] "Return: 67"
    ; "basic5.vcy" >:: make_test_vcy_file "basic5.vcy" [] "Return: 45"
    ; "basic6.vcy" >:: make_test_vcy_file "basic6.vcy" [] "Return: 720"
    
    ; "basic_fail1.vcy" >:: make_test_vcy_file_error "basic_fail1.vcy" [] ("An error occurred: IdNotFound(z, " ^ program_dir ^ "basic_fail1.vcy:[10.12-10.13])\n")
    ; "basic_fail2.vcy" >:: make_test_vcy_file_error "basic_fail2.vcy" [] ("An error occurred: IdNotFound(fx, " ^ program_dir ^ "basic_fail2.vcy:[8.13-8.21])\n")
    
    (* TODO: commute tests with the new nondet test *)
    
    ; "factorial.vcy" >:: make_test_vcy_file "factorial.vcy" ["5"] "Return: 120"
    
    (* TODO: files1 test *)
    
    ; "for_loop1.vcy" >:: make_test_vcy_file "for_loop1.vcy" [] "Return: 45"
    
    ; "function1.vcy" >:: make_test_vcy_file "function1.vcy" [] "Return: 15"
    ; "function2.vcy" >:: make_test_vcy_file "function2.vcy" [] "Return: 120"
    
    ; "function_fail1.vcy" >:: make_test_vcy_file_error "function_fail1.vcy" [] "An error occurred: TypeFailure(Function func is ill-defined, __internal:[1.1-1.1])\n"
    
    ; "global_fail1.vcy" >:: make_test_vcy_file_error "global_fail1.vcy" [] ("An error occurred: IdNotFound(haveChild, " ^ program_dir ^ "global_fail1.vcy:[15.14-15.56])\n")
    
    ; "hashset.vcy" >:: make_test_vcy_file "hashset.vcy" ["Hello"] "true\nReturn: 4"
    
    ; "hashtable1.vcy" >:: make_test_vcy_file "hashtable1.vcy" [] "LEN 1\nLEN 3\n5\n7\n8\nLEN 3\n10\nLEN 2\ntbl[d] is null.\nReturn: 0"
    ; "hashtable2.vcy" >:: make_test_vcy_file "hashtable2.vcy" [] "Return: 42"
    ; "hashtable3.vcy" >:: make_test_vcy_file "hashtable3.vcy" [] "Return: 123"
    
    ; "simple.vcy" >:: make_test_vcy_file "simple.vcy" [] "95\nReturn: 0"
    
    ; "struct1.vcy" >:: make_test_vcy_file "struct1.vcy" [] "x = 7; y = 15.\nReturn: 0"
    ; "struct2.vcy" >:: make_test_vcy_file "struct2.vcy" [] "Name is Dingus, age is 30, parents are Adam and Eve\nName is New name!, age is 30, parents are Adam and Eve\nName is Monocle, age is 10, parents are Dingus and New name!\nReturn: 0"
    
    ; "user_input.vcy" >:: make_test_vcy_file_with_input "user_input.vcy" [] "Return: 11" "1\n2\n3\n"
    
    ; "while1.vcy" >:: make_test_vcy_file "while1.vcy" ["10"] "3628800\nReturn: 11"
    ]


(* Timeout standardization: pure checks on Servois2.Timeouts, no solver or
   subprocess involved, so these run cleanly regardless of the program-file
   fixtures above. *)
module T = Servois2.Timeouts

let with_query q f =
  let saved = T.get () in
  Fun.protect ~finally:(fun () -> T.set saved) (fun () ->
    T.set { (T.get ()) with T.query = q }; f ())

let timeouts_suite =
  "Timeouts" >::: [
    (* The per-query limit is turned into the solver's own flag: this is what
       makes it configurable, and it must track [query]. *)
    "cvc5 flag tracks query" >:: (fun _ ->
      with_query 7.5 (fun () ->
        assert_equal ~printer:(String.concat " ")
          [ "--tlimit-per=7500" ]
          (Array.to_list (T.prover_args "CVC5"))));
    "z3 flag tracks query" >:: (fun _ ->
      with_query 7.5 (fun () ->
        assert_equal ~printer:(String.concat " ")
          [ "-t:7500" ] (Array.to_list (T.prover_args "Z3"))));
    (* Z3 used to have no limit at all; now it always gets one. *)
    "z3 is bounded by default" >:: (fun _ ->
      assert_bool "z3 has a timeout flag"
        (Array.length (T.prover_args "Z3") > 0));
    "unknown prover: no flag" >:: (fun _ ->
      assert_equal [||] (T.prover_args "no-such-prover"));
    (* "none"/"0"/"off" disable the optional limits. *)
    "opt parsing: none" >:: (fun _ ->
      assert_equal None (T.opt_of_arg "x" "none");
      assert_equal None (T.opt_of_arg "x" "0");
      assert_equal (Some 30.) (T.opt_of_arg "x" "30"));
    "query rejects non-positive" >:: (fun _ ->
      assert_raises (T.Bad_timeout ("x", "0"))
        (fun () -> T.float_of_arg "x" "0"));
  ]

let () = run_test_tt_main ("all" >::: [ suite; timeouts_suite ])
