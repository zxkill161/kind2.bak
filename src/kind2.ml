(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

(** Top level of the Kind 2 model-checker. *)

(** 打开名为 "Lib" 的模块，以便在当前作用域中使用其中定义的函数和类型。*)
open Lib

(* 定义一个名为 "Signals" 的模块，其实际上是引用了另一个名为 "TermLib.Signals" 的模块。通过这样的方式，可以在当前作用域中使用 "TermLib.Signals" 模块中定义的函数和类型。 *)
module Signals = TermLib.Signals

(* Hide existential type parameter of to construct values of 'a InputSystem.t
   at runtime *)
type any_input =
| Input : 'a InputSystem.t -> any_input

(* 根据输入文件的路径，返回一个字符串，用于描述输入流的类型。 *)
(* 如果 "in_file" 的值为空字符串，则返回 "standard input"，否则返回 "input file '文件名'" 的字符串，其中 "文件名" 是 "in_file" 的值 *)
let classify_input_stream: string -> string = fun in_file -> 
  match in_file with
   | "" -> "standard input"
   | _  -> "input file '" ^ in_file ^ "'"


(* Setup everything and returns the input system. Setup includes:
   - flag parsing,标志解析（flag parsing）：解析并处理命令行标志，以获取程序运行时的配置参数。
   - debug setup,调试设置（debug setup）：根据配置参数设置调试相关的选项和参数。
   - log level setup,日志级别设置（log level setup）：设置日志输出的级别，以控制日志的详细程度。
   - smt solver setup,SMT求解器设置（smt solver setup）：配置程序所使用的SMT求解器。
   - timeout setup,超时设置（timeout setup）：设置程序运行的最大时间限制，以防止运行时间过长。
   - signal handling,信号处理（signal handling）：处理来自操作系统的信号，例如键盘中断信号。
   - starting global timer,启动全局计时器（starting global timer）：开始计时，以测量程序的执行时间。
   - parsing input file,解析输入文件（parsing input file）：读取和解析输入文件，以获取程序所需的输入数据。
   - building input system. 构建输入系统（building input system）：根据解析得到的输入数据构建输入系统。*)
let setup : unit -> any_input = fun () ->

  (* Parse command-line flags. *)
  (* 根据命令行的各种参数对kind2的执行进行配置 
     Flags.parse_argv是配置的主体函数
   *)
  (try
    Flags.parse_argv ()
   with
   | Flags.Error -> (
      KEvent.terminate_log () ; exit ExitCodes.usage_error
   )
   | Flags.UnsupportedSolver -> (
      KEvent.terminate_log () ; exit ExitCodes.unsupported_solver
   )
   | Flags.SolverNotFound -> (
      KEvent.terminate_log () ; exit ExitCodes.not_found_error
   )
  );

  Debug.set_dflags (Flags.debug ()) ;

  (* Formatter to write debug output to. *)
  (* 根据用户指定的参数来决定是否把debug日志写入文件中 *)
  (match Flags.debug_log () with
    (* Write to stdout by default. *)
    | None -> ()
    (* Open channel to given file and create formatter on channel. *)
    | Some f ->
      let oc = try open_out f with Sys_error msg ->
        Format.sprintf
          "Could not open debug logfile '%s': '%s'" f msg
        |> failwith
      in
      Debug.set_formatter (Format.formatter_of_out_channel oc)
  ) ;


  (* Record backtraces on log levels debug and higher. *)
  if output_on_level L_debug then Printexc.record_backtrace true ;

  (*
    /!\ ================================================================== /!\
    /!\ Must not use [vtalrm] signal, this is used internally by the OCaml /!\
    /!\                        [Threads] module.                           /!\
    /!\ ================================================================== /!\
  *)

  (* Raise exception on CTRL+C. *)
  Sys.catch_break true ;

  (* Set sigalrm handler. *)
  Signals.set_sigalrm_timeout_from_flag () ;

  (* Install generic signal handlers for other signals. *)
  Signals.set_sigint () ;
  Signals.set_sigpipe () ;
  Signals.set_sigterm () ;
  Signals.set_sigquit () ;

  (* Starting global timer. *)
  Stat.start_timer Stat.total_time ;

  (* 读取输入的文件，根据输入的文件类型创建一个input_file 
     input_file在前面定义过，暂时不知道具体用法
   *)
  
  let in_file = Flags.input_file () in

  KEvent.log L_info "Creating Input system from  %s." (classify_input_stream in_file);

  try
    let input_system = 
      match Flags.input_format () with
      | `Lustre -> (
        KEvent.log L_debug "Lustre input detected";
        match InputSystem.read_input_lustre (Flags.only_parse ()) in_file with
        | Some in_sys -> Input in_sys
        | None -> (
            KEvent.log L_note "No parse errors found!";
            KEvent.terminate_log ();
            exit ExitCodes.success
        )
      )
                   
      | `Native -> KEvent.log L_debug "Native input detected";
                   Input (InputSystem.read_input_native in_file)
                   
      | `Horn   -> KEvent.log L_fatal "Horn clauses are not supported." ;
                   KEvent.terminate_log () ;
                   exit ExitCodes.error
    in
    KEvent.log L_debug "Input System built";
    input_system
  with
  (* Could not create input system. *)
  (* 处理各种创建input system失败的函数 *)
  | LustreAst.Parser_error  ->
     (* We should have printed the appropriate message so just 'gracefully' exit *)
     KEvent.terminate_log () ; exit ExitCodes.parse_error
  | LustreInput.NoMainNode msg ->
     KEvent.log L_fatal "Error reading input file '%s': %s" in_file msg ;
     KEvent.terminate_log () ; exit ExitCodes.error
  | Sys_error msg ->
     KEvent.log L_fatal "Error opening input file '%s': %s" in_file msg ;
     KEvent.terminate_log () ; exit ExitCodes.error
  | e ->
     let backtrace = Printexc.get_raw_backtrace () in
     KEvent.log L_fatal "Error opening input file '%s':@ %s%a"
       (in_file) (Printexc.to_string e)
       (if Printexc.backtrace_status ()
        then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
        else fun _ _ -> ()) backtrace;
     (* Terminating log and exiting with error. *)
     KEvent.terminate_log () ;
     exit ExitCodes.error  

(* Entry point *)
let main () =

  (* Set everything up and produce input system. *)
  (* 对应了上面哪个setup函数，返回了一个input_sys *)
  let Input input_sys = setup () in

  (* Not launching if we're just translating contracts. *)
  (* 决定是否要翻译合约 *)
  match Flags.Contracts.translate_contracts () with
  | Some target -> (
    let src = Flags.input_file () in
    KEvent.log_uncond "Translating contracts to file '%s'" target ;
    try (
      InputSystem.translate_contracts_lustre src target ;
      KEvent.log_uncond "Success"
    ) with e ->
      KEvent.log L_error
        "Could not translate contracts from file '%s':@ %s"
        src (Printexc.to_string e)
  )
  | None ->
    try
      (* main 不翻译合约，开始执行 *)
      Kind2Flow.run input_sys
    with e -> (
      KEvent.log L_fatal "Caught unexpected exception: %s" (Printexc.to_string e) ;
      KEvent.terminate_log () ;
      exit ExitCodes.error
    )
;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
