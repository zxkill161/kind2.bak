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

(*./kind2 --enable interpreter --debug smt --debug parse microwave.lus*)
open Lib


(* Solver instance if created *)
let ref_solver = ref None


(* Exit and terminate all processes here in case we are interrupted *)
let on_exit _ = 

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         SMTSolver.delete_instance solver;  
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       KEvent.log L_error
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* Assert transition relation for all steps below [i] *)
let rec assert_trans solver t i =
  
  (* Instant zero is base instant *)
  if Numeral.(i < one) then () else  
    
    (

      (* Assert transition relation from [i-1] to [i] *)
      SMTSolver.assert_term solver
        (TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) t i);
                            
      (* Continue with for [i-2] and [i-1] *)
      assert_trans solver t Numeral.(i - one)

    )
    

(* Main entry point *)
let main input_file input_sys _ trans_sys =

  KEvent.set_module `Interpreter;

  let input_scope = TransSys.scope_of_trans_sys trans_sys @
                    LustreIdent.user_scope in

  let trans_svars = TransSys.state_vars trans_sys in
  (*trans_svars |> List.iter (fun sv -> KEvent.log_uncond "%a" StateVar.pp_print_state_var sv) ;*)

  (* Read inputs from file *)
  (* 从文件读入，main函数是InputParser.read_file *)
  let inputs =
    if input_file = "" then []
    else
      try InputParser.read_file input_scope input_file
      with Sys_error e -> 
        (* Output warning *)
        KEvent.log L_warn "@[<v>Error reading interpreter input file.@,%s@]" e;
        raise (Failure "main")
  in

  (* 代码使用 List.filter 和 StateVar.is_input 来过滤出输入状态变量，并计算其数量，并将其赋值给变量 nb_inputs *)
  let nb_inputs = List.filter StateVar.is_input trans_svars |> List.length in

  (* 代码对输入进行检查，确保常量输入确实是常量。代码遍历每个输入，对于每个常量输入状态变量，检查其输入值列表是否都相等。如果发现输入值不相等，则记录一个警告日志消息，并抛出一个 Failure 异常。 *)
  (* Check that constant inputs are indeed constant. *)
  inputs |> List.iter (
    function
    | ((sv, _), head :: tail) when StateVar.is_const sv ->
      tail |> List.fold_left (
        fun acc value ->
          if acc != value then (
            KEvent.log L_warn
              "Input %s is constant, but input values differ: \
              got %a and, later, %a."
              (StateVar.name_of_state_var sv)
              Term.pp_print_term acc
              Term.pp_print_term value ;
            Failure "main" |> raise
          ) ;
          acc
      ) head |> ignore
    | _ -> ()
  ) ;

  (* Remove sliced inputs *)
  (* 代码使用 List.filter 和 List.exists 来过滤出与转换系统中的状态变量匹配的输入，并将结果赋值给变量 inputs *)
  let inputs = List.filter (fun ((sv,_), _) ->
      List.exists (StateVar.equal_state_vars sv) trans_svars
    ) inputs
  in

  (* Minimum number of steps in input *)
  (* 代码使用 List.fold_left 和 List.length 来计算输入的最小步数，并将其赋值给变量 input_length
    计算输入的最小步数是指确定输入数据中最短的列表的长度。在这段代码中，输入数据是由 `inputs` 列表表示的。每个输入是一个二元组，其中第一个元素是输入状态变量，第二个元素是一个输入值的列表。因此，`inputs` 列表的结构大致如下：

    ```
    inputs = [ ((sv1, _), [val11; val12; ...]);
           ((sv2, _), [val21; val22; ...]);
           ...
         ]
    ```

    每个输入值的列表可能有不同的长度。计算输入的最小步数就是找到输入值列表中最短的长度。在代码中，使用 `List.fold_left` 和 `List.length` 循环遍历 `inputs` 列表，逐个获取输入值列表，并将其长度与累积的最小步数进行比较，取较小值作为新的最小步数。最后，最小步数将存储在变量 `input_length` 中。

    这个最小步数的计算对于确定输入数据的有效性和一致性非常重要。在模型验证等领域中，输入数据的长度通常会影响到系统行为的分析和验证的范围。因此，计算输入的最小步数可以帮助确保输入数据的一致性和正确性。 *)
  let input_length = 
    List.fold_left 
      (fun accum (_, inputs) -> 
         min (if accum = 0 then max_int else accum) (List.length inputs))
      0
      inputs
  in

  (* Check if all inputs are of the same length *)
  List.iter
    (fun ((state_var, _), inputs) -> 

       (* Is input longer than minimum? *)
       if List.length inputs > input_length then

         (* Output warning *)
         KEvent.log L_warn 
           "Input for %s is longer than other inputs"
           (StateVar.name_of_state_var state_var))

    inputs;

  (* Number of steps to simulate *)
  (* 代码根据用户定义的模拟步数来确定要模拟的步数 steps。通过调用 Flags.Interpreter.steps 函数获取用户定义的模拟步数。
     如果用户没有指定步数或步数小于等于0，则将 steps 设置为 input_length，即最小输入列表的长度。
     否则，如果用户指定的步数大于 input_length 并且存在输入变量，则记录一个警告日志消息，指示输入不足以模拟指定的步数，并将 steps 设置为用户指定的步数。 *)
  let steps = 

    match Flags.Interpreter.steps () with 

    (* Simulate length of smallest input if number of steps not given *)
    | s when s <= 0 -> input_length

    (* Length of simulation given by user *)
    | s -> 

      (* Lenghth of simulation greater than input? *)
      if s > input_length && nb_inputs > 0 then

        KEvent.log L_warn 
          "Input is not long enough to simulate %d steps. \
           Simulation is nondeterministic." 
          input_length;

      (* Simulate for given length *)
      s

  in

  KEvent.log L_info "Interpreter running up to k=%d" steps;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in

  (* Create solver instance *)

  (* 首先创建了一个 SMT 求解器实例 solver。
     通过调用 Flags.Smt.solver 函数获取用户定义的 SMT 求解器类型，并使用 SMTSolver.create_instance 函数创建实例。
     produce_models:true 参数表示该求解器实例将生成模型。 *)
  let solver = 
    Flags.Smt.solver ()
    |> SMTSolver.create_instance ~produce_models:true logic
  in

  (* Create a reference for the solver. Only used in on_exit. *)
  ref_solver := Some solver;

  (* Defining uf's and declaring variables. *)
  (* 用于定义和声明转换系统的未解析函数和变量，并使用给定的边界条件。 *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.(~- one) Numeral.(of_int steps) ;

  (* Assert initial state constraint *)
(* 代码通过调用 SMTSolver.assert_term 函数添加了初始状态约束。
   使用 TransSys.init_of_bound 函数生成约束，并使用 SMTSolver.declare_fun 函数声明变量。这个约束表示系统的初始状态必须满足转换系统的边界条件。 *)
    SMTSolver.assert_term solver
      (TransSys.init_of_bound (Some (SMTSolver.declare_fun solver))
         trans_sys Numeral.zero);

  (* Assert transition relation up to number of steps *)
  assert_trans solver trans_sys (Numeral.of_int steps);

  (* Assert equation of state variable and its value at each
     instant *)
  (* 建模系统状态变化：通过将状态变量和其在每个时间步骤上的值添加到约束中，这段代码帮助建模系统的状态变化。约束将系统的状态限制为特定的值和时间步骤，从而定义了系统在模拟和验证过程中的行为。

  约束求解器的可满足性：将约束添加到求解器中后，可以使用求解器来检查约束的可满足性。如果约束是不可满足的，则意味着系统的状态和值之间存在冲突，即系统的行为是不一致的。这对于验证模型的正确性和一致性是很有用的。

  支持模拟和验证过程：通过将状态变量和值添加到约束中，这段代码为后续的模拟和验证过程提供了基础。在模拟过程中，可以使用约束来生成系统的执行路径，以验证系统的行为是否满足预期。在验证过程中，约束可以用于检查系统的性质和约束条件是否被满足。 *)
  List.iter

    (fun ((state_var, indexes), values) ->

       List.iteri 
         (fun instant instant_value ->

            (* Only assert up to the maximum number of steps *)
            if instant < steps then
            (
              (* Create variable at instant *)
              let var = 
                Var.mk_state_var_instance 
                  state_var 
                  (Numeral.of_int instant)
                |> Term.mk_var
              in

              (* Select index of instance variable *)
              let var = List.fold_left (
                fun acc i ->
                Term.mk_select acc (Term.mk_num_of_int i)
              ) var indexes |> Term.convert_select in

              (* Constrain variable to its value at instant *)
              let equation = 
                Term.mk_eq [var; instant_value] 
              in

              (* Assert equation *)
              SMTSolver.assert_term solver equation
            )
          )
         values)

    inputs;

  KEvent.log L_info 
    "Parsing interpreter input file %s"
    (Flags.input_file ()); 

  (* Run the system *)
  (* main 使用 SMTSolver.check_sat 函数检查求解器 solver 是否具有可满足的模型。如果有可满足的模型，继续执行下一步；如果没有可满足的模型，则跳过执行路径提取和输出的步骤。 *)
  if (SMTSolver.check_sat solver) then

    (

      (* Extract execution path from model *)
      (* 使用 Model.path_from_model 函数从模型中提取执行路径。该函数接受以下参数：

      TransSys.state_vars trans_sys：转换系统的状态变量列表。
      SMTSolver.get_var_values solver：求解器中的变量值。
      Numeral.(pred (of_int steps))：模拟的步数。
      它返回一个路径，表示系统的执行轨迹。 *)
      let path = 
        Model.path_from_model 
          (TransSys.state_vars trans_sys)
            (* (SMTSolver.get_model solver) *)
            (SMTSolver.get_var_values solver
               (TransSys.get_state_var_bounds trans_sys)
               (TransSys.vars_of_bounds trans_sys
                  Numeral.zero (Numeral.of_int steps)))
          Numeral.(pred (of_int steps))
      in

      (* Output execution path *)
      KEvent.execution_path
        input_sys
        trans_sys 
        (Model.path_to_list path)

    )

  else

    (* Transition relation must be satisfiable *)
    KEvent.log L_error "Transition relation not satisfiable"


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
